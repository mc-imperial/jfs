#!/usr/bin/env python
# vim: set sw=4 ts=4 softtabstop=4 expandtab:
import argparse
import concurrent.futures
import datetime
import logging
import os
import pprint
import psutil
import random
import signal
import subprocess
import sys
import time
import yaml
"""
Script to run a set of queries found in directory and
record their execution time and result.
"""

_logger = logging.getLogger(__name__)

# HACK: http://stackoverflow.com/questions/26475636/measure-elapsed-time-amount-of-memory-and-cpu-used-by-the-extern-program
class ResourcePopen(subprocess.Popen):
    def _try_wait(self, wait_flags):
        """All callers to this function MUST hold self._waitpid_lock."""
        try:
            (pid, sts, res) = self._eintr_retry_call(os.wait4, self.pid, wait_flags)
        except OSError as e:
            if e.errno != errno.ECHILD:
                raise
            # This happens if SIGCLD is set to be ignored or waiting
            # for child processes has otherwise been disabled for our
            # process.  This child is dead, we can't get the status.
            pid = self.pid
            sts = 0
            self.rusage = None
        else:
            self.rusage = res
        return (pid, sts)

    def _eintr_retry_call(self, func, *args):
        while True:
            try:
                return func(*args)
            except (OSError, IOError) as e:
                if e.errno == errno.EINTR:
                    continue
                raise e
jobs = None

def handleInterrupt(signum, _):
    global jobs
    _logger.error('Received signal {}. Trying to kill jobs'.format(signum))
    if jobs != None:
        # Cancel any existing futures
        for future in jobs.keys():
            future.cancel()
        # Now kill the runners
        for runner in { j[0] for j in jobs.values()}:
            runner.kill()

def main(args):
    global jobs
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("-l", "--log-level", type=str, default="info",
                        dest="log_level",
                        choices=['debug', 'info', 'warning', 'error'])
    parser.add_argument("--log-file",
                        dest='log_file',
                        type=str,
                        default=None,
                        help="Log to specified file")
    parser.add_argument("--log-only-file",
                        dest='log_only_file',
                        action='store_true',
                        default=False,
                        help='Only log to file specified by --log-file and not the console')
    parser.add_argument(
        "-j",
        "--jobs",
        type=int,
        default="1",
        help="Number of jobs to run in parallel (Default %(default)s)")
    parser.add_argument(
        "--per-query-timeout",
        dest="per_query_timeout",
        type=float,
        help="Per query timeout in seconds",
        default=0.0,
    )
    parser.add_argument(
        "--per-query-max-memory",
        dest="per_query_max_memory",
        help="Per query max memory usage in MiB",
        type=int,
        default=0
    )
    parser.add_argument(
        "--solver-exe",
        type=str,
        dest="solver_executable",
        default="/usr/bin/z3",
    )
    parser.add_argument('--randomize-execution-order',
        dest='randomize_execution_order',
        action='store_true',
    )
    parser.add_argument("--runner",
        dest='runner',
        default='z3',
        choices=['z3', 'mathsat5', 'fake', 'jfs'],
    )
    parser.add_argument("query_dir",
        help="Directory to search for queries")
    parser.add_argument("yaml_output", help="path to write YAML output to")
    pargs = parser.parse_args(args)


    # Handle logging
    logLevel = getattr(logging, pargs.log_level.upper(), None)
    if logLevel == logging.DEBUG:
        logFormat = ('%(levelname)s:%(threadName)s: %(filename)s:%(lineno)d '
                     '%(funcName)s()  : %(message)s')
    else:
        logFormat = '%(levelname)s:%(threadName)s: %(message)s'

    if not pargs.log_only_file:
        # Add default console level with appropriate formatting and level.
        logging.basicConfig(level=logLevel, format=logFormat)
    else:
        if pargs.log_file is None:
            parser.error('--log-file-only must be used with --log-file')
        logging.getLogger().setLevel(logLevel)
    if pargs.log_file is not None:
        file_handler = logging.FileHandler(pargs.log_file)
        log_formatter = logging.Formatter(logFormat)
        file_handler.setFormatter(log_formatter)
        logging.getLogger().addHandler(file_handler)

    if pargs.jobs <= 0:
        _logger.error('jobs must be <= 0')
        return 1

    if os.path.exists(pargs.yaml_output):
        _logger.error('"{}" already exists'.format(pargs.yaml_output))
        return 1

    # Check directory
    if not os.path.isdir(pargs.query_dir):
        _logger.error('"{}" is not a directory'.format(pargs.query_dir))
        return 1

    if not os.path.exists(pargs.solver_executable):
        _logger.error('Could not find solver executable "{}"'.format(pargs.solver_executable))
        return 1

    start_time = time.monotonic()
    start_date = datetime.datetime.now()

    signal.signal(signal.SIGINT, handleInterrupt)
    signal.signal(signal.SIGTERM, handleInterrupt)

    # Collect queries
    query_dir_root = os.path.abspath(pargs.query_dir)
    query_files = set() # Relative to query_dir
    for dirpath, _, filenames in os.walk(query_dir_root):
        # Compute dir prefix
        assert dirpath.startswith(query_dir_root)
        prefix_path = dirpath[len(query_dir_root):]
        if prefix_path.startswith(os.sep):
            prefix_path = prefix_path[1:]
        for f in sorted(filenames):
            if not f.endswith('.smt2'):
                _logger.debug('Skipping "{}";'.format(f))
                continue
            query_path = os.path.join(prefix_path, f)
            _logger.info('Found "{}"'.format(query_path))
            if query_path in query_files:
                _logger.error('Found duplicate "{}"'.format(query_path))
                return 1
            query_files.add(query_path)
    _logger.info('Found {} queries'.format(len(query_files)))

    # Create Runners
    runnerClass = None
    if pargs.runner == 'z3':
        runnerClass = Z3Runner
    elif pargs.runner == 'mathsat5':
        runnerClass = MathSat5Runner
    elif pargs.runner == 'fake':
        runnerClass = FakeRunner
    elif pargs.runner == 'jfs':
        runnerClass = JFSRunner
    else:
        _logger.error('Runner {} is not available'.format(pargs.runner))
        return 1
    run_info = {}
    jobs = {}
    ordered_query_files = None
    if pargs.randomize_execution_order:
        _logger.info('Randomizing execution order')
        random.seed()
        ordered_query_files = list(sorted(query_files))
        random.shuffle(ordered_query_files)
    else:
        _logger.info('Using sorted execution order')
        ordered_query_files = sorted(query_files)
    try:
        with concurrent.futures.ThreadPoolExecutor(max_workers=pargs.jobs) as executor:
            # Submit jobs
            for query in ordered_query_files:
                query_file = os.path.join(query_dir_root, query)
                _logger.info('Submitting "{}"'.format(query))
                runner = runnerClass(
                    pargs.solver_executable,
                    query_file,
                    pargs.per_query_timeout,
                    pargs.per_query_max_memory
                )
                future = executor.submit(runner.run)
                jobs[future] = (runner, query)
            # Receive jobs
            completed_jobs_count = 0
            for future in concurrent.futures.as_completed(jobs):
                query = jobs[future][1]
                if future.done() and not future.cancelled():
                    result = future.result()
                    completed_jobs_count += 1
                    _logger.info('"{}" completed ({}/{}, {:.2f}%)'.format(
                        query,
                        completed_jobs_count,
                        len(jobs),
                        100.0*(float(completed_jobs_count)/len(jobs)))
                    )
                    run_info[query] = result
    except KeyboardInterrupt:
        _logger.error('Keyboard interrupt')
    except Exception as e:
        raise e
    finally:
        # Stop catching signals and just use default handlers
        signal.signal(signal.SIGINT, signal.SIG_DFL)
        signal.signal(signal.SIGTERM, signal.SIG_DFL)


    end_time = time.monotonic()
    end_date = datetime.datetime.now()
    run_time = end_time - start_time
    _logger.info('Start date: {}'.format(start_date.isoformat(' ')))
    _logger.info('End date: {}'.format(end_date.isoformat(' ')))
    _logger.info('Run time: {} seconds'.format(run_time))

    output_data = {
        'start_date': start_date.isoformat(' '),
        'end_date': end_date.isoformat(' '),
        'run_time': run_time,
        'run_info': run_info,
    }

    # Write results out
    with open(pargs.yaml_output, 'w') as f:
        raw_text = yaml.dump(output_data, default_flow_style=False)
        f.write(raw_text)
    return 0


class Z3Runner:
    def __init__(self, executable, query, timeout, max_memory_mib):
        assert isinstance(executable, str)
        assert isinstance(query, str)
        assert isinstance(timeout, float)
        self.executable = executable
        self.query = query
        self.timeout = timeout
        self.proc = None
        self.max_memory_mib = max_memory_mib

    def _run_info_default(self):
        run_info = {
            'exit_code': None,
            'sat': None,
            'user_time': None,
            'sys_time': None,
            'wallclock_time': None
        }
        return run_info

    def run(self):
        run_info = self._run_info_default()
        cmd_line = [
            self.executable,
            '-smt2'
        ]
        if self.timeout > 0.0:
            cmd_line.append( '-T:{}'.format(self.timeout))
        if self.max_memory_mib > 0:
            cmd_line.append('-memory:{}'.format(self.max_memory_mib))

        cmd_line.append(self.query)

        _logger.info('Running: {}'.format(cmd_line))
        start_time = time.perf_counter()
        self.proc = ResourcePopen(cmd_line, stdout=subprocess.PIPE)
        stdout, _ = self.proc.communicate()
        end_time = time.perf_counter()
        stdout = stdout.decode()
        _logger.info('Got "{}"'.format(stdout))
        run_info['exit_code'] = self.proc.returncode
        # Try to parse out result
        run_info['sat'] = self.parse_smtlib_result(stdout)
        try:
            # Seconds
            run_info['user_time'] = self.proc.rusage.ru_utime
            run_info['sys_time'] = self.proc.rusage.ru_stime
        except Exception:
            pass
        run_info['wallclock_time'] = end_time - start_time
        _logger.info('Outcome: {}:\n{}'.format(
            self.query,
            pprint.pformat(run_info)))
        return run_info

    def kill(self):
        if self.proc != None:
            self.proc.kill()

    def parse_smtlib_result(self, stdout):
        if stdout.startswith('sat'):
            return True
        elif stdout.startswith('unsat'):
            return False
        else:
            return None

class MathSat5Runner(Z3Runner):
    def run(self):
        run_info = self._run_info_default()
        cmd_line = [
            self.executable,
            '-input=smt2'
        ]
        if self.max_memory_mib > 0:
            _logger.error('Forcing memory limit not supported')
            raise Exception('Forcing memory limit not supported')

        cmd_line.append(self.query)

        _logger.info('Running: {}'.format(cmd_line))
        start_time = time.perf_counter()
        self.proc = ResourcePopen(cmd_line, stdout=subprocess.PIPE)
        stdout = None
        try:
            # Mathsat5 doesn't have a timeout option so we have to
            # enforce it outselves.
            stdout, _ = self.proc.communicate(timeout=self.timeout if self.timeout > 0 else None)
        except subprocess.TimeoutExpired as e:
            _logger.error('Timeout occurred')
            self.proc.kill()
            self.proc.wait()
        end_time = time.perf_counter()

        run_info['exit_code'] = self.proc.returncode
        if stdout:
            stdout = stdout.decode()
            _logger.info('Got "{}"'.format(stdout))
            # Try to parse out result
            run_info['sat'] = self.parse_smtlib_result(stdout)
        else:
            run_info['sat'] = None
        try:
            # Seconds
            run_info['user_time'] = self.proc.rusage.ru_utime
            run_info['sys_time'] = self.proc.rusage.ru_stime
        except Exception:
            pass
        run_info['wallclock_time'] = end_time - start_time
        _logger.info('Outcome: {}:\n{}'.format(
            self.query,
            pprint.pformat(run_info)))
        return run_info

class FakeRunner(Z3Runner):
    def run(self):
        return self._run_info_default()

class JFSRunner(Z3Runner):
    def run(self):
        run_info = self._run_info_default()
        cmd_line = [
            self.executable,
        ]
        if self.max_memory_mib > 0:
            _logger.error('Forcing memory limit not supported')
            raise Exception('Forcing memory limit not supported')

        cmd_line.append(self.query)

        _logger.info('Running: {}'.format(cmd_line))
        start_time = time.perf_counter()
        self.proc = ResourcePopen(cmd_line, stdout=subprocess.PIPE)
        stdout = None
        try:
            # JFS has a timeout option but it doesn't work yet so we have to
            # enforce it outselves.
            stdout, _ = self.proc.communicate(timeout=self.timeout if self.timeout > 0 else None)
        except subprocess.TimeoutExpired as e:
            _logger.error('Timeout occurred')
            self.proc.kill()
            self.proc.wait()
        end_time = time.perf_counter()

        run_info['exit_code'] = self.proc.returncode
        if stdout:
            stdout = stdout.decode()
            _logger.info('Got "{}"'.format(stdout))
            # Try to parse out result
            run_info['sat'] = self.parse_smtlib_result(stdout)
        else:
            run_info['sat'] = None
        try:
            # Seconds
            run_info['user_time'] = self.proc.rusage.ru_utime
            run_info['sys_time'] = self.proc.rusage.ru_stime
        except Exception:
            pass
        run_info['wallclock_time'] = end_time - start_time
        _logger.info('Outcome: {}:\n{}'.format(
            self.query,
            pprint.pformat(run_info)))
        return run_info
if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))

