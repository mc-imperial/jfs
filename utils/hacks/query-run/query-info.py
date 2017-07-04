#!/usr/bin/env python
# vim: set sw=4 ts=4 softtabstop=4 expandtab:
import argparse
import logging
import os
import pprint
import re
import sys
import yaml

_logger = None

if hasattr(yaml, 'CLoader'):
    # Use libyaml which is faster
    _loader = yaml.CLoader
else:
    _loader = yaml.Loader

def main(args):
    global _logger
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
    parser.add_argument("--analyse",
        choices=['all','sat','unsat','unknown'],
        default='all',
        help='Select group of queries for analysis',
    )
    parser.add_argument("--num-results",
        dest="num_results",
        default=10,
        help="Number of results to display as slowest and fastest"
    )
    parser.add_argument("--plot",
        default=False,
        action='store_true'
    )
    parser.add_argument("--check-fp-to-ieeebv",
        dest="check_fp_to_ieeebv",
        default=False,
        action='store_true'
    )
    parser.add_argument("--count-array-free",
        dest="count_array_free",
        default=False,
        action='store_true',
        help='Count number of benchmarks that do not use arrays',
    )
    parser.add_argument("--plot-bins",
        type=int,
        dest='plot_number_of_bins',
        default=100,
        help='Number of bins for histogram plot'
    )
    parser.add_argument("--queries-root-dir",
        dest="queries_root_dir",
        default=os.path.join(os.getcwd(), "queries"),
    )
    parser.add_argument("queries_yaml_file",
        type=argparse.FileType('r')
    )
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
    _logger = logging.getLogger(__name__)

    # Open queries
    _logger.info('Loading "{}"'.format(pargs.queries_yaml_file.name))
    queries_data = yaml.load(pargs.queries_yaml_file, Loader=_loader)
    _logger.info('Finished loading')

    run_info = queries_data['run_info']
    assert isinstance(run_info, dict)

    # Collect sat/unsat/unknown runs
    sat_runs = { k:v for (k, v) in run_info.items() if v['sat'] is True }
    unsat_runs = { k:v for (k, v) in run_info.items() if v['sat'] is False }
    unknown_runs = { k:v for (k, v) in run_info.items() if v['sat'] is None }
    print("# of queries: {}".format(len(run_info.keys())))
    print("# of sat queries: {}".format(len(sat_runs)))
    print("# of unsat queries: {}".format(len(unsat_runs)))
    print("# of unknown queries: {}".format(len(unknown_runs)))

    if pargs.check_fp_to_ieeebv:
        uses_fp_to_ieeebv = set()
        for query_name, data in unknown_runs.items():
            query_path = os.path.join(pargs.queries_root_dir, query_name)
            if not os.path.exists(query_path):
                _logger.error('Could not find query "{}"'.format(query_path))
                return 1
            with open(query_path, 'r') as f:
                for line in f:
                    if line.find('(fp.to_ieee_bv') != -1:
                        uses_fp_to_ieeebv.add(query_name)
                        break
        print("# of unknown queries that use fp.to_ieee_bv: {}".format(len(uses_fp_to_ieeebv)))
        # Compute queries that where unknown that don't use this function
        queries_result_unknown_not_use_fp_to_ieee_bv = set(unknown_runs.keys()).difference(uses_fp_to_ieeebv)
        print("# of unknown queries that does not use fp.to_ieee_bv: {}".format(len(queries_result_unknown_not_use_fp_to_ieee_bv)))
        for q in queries_result_unknown_not_use_fp_to_ieee_bv:
            print("  {}:\n{}".format(q, pprint.pformat(run_info[q])))
        print("#"*80)


    # Pick subset to analyse
    runs_to_analyse = None
    if pargs.analyse == 'all':
        runs_to_analyse = run_info
    elif pargs.analyse == 'sat':
        runs_to_analyse = sat_runs
    elif pargs.analyse == 'unsat':
        runs_to_analyse = unsat_runs
    elif pargs.analyse == 'unknown':
        runs_to_analyse = unknown_runs
    else:
        raise Exception('Unhandled group to analyse: {}'.format(pargs.analyse))

    if pargs.count_array_free:
        _logger.info('Counting benchmarks using/not using arrays')
        # Match (declare-fun a1 () (Array (_ BitVec 32) (_ BitVec 8)))
        RE_ARRAY_DECL = re.compile(r'^\s*\(\s*declare-fun\s.+\(Array')
        RE_DECLS_END = re.compile(r'^\s*\(\s*assert')
        RE_DECL = re.compile(r'^\s*\(\s*declare-fun')
        no_array_use = set()
        array_use = set()
        no_decls = set()
        for query_name, data in runs_to_analyse.items():
            query_path = os.path.join(pargs.queries_root_dir, query_name)
            if not os.path.exists(query_path):
                _logger.error('Could not find query "{}"'.format(query_path))
                return 1
            decls_found = False
            with open(query_path, 'r') as f:
                _logger.debug('Loaded "{}"'.format(f.name))
                handled = False
                for line in f:
                    if not decls_found and RE_DECL.match(line):
                        # Contains at least one decl
                        decls_found = True
                    if RE_ARRAY_DECL.match(line):
                        # Uses array
                        array_use.add(query_name)
                        handled = True
                        break
                    if RE_DECLS_END.match(line):
                        # If we've got this far we can't have seen any array declarations
                        no_array_use.add(query_name)
                        handled = True
                        break
                if not handled:
                    # Not handling should only happen if the benchmark contains no decls
                    assert not decls_found
                    no_array_use.add(query_name)
                if not decls_found:
                    no_decls.add(query_name)

        print("# of benchmarks not using arrays: {}".format(len(no_array_use)))
        print("# of benchmarks using arrays: {}".format(len(array_use)))
        print("# of benchmarks without decls: {}".format(len(no_decls)))
        no_array_use_but_has_delcs = no_array_use.difference(no_decls)
        print("# of benchmarks not using arrays (but has decls): {}".format(len(no_array_use_but_has_delcs)))

    # Collect the fastest and slowest
    runs_ordered_by_run_time = sorted(runs_to_analyse.items(), key=lambda t: t[1]['wallclock_time'])
    runs_ordered_by_run_time_slowest_first = runs_ordered_by_run_time.copy()
    runs_ordered_by_run_time_slowest_first.reverse()

    print("#"*80)
    max_time = runs_ordered_by_run_time_slowest_first[0][1]['wallclock_time']
    print("{} slowest queries:".format(pargs.num_results))
    for index in range(0, pargs.num_results):
        key, value = runs_ordered_by_run_time_slowest_first[index]
        print("{}:\n{}".format(key, pprint.pformat(value)))
    print("#"*80)
    print("{} fastest queries:".format(pargs.num_results))
    for index in range(0, pargs.num_results):
        key, value = runs_ordered_by_run_time[index]
        print("{}:\n{}".format(key, pprint.pformat(value)))
    print("#"*80)

    # Optional plotting
    if pargs.plot:
        plot_histogram(runs_to_analyse, pargs.plot_number_of_bins)
    return 0

def plot_histogram(runs, nbins):
    import matplotlib.pyplot as plt
    execution_times = [ r['wallclock_time'] for r in runs.values() ]
    min_exec = min(execution_times)
    max_exec = max(execution_times)
    bin_width = max_exec / nbins
    _logger.info('Bin width: {}'.format(bin_width))
    n, bins, patches = plt.hist(
        execution_times,
        bins=nbins,
        range=(0, max_exec),
    )
    _logger.info('n: {}'.format(n))
    _logger.info('bins: {}'.format(bins))
    
    plt.grid(True)
    plt.xlabel('Execution Time (s)')
    plt.ylabel('Count')
    plt.show()

if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))

