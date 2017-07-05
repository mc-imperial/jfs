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

###############################################################################
# Filters
###############################################################################

def filter_only_sat_type(run_info, satisfiable):
    _logger.info('Keeping only results that has sat: {}'.format(satisfiable))
    original_count = len(run_info.keys())
    assert satisfiable is None or isinstance(satisfiable, bool)
    sat_runs = { k:v for (k, v) in run_info.items() if v['sat'] is satisfiable }
    assert isinstance(sat_runs, dict)
    _logger.info('Removed {} queries'.format(original_count - len(sat_runs.keys())))
    return sat_runs

def _filter_n_speed(run_info, n, slowest):
    assert isinstance(run_info, dict)
    assert isinstance(n, int)
    assert isinstance(slowest, bool)
    runs_ordered_by_run_time = sorted(runs_info.items(), key=lambda t: t[1]['wallclock_time'])
    if slowest:
        runs_ordered_by_run_time_slowest_first = runs_ordered_by_run_time.reverse()
    if n < len(runs_ordered_by_run_time_slowest_first):
        runs_ordered_by_run_time_slowest_first = runs_ordered_by_run_time[:n]
    # Make into dictionary again
    d = dict(runs_ordered_by_run_time_slowest_first)
    assert isinstance(d, dict)
    return d

def filter_gt_exec_time(run_info, min_time):
    _logger.info('Keeping only results that had exec time >= {}'.format(min_time))
    assert isinstance(run_info, dict)
    assert isinstance(min_time, float)
    original_count = len(run_info.keys())
    d = dict()
    for query_name, data in run_info.items():
        exec_time = data['wallclock_time']
        if exec_time >= min_time:
            d[query_name] = data
    _logger.info('Removed {} queries'.format(original_count - len(d.keys())))
    return d

def filter_lt_exec_time(run_info, max_time):
    _logger.info('Keeping only results that had exec time < {}'.format(max_time))
    assert isinstance(run_info, dict)
    assert isinstance(max_time, float)
    original_count = len(run_info.keys())
    d = dict()
    for query_name, data in run_info.items():
        exec_time = data['wallclock_time']
        if exec_time < max_time:
            d[query_name] = data
    _logger.info('Removed {} queries'.format(original_count - len(d.keys())))
    return d

def filter_n_slowest(run_info, n):
    _logger.info('Keeping only {} slowest queries: {}'.format(n))
    original_count = len(run_info.keys())
    r = _filter_n_speed(run_info, n, slowest=True)
    _logger.info('Removed {} queries'.format(original_count - len(r.keys())))
    return r

def filter_n_fastest(run_info, n):
    _logger.info('Keeping only {} fastest queries: {}'.format(n))
    original_count = len(run_info.keys())
    r = _filter_n_speed(run_info, n, slowest=False)
    _logger.info('Removed {} queries'.format(original_count - len(r.keys())))
    return r

def filter_has_array_decls(run_info, queries_root_dir):
    _logger.info('Keeping only queries that have array decls')
    original_count = len(run_info.keys())
    assert isinstance(run_info, dict)
    # Match (declare-fun a1 () (Array (_ BitVec 32) (_ BitVec 8)))
    RE_ARRAY_DECL = re.compile(r'^\s*\(\s*declare-fun\s.+\(Array')
    RE_DECLS_END = re.compile(r'^\s*\(\s*assert')
    RE_DECL = re.compile(r'^\s*\(\s*declare-fun')
    array_use = dict()
    for query_name, data in run_info.items():
        query_path = os.path.join(queries_root_dir, query_name)
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
                    array_use[query_name] = data
                    handled = True
                    break
                if RE_DECLS_END.match(line):
                    # Try to early exit from scanning lines
                    handled = True
                    break
            if not handled:
                # Not handling should only happen if the benchmark contains no decls
                assert not decls_found
    assert isinstance(array_use, dict)
    _logger.info('Removed {} queries'.format(original_count - len(array_use.keys())))
    return array_use

def filter_has_no_array_decls(run_info, queries_root_dir):
    _logger.info('Keeping only queries that do not have array decls')
    original_count = len(run_info.keys())
    assert isinstance(run_info, dict)
    # Match (declare-fun a1 () (Array (_ BitVec 32) (_ BitVec 8)))
    RE_ARRAY_DECL = re.compile(r'^\s*\(\s*declare-fun\s.+\(Array')
    RE_DECLS_END = re.compile(r'^\s*\(\s*assert')
    RE_DECL = re.compile(r'^\s*\(\s*declare-fun')
    not_array_use = dict()
    for query_name, data in run_info.items():
        query_path = os.path.join(queries_root_dir, query_name)
        if not os.path.exists(query_path):
            _logger.error('Could not find query "{}"'.format(query_path))
            return 1
        with open(query_path, 'r') as f:
            _logger.debug('Loaded "{}"'.format(f.name))
            found_array_decl = False
            for line in f:
                if RE_ARRAY_DECL.match(line):
                    # Uses array
                    found_array_decl = True
                    break
                if RE_DECLS_END.match(line):
                    # Try to early exit from scanning lines
                    break
            if not found_array_decl:
                not_array_use[query_name] = data
    assert isinstance(not_array_use, dict)
    _logger.info('Removed {} queries'.format(original_count - len(not_array_use.keys())))
    return not_array_use

def filter_decls(run_info, queries_root_dir):
    _logger.info('Keeping only queries that have decls')
    original_count = len(run_info.keys())
    assert isinstance(run_info, dict)
    # Match (declare-fun a1 () (Array (_ BitVec 32) (_ BitVec 8)))
    RE_DECL = re.compile(r'^\s*\(\s*declare-fun')
    RE_DECLS_END = re.compile(r'^\s*\(\s*assert')
    use_decl = dict()
    for query_name, data in run_info.items():
        query_path = os.path.join(queries_root_dir, query_name)
        if not os.path.exists(query_path):
            _logger.error('Could not find query "{}"'.format(query_path))
            return 1
        with open(query_path, 'r') as f:
            _logger.debug('Loaded "{}"'.format(f.name))
            found_decl = False
            for line in f:
                if RE_DECL.match(line):
                    # Found a decl
                    found_decl = True
                    break
                if RE_DECLS_END.match(line):
                    # Try to early exit from scanning lines
                    break
            if found_decl:
                use_decl[query_name] = data
    assert isinstance(use_decl, dict)
    _logger.info('Removed {} queries'.format(original_count - len(use_decl.keys())))
    return use_decl

def filter_no_decls(run_info, queries_root_dir):
    _logger.info('Keeping only queries that have no decls')
    original_count = len(run_info.keys())
    assert isinstance(run_info, dict)
    # Match (declare-fun a1 () (Array (_ BitVec 32) (_ BitVec 8)))
    RE_DECL = re.compile(r'^\s*\(\s*declare-fun')
    RE_DECLS_END = re.compile(r'^\s*\(\s*assert')
    no_use_decl = dict()
    for query_name, data in run_info.items():
        query_path = os.path.join(queries_root_dir, query_name)
        if not os.path.exists(query_path):
            _logger.error('Could not find query "{}"'.format(query_path))
            return 1
        with open(query_path, 'r') as f:
            _logger.debug('Loaded "{}"'.format(f.name))
            found_decl = False
            for line in f:
                if RE_DECL.match(line):
                    # Found a decl
                    found_decl = True
                    break
                if RE_DECLS_END.match(line):
                    # Try to early exit from scanning lines
                    break
            if not found_decl:
                no_use_decl[query_name] = data
    assert isinstance(no_use_decl, dict)
    _logger.info('Removed {} queries'.format(original_count - len(no_use_decl.keys())))
    return no_use_decl

def filter_uses_fp_to_ieee_bv(run_info, queries_root_dir):
    _logger.info('Keeping only queries that use fp.to_ieee_bv')
    original_count = len(run_info.keys())
    assert isinstance(run_info, dict)
    RE_USE_IEEE = re.compile(r'\(fp.to_ieee_bv')
    use_ieee_bv = dict()
    for query_name, data in run_info.items():
        query_path = os.path.join(queries_root_dir, query_name)
        if not os.path.exists(query_path):
            _logger.error('Could not find query "{}"'.format(query_path))
            return 1
        with open(query_path, 'r') as f:
            _logger.debug('Loaded "{}"'.format(f.name))
            found_decl = False
            for line in f:
                if RE_USE_IEEE.search(line):
                    use_ieee_bv[query_name] = data
                    break
    assert isinstance(use_ieee_bv, dict)
    _logger.info('Removed {} queries'.format(original_count - len(use_ieee_bv.keys())))
    return use_ieee_bv

def filter_uses_qf_fpbv(run_info, queries_root_dir):
    # FIXME: This isn't quite right. We aren't filtering out stuff like reals and quantifiers
    # FIXME: We aren't checking for bitvector operations/sorts.
    _logger.info('Keeping only queries that use QF_FPBV')
    original_count = len(run_info.keys())

    # First keep only queries that have declarations. We don't want empty queries
    temp_run_info = filter_decls(run_info, queries_root_dir)

    # Filter out queries that have arrays
    temp_run_info2 = filter_has_no_array_decls(temp_run_info, queries_root_dir)

    # Keep only queries that use the floating point theory
    temp_run_info3 = filter_uses_floating_point_theory(temp_run_info2, queries_root_dir)

    _logger.info('Removed {} queries'.format(original_count - len(temp_run_info3.keys())))
    return temp_run_info3

def filter_uses_qf_fpabv(run_info, queries_root_dir):
    # FIXME: This isn't quite right. We aren't filtering out stuff like reals and quantifiers
    # FIXME: We aren't checking for bitvector operations/sorts.
    _logger.info('Keeping only queries that use QF_FPABV')
    original_count = len(run_info.keys())

    # First keep only queries that have declarations. We don't want empty queries
    temp_run_info = filter_decls(run_info, queries_root_dir)

    # Keep queries that declare arrays
    temp_run_info2 = filter_has_array_decls(temp_run_info, queries_root_dir)

    # Keep only queries that use the floating point theory
    temp_run_info3 = filter_uses_floating_point_theory(temp_run_info2, queries_root_dir)

    _logger.info('Removed {} queries'.format(original_count - len(temp_run_info3.keys())))
    return temp_run_info3

def filter_non_zero_exit_code(run_info, queries_root_dir):
    _logger.info('Keeping only queries with non-zero exit code')
    original_count = len(run_info.keys())
    non_zero_ec = dict()
    for query_name, data in run_info.items():
        if data['exit_code'] != 0:
            non_zero_ec[query_name] = data
    _logger.info('Removed {} queries'.format(original_count - len(non_zero_ec.keys())))
    return non_zero_ec


def filter_uses_floating_point_theory(run_info, queries_root_dir):
    _logger.info('Keeping only queries that use floating point theory')
    original_count = len(run_info.keys())
    assert isinstance(run_info, dict)
    # We look for fp constants, fp declarations and conversions to fp sorts
    # as indicators that floating point is being used
    RE_FP_CONSTANTS = re.compile(
        r'(\(_ +oo \d+ \d+\))|'
        r'(\(_ -oo \d+ \d+\))|'
        r'(\(_ +zero \d+ \d+\))|'
        r'(\(_ -zero \d+ \d+\))|'
        r'(\(_ NaN \d+ \d+\))|'
        r'(\(fp #b)'
    )
    RE_FP_DECL = re.compile(r'^\s*\(\s*declare-fun\s.+\(_ FloatingPoint')
    RE_FP_CONV = re.compile(r'\(_ to_fp')
    use_fp = dict()
    for query_name, data in run_info.items():
        query_path = os.path.join(queries_root_dir, query_name)
        if not os.path.exists(query_path):
            _logger.error('Could not find query "{}"'.format(query_path))
            return 1
        with open(query_path, 'r') as f:
            #_logger.debug('Loaded "{}"'.format(f.name))
            match_found = False
            for line in f:
                if RE_FP_DECL.match(line):
                    match_found = True
                if RE_FP_CONSTANTS.search(line):
                    match_found = True
                if RE_FP_CONV.search(line):
                    match_found = True
                if match_found:
                    use_fp[query_name] = data
                    break
            if not match_found:
                _logger.debug('"{}" does not seem to use fp'.format(query_name))
    assert isinstance(use_fp, dict)
    _logger.info('Removed {} queries'.format(original_count - len(use_fp.keys())))
    return use_fp

# Entry point
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
    parser.add_argument("--filter",
        choices= [
            "sat",
            "slowest",
            "fastest",
            "has_array_decls",
            "no_array_decls",
            "has_decls",
            "no_decls",
            "min_exec_time",
            "max_exec_time",
            "uses_fp_to_ieee_bv",
            "uses_fp_theory",
            "uses_qf_fpbv",
            "uses_qf_fpabv",
            "non_zero_exit_code",
        ],
        default=[],
        action='append',
    )
    parser.add_argument("--min-exec-time",
        dest="min_exec_time",
        type=float,
        default=20.0,
        help='The minimum execution time to use for min_exec_time filter',
    )
    parser.add_argument("--max-exec-time",
        dest="max_exec_time",
        type=float,
        default=20.0,
        help='The maximum execution time to use for max_exec_time filter',
    )
    parser.add_argument("--sat",
        choices=['sat','unsat','unknown'],
        default='sat',
        help='When using sat filter keep only queries with this answer',
    )
    parser.add_argument("--num-slowest",
        dest="num_slowest",
        default=10,
        help="Number of results to keep that are slowest"
    )
    parser.add_argument("--num-fastest",
        dest="num_fastest",
        default=10,
        help="Number of results to keep that are fastest"
    )
    parser.add_argument("--queries-root-dir",
        dest="queries_root_dir",
        default=os.path.join(os.getcwd(), "queries"),
    )
    parser.add_argument("queries_yaml_file",
        type=argparse.FileType('r')
    )
    parser.add_argument("-o", "--output-yaml-file",
        dest='output_yaml_file',
        type=argparse.FileType('w'),
        default=sys.stdout,
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
    original_length = len(run_info.keys())
    _logger.info('Input has {} queries'.format(original_length))

    assert isinstance(run_info, dict)
    # Go through filters and apply them
    for filter_ty in pargs.filter:
        if filter_ty == 'sat':
            sat_type = None
            if pargs.sat == 'sat':
                sat_type = True
            elif pargs.sat == 'unsat':
                sat_type = False
            run_info = filter_only_sat_type(run_info, sat_type)
        elif filter_ty == 'slowest':
            run_info = filter_n_slowest(run_info, pargs.num_slowest)
        elif filter_ty == 'fastest':
            run_info = filter_n_fastest(run_info, pargs.num_fastest)
        elif filter_ty == 'has_array_decls':
            run_info = filter_has_array_decls(run_info, pargs.queries_root_dir)
        elif filter_ty == 'no_array_decls':
            run_info = filter_has_no_array_decls(run_info, pargs.queries_root_dir)
        elif filter_ty == 'has_decls':
            run_info = filter_decls(run_info, pargs.queries_root_dir)
        elif filter_ty == 'no_decls':
            run_info = filter_no_decls(run_info, pargs.queries_root_dir)
        elif filter_ty == 'min_exec_time':
            run_info = filter_gt_exec_time(run_info, pargs.min_exec_time)
        elif filter_ty == 'max_exec_time':
            run_info = filter_lt_exec_time(run_info, pargs.max_exec_time)
        elif filter_ty == 'uses_fp_to_ieee_bv':
            run_info = filter_uses_fp_to_ieee_bv(run_info, pargs.queries_root_dir)
        elif filter_ty == 'uses_fp_theory':
            run_info = filter_uses_floating_point_theory(run_info, pargs.queries_root_dir)
        elif filter_ty == 'uses_qf_fpbv':
            run_info = filter_uses_qf_fpbv(run_info, pargs.queries_root_dir)
        elif filter_ty == 'uses_qf_fpabv':
            run_info = filter_uses_qf_fpabv(run_info, pargs.queries_root_dir)
        elif filter_ty == 'non_zero_exit_code':
            run_info = filter_non_zero_exit_code(run_info, pargs.queries_root_dir)
        else:
            raise Exception('Unhandled filter "{}"'.format(filter_ty))
        assert isinstance(run_info, dict)

    queries_data['run_info'] = run_info
    new_length = len(run_info.keys())
    _logger.info('Final Output has {} queries'.format(new_length))
    _logger.info('{} queries removed in total'.format(original_length - new_length))

    # Write result out
    raw_text = yaml.dump(queries_data, default_flow_style=False)
    pargs.output_yaml_file.write(raw_text)
    pargs.output_yaml_file.close()
    return 0

if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))

