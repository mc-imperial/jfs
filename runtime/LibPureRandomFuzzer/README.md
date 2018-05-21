# LibPureRandomFuzzer

A fuzzer that throws random values at the target and hopes for the best.  This
is not meant for production use, but it is instead useful as a control group for
comparison with JFS.

This fuzzer generally follows the same API as `LibFuzzer` from LLVM and intends
to be a replacement for it.  However, only a subset of the `LibFuzzer` API is
currently implemented to match what's needed for JFS.

## Functions

- [x] `LLVMFuzzerTestOneInput` (user-provided, required)
- [ ] `LLVMFuzzerInitialize` (user-provided, optional)
- [ ] `LLVMFuzzerCustomMutator` (user-provided, optional)
- [ ] `LLVMFuzzerCustomCrossOver` (user-provided, optional)
- [x] `LLVMFuzzerAtExit` (user-provided, optional)
- [ ] `LLVMFuzzerMutate` (fuzzer-provided)
- [ ] `LLVMFuzzerAnnounceOutput` (fuzzer-provided)

## Options

- [ ] `verbosity`
- [ ] `seed`
- [x] `runs`
- [x] `max_len`
- [ ] `experimental_len_control`
- [ ] `cross_over`
- [ ] `mutate_depth`
- [ ] `reduce_depth`
- [ ] `shuffle`
- [ ] `prefer_small`
- [x] `timeout`
- [x] `error_exitcode`
- [x] `timeout_exitcode`
- [ ] `max_total_time`
- [ ] `help`
- [ ] `merge`
- [ ] `merge_inner`
- [ ] `merge_control_file`
- [ ] `save_coverage_summary`
- [ ] `load_coverage_summary`
- [ ] `minimize_crash`
- [ ] `cleanse_crash`
- [ ] `minimize_crash_internal_step`
- [ ] `use_counters`
- [ ] `use_memmem`
- [ ] `use_value_profile`
- [ ] `use_cmp`
- [ ] `shrink`
- [ ] `reduce_inputs`
- [ ] `jobs`
- [ ] `workers`
- [ ] `reload`
- [ ] `report_slow_units`
- [ ] `only_ascii`
- [ ] `dict`
- [x] `artifact_prefix`
- [ ] `exact_artifact_path`
- [ ] `print_pcs`
- [ ] `print_funcs`
- [x] `print_final_stats`
- [ ] `print_corpus_stats`
- [ ] `print_coverage`
- [ ] `dump_coverage`
- [ ] `handle_segv`
- [ ] `handle_bus`
- [x] `handle_abrt`
- [ ] `handle_ill`
- [ ] `handle_fpe`
- [ ] `handle_int`
- [ ] `handle_term`
- [ ] `handle_xfsz`
- [ ] `handle_usr1`
- [ ] `handle_usr2`
- [ ] `close_fd_mask`
- [ ] `detect_leaks`
- [ ] `purge_allocator_interval`
- [ ] `trace_malloc`
- [ ] `rss_limit_mb`
- [ ] `malloc_limit_mb`
- [ ] `exit_on_src_pos`
- [ ] `exit_on_item`
- [ ] `ignore_remaining_args`
- [ ] `run_equivalence_server`
- [ ] `use_equivalence_server`
- [ ] `analyze_dict`
- [ ] `use_clang_coverage`
- [ ] `use_feature_frequency`
- [ ] `default_mutators_resize_input`

## Exit Codes

- [x] Normal: `0`
- [x] Error: `77` or `error_exitcode`
- [x] Timeout: `77` or `timeout_exitcode`
