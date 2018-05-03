# JFS basics

This tutorial will walk you through the basics of using JFS.

JFS is designed to solve constraints in the [SMT-LIBv2.6 format](http://smtlib.cs.uiowa.edu/).
More specifically it is designed to solve constraints that
use any combination of Booleans, BitVectors, and floating-point
types.

Let's walk through running JFS on the constraints in the [0-basics-example.smt2](0-basics-example.smt2) file.

Try running the following. **NOTE the $ symbol indicates a shell
prompt and it should not be typed.**

```
$ jfs 0-basics-example.smt2
sat
```

We can see that the tool responded with `sat` meaning that JFS found
a satisfying assignment to the constraints in `0-basics-example.smt2`.

## Verbose output

How do we see what happened? We can use the `-v=1` to see more information. The `-v` sets the verbosity level.

```
$ jfs -v=1 -keep-output-dir 0-basics-example.smt2
(WorkingDirectoryManager "/home/user/dev/jfs/jfs/src/0-basics-example.smt2-2", deleteOnDestruction: 1)
pathToBinary: "/home/user/dev/jfs/jfs/builds/upgrades/gcc_rel/runtime/bin/clang++"
pathToRuntimeIncludeDir: "/home/user/dev/jfs/jfs/builds/upgrades/gcc_rel/runtime/include"
pathToLibFuzzerLib: "/home/user/dev/jfs/jfs/builds/upgrades/gcc_rel/runtime/LibFuzzer_RelWithDebInfo/Fuzzer/libLLVMFuzzer.a"
optimizationLevel: O0
debug symbols:false
useASan: false
useUBSan: false
sanitizerCoverageOptions: TRACE_PC_GUARD
(Parser starting)
(Parser finished)
(QueryPassManager starting)
(QueryPassManager "AndHoisting")
(QueryPassManager "Simplification")
(QueryPassManager "AndHoisting")
(QueryPassManager "Simplification")
(QueryPassManager "ConstantPropagation")
(QueryPassManager "AndHoisting")
(QueryPassManager "Simplification")
(QueryPassManager "ConstantPropagation")
(QueryPassManager "Simplification")
(QueryPassManager "AndHoisting")
(QueryPassManager "DuplicateConstraintElimination")
(QueryPassManager "TrueConstraintElimination")
(QueryPassManager "SimpleContradictionsToFalse")
(QueryPassManager "DuplicateConstraintElimination")
(QueryPassManager finished)
(using solver "CXXFuzzingSolver")
(QueryPassManager starting)
(QueryPassManager "EqualityExtractionPass")
(QueryPassManager "FreeVariableToBufferAssignmentPass")
(QueryPassManager finished)
(QueryPassManager starting)
(QueryPassManager "SortConformanceCheckPass")
(QueryPassManager finished)
(QueryPassManager starting)
(QueryPassManager "CXXProgramBuilder")
(QueryPassManager finished)
(ClangInvocationManager
 ["/home/user/dev/jfs/jfs/builds/upgrades/gcc_rel/runtime/bin/clang++", "-std=c++11", "-I", "/home/user/dev/jfs/jfs/builds/upgrades/gcc_rel/runtime/include", "-O0", "-fno-omit-frame-pointer", "-fsanitize-coverage=trace-pc-guard", "/home/user/dev/jfs/jfs/src/0-basics-example.smt2-2/program.cpp", "/home/user/dev/jfs/jfs/builds/upgrades/gcc_rel/runtime/SMTLIB/SMTLIB__DebugSymbols_Optimized_TracePCGuard/libJFSSMTLIBRuntime.a", "/home/user/dev/jfs/jfs/builds/upgrades/gcc_rel/runtime/LibFuzzer_RelWithDebInfo/Fuzzer/libLLVMFuzzer.a", "-o", "/home/user/dev/jfs/jfs/src/0-basics-example.smt2-2/fuzzer", ]
)
(SeedManager effectiveBound:18446744073709551615)
(SeedManager creating seed "/home/user/dev/jfs/jfs/src/0-basics-example.smt2-2/corpus/zeros_0")
(SeedManager creating seed "/home/user/dev/jfs/jfs/src/0-basics-example.smt2-2/corpus/ones_0")
(SeedManager active generators exhausted)
(SeedManager wrote 2 seeds (16 bytes each))
(LibFuzzerInvocationManager
["/home/user/dev/jfs/jfs/src/0-basics-example.smt2-2/fuzzer", "-runs=-1", "-seed=1", "-mutate_depth=5", "-cross_over=1", "-max_len=16", "-use_cmp=0", "-print_final_stats=1", "-reduce_inputs=0", "-default_mutators_resize_input=0", "-handle_abrt=1", "-handle_bus=0", "-handle_fpe=0", "-handle_ill=0", "-handle_int=1", "-handle_segv=0", "-handle_term=1", "-handle_xfsz=1", "-artifact_prefix=/home/user/dev/jfs/jfs/src/0-basics-example.smt2-2/artifacts/", "-error_exitcode=77", "-timeout_exitcode=88", "/home/user/dev/jfs/jfs/src/0-basics-example.smt2-2/corpus", ]
)
INFO: Seed: 1
INFO: HACK: Mutators that resize input DISABLED!
INFO: Loaded 1 modules   (443 guards): 443 [0x677fd0, 0x6786bc),
INFO:        2 files found in /home/user/dev/jfs/jfs/src/0-basics-example.smt2-2/corpus
JFS WARNING: Wrong sized input tried.
INFO: seed corpus: files: 2 min: 16b max: 16b total: 32b rss: 33Mb
#3      INITED cov: 23 ft: 23 corp: 2/32b exec/s: 0 rss: 33Mb
#6      NEW    cov: 24 ft: 26 corp: 3/48b exec/s: 0 rss: 33Mb L: 16/16 MS: 3 CopyPart-CopyPart-ChangeBinInt-
#9      NEW    cov: 25 ft: 27 corp: 4/64b exec/s: 0 rss: 33Mb L: 16/16 MS: 3 CrossOver-CopyPart-CrossOver-
==24758== ERROR: libFuzzer: deadly signal
    #0 0x42bcd3 in __sanitizer_print_stack_trace /home/user/dev/jfs/llvm6/src/projects/compiler-rt/lib/ubsan/ubsan_diag_standalone.cc:29
    #1 0x43e811 in fuzzer::Fuzzer::CrashCallback() /home/user/dev/jfs/jfs/src/runtime/LibFuzzer/Fuzzer/FuzzerLoop.cpp:233:5
    #2 0x43e7df in fuzzer::Fuzzer::StaticCrashSignalCallback() /home/user/dev/jfs/jfs/src/runtime/LibFuzzer/Fuzzer/FuzzerLoop.cpp:206:6
    #3 0x151b23c44b8f  (/usr/lib/libpthread.so.0+0x11b8f)
    #4 0x151b23289efa in __GI_raise (/usr/lib/libc.so.6+0x34efa)
    #5 0x151b2328b2c0 in __GI_abort (/usr/lib/libc.so.6+0x362c0)
    #6 0x42e4a5 in LLVMFuzzerTestOneInput (/home/user/dev/jfs/jfs/src/0-basics-example.smt2-2/fuzzer+0x42e4a5)
    #7 0x43fa13 in fuzzer::Fuzzer::ExecuteCallback(unsigned char const*, unsigned long) /home/user/dev/jfs/jfs/src/runtime/LibFuzzer/Fuzzer/FuzzerLoop.cpp:524:13
    #8 0x43f2ab in fuzzer::Fuzzer::RunOne(unsigned char const*, unsigned long, bool, fuzzer::InputInfo*, bool*) /home/user/dev/jfs/jfs/src/runtime/LibFuzzer/Fuzzer/FuzzerLoop.cpp:449:3
    #9 0x44043d in fuzzer::Fuzzer::MutateAndTestOne() /home/user/dev/jfs/jfs/src/runtime/LibFuzzer/Fuzzer/FuzzerLoop.cpp:657:19
    #10 0x440c75 in fuzzer::Fuzzer::Loop(std::vector<std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char> >, fuzzer::fuzzer_allocator<std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char> > > > const&) /home/user/dev/jfs/jfs/src/runtime/LibFuzzer/Fuzzer/FuzzerLoop.cpp:784:5
    #11 0x437a6b in fuzzer::FuzzerDriver(int*, char***, int (*)(unsigned char const*, unsigned long)) /home/user/dev/jfs/jfs/src/runtime/LibFuzzer/Fuzzer/FuzzerDriver.cpp:755:6
    #12 0x4331a0 in main /home/user/dev/jfs/jfs/src/runtime/LibFuzzer/Fuzzer/FuzzerMain.cpp:20:10
    #13 0x151b232769a6 in __libc_start_main (/usr/lib/libc.so.6+0x219a6)
    #14 0x406af9 in _start (/home/user/dev/jfs/jfs/src/0-basics-example.smt2-2/fuzzer+0x406af9)

NOTE: libFuzzer has rudimentary signal handlers.
      Combine libFuzzer with AddressSanitizer or similar for better crash reports.
SUMMARY: libFuzzer: deadly signal
MS: 1 CopyPart-; base unit: 1519e74668a11df04e90de531274a5929990d1fa
0x0,0xff,0xff,0xff,0xff,0xff,0xff,0x0,0x0,0x0,0x0,0x0,0xff,0xff,0xff,0x0,
\x00\xff\xff\xff\xff\xff\xff\x00\x00\x00\x00\x00\xff\xff\xff\x00
artifact_prefix='/home/user/dev/jfs/jfs/src/0-basics-example.smt2-2/artifacts/'; Test unit written to /home/user/dev/jfs/jfs/src/0-basics-example.smt2-2/artifacts/crash-26f92ccb5076c2b6534271d13d4ac70dc5c26f2f
Base64: AP///////wAAAAAA////AA==
stat::number_of_executed_units: 25
stat::average_exec_per_sec:     0
stat::new_units_added:          2
stat::slowest_unit_time_sec:    0
stat::peak_rss_mb:              38
sat
```

The verbose output shows a lot of internal implementation details of JFS.
We'll now highlight some of the important information.

The line below informs us where JFS's temporary working directory will be
located (note this can be set by using the `-output-dir` option).
Note that `deleteOnDestruction` is set to 1 which means the temporary working
directory will be deleted when JFS exits. To prevent this use the `-keep-output-dir` command line option.

```
(WorkingDirectoryManager "/home/user/dev/jfs/jfs/src/0-basics-example.smt2-2", deleteOnDestruction: 1)
```

The following lines indicate that the SMT-LIB parser is running.

```
(Parser starting)
(Parser finished)
```

After parsing the next step is to run a set of simplification passes
on the constraints. We can see this in the `(QueryPassManager ...)` lines.

After this we see the line `(using solver "CXXFuzzingSolver")`. This informs
us that the CXXFuzzingSolver back-end is being used. Note this can be changed
on the command line. See `--help`, e.g. `-z3` causes Z3 to be used to solve the simplified constraints.

After this we see the `QueryPassManager` running again. This is running
some passes that are specific to the CXXFuzzingSolver backend. Notice that
a pass named `CXXProgramBuilder` is executed. This pass reads the constraints
and constructs a C++ program that encodes the constraints as a path
reachability problem.

After this we see the following.

```
(ClangInvocationManager
 ["/home/user/dev/jfs/jfs/builds/upgrades/gcc_rel/runtime/bin/clang++", "-std=c++11", "-I", "/home/user/dev/jfs/jfs/builds/upgrades/gcc_rel/runtime/include", "-O0", "-fno-omit-frame-pointer", "-fsanitize-coverage=trace-pc-guard", "/home/user/dev/jfs/jfs/src/0-basics-example.smt2-2/program.cpp", "/home/user/dev/jfs/jfs/builds/upgrades/gcc_rel/runtime/SMTLIB/SMTLIB__DebugSymbols_Optimized_TracePCGuard/libJFSSMTLIBRuntime.a",
 "/home/user/dev/jfs/jfs/builds/upgrades/gcc_rel/runtime/LibFuzzer_RelWithDebInfo/Fuzzer/libLLVMFuzzer.a", "-o", "/home/user/dev/jfs/jfs/src/0-basics-example.smt2-2/fuzzer", ]
)
```

This shows us how the Clang compiler is invoked to take the generated C++ programs and generate native code that is linked with [LibFuzzer](https://llvm.org/docs/LibFuzzer.html).

After this we then see the following.

```
(SeedManager effectiveBound:18446744073709551615)
(SeedManager creating seed "/home/user/dev/jfs/jfs/src/0-basics-example.smt2-2/corpus/zeros_0")
(SeedManager creating seed "/home/user/dev/jfs/jfs/src/0-basics-example.smt2-2/corpus/ones_0")
(SeedManager active generators exhausted)
(SeedManager wrote 2 seeds (16 bytes each))
```

This is informing us that JFS has created two seeds to fuzz the generated
programs and that each seed is 16 bytes.

After this we see then the following.

```
(LibFuzzerInvocationManager
["/home/user/dev/jfs/jfs/src/0-basics-example.smt2-2/fuzzer", "-runs=-1", "-seed=1", "-mutate_depth=5", "-cross_over=1", "-max_len=16", "-use_cmp=0", "-print_final_stats=1", "-reduce_inputs=0", "-default_mutators_resize_input=0", "-handle_abrt=1", "-handle_bus=0", "-handle_fpe=0", "-handle_ill=0", "-handle_int=1", "-handle_segv=0", "-handle_term=1", "-handle_xfsz=1", "-artifact_prefix=/home/user/dev/jfs/jfs/src/0-basics-example.smt2-2/artifacts/", "-error_exitcode=77", "-timeout_exitcode=88", "/home/user/dev/jfs/jfs/src/0-basics-example.smt2-2/corpus", ]
)
```

This shows us how the generated binary is invoked to run LibFuzzer.

The output that follows this is [LibFuzzer's output](https://llvm.org/docs/LibFuzzer.html#output). Here we can see that
LibFuzzer catches a deadly signal.

```
==24758== ERROR: libFuzzer: deadly signal
```

Due to the way the generated program is constructed, this indicates that
a satisfying assignment to constraints has been found.

## Working directory

We can run the example again but this time keeping the working directory and
giving it a fixed name.

```
$ jfs -keep-output-dir -output-dir=wd 0-basics-example.smt2
sat
$ cd wd
$ ls
artifacts  clang.stderr.txt  clang.stdout.txt  corpus  fuzzer  libfuzzer.stderr.txt  libfuzzer.stdout.txt  program.cpp
```

* `artifacts/` - Contains the input that is a satisfying assignment (if any).
* `clang.stderr.txt` - Contains any standard error output from the Clang invocation.
* `clang.stdout.txt` - Contains any standard output from the Clang invocation.
* `corpus/` - Contains the fuzzing corpus (seeds + found inputs).
* `fuzzer` - Is the fuzzing binary that is executed by JFS
* `libfuzzer.stderr.txt` - Contains any standard output from running the `fuzzer` binary.
* `libfuzzer.stderr.txt` - Contains any standard error output from running the `fuzzer` binary.
* `program.cpp` - The generated C++ program that is compiled using Clang.

Note that the `*.stdout.txt` and `*.stderr.txt` files will not be created
if JFS is used in verbose mode because the output goes to JFS's standard output and standard error output respectively. This behaviour can be changed
by using the `-redirect-clang-output` and `-redirect-libfuzzer-output` options.
