# JFS

JFS (Just Fuzz it Solver) (originally JIT Fuzzing Solver) is an experimental
constraint solver designed to investigate using __coverage guided fuzzing__ as
an incomplete strategy for solving boolean, BitVector, and floating-point
constraints.

JFS supports constraints in the [SMT-LIBv2][1] constraint langauge in the
`QF_BV`, `QF_BVFP`, and `QF_FP` logics. JFS's primary purpose however is
solve floating-point constraints.

JFS is built on top of the following projects

* [LLVM](https://llvm.org/)
* [Clang](http://clang.llvm.org/)
* [Z3](https://github.com/Z3Prover/z3)
* [LibFuzzer](https://llvm.org/docs/LibFuzzer.html)

[1]: http://smtlib.cs.uiowa.edu/

## FSE 2019 paper

[A paper on JFS](https://srg.doc.ic.ac.uk/files/papers/jfs-esecfse-19.pdf) was presented and published at ESEC/FSE 2019.

Additional resources:

* [artifact](https://github.com/mc-imperial/jfs-fse-2019-artifact)
* [slides](https://docs.google.com/presentation/d/1wPxNJ3rXVqLRCm9jRMZTsL5sEW5aW9WZ583TPpb2Ffo/edit?usp=sharing)

The [Docker image](https://cloud.docker.com/u/delcypher/repository/docker/delcypher/jfs_build) with the tag `fse_2019`

## Using JFS Docker image

If you want to get started with JFS with minimal effort the easiest thing to do
is download the latest Docker image for JFS. Note this image may not be up-to-date
so you might not the latest changes.

To obtain the image run (replace `fse_2019` with the tag you wish to use).

```
docker pull delcypher/jfs_build:fse_2019
```

The simplest invocation is something like this which will show JFS's help output.

```
docker run --user 1000 --rm -t delcypher/jfs_build:fse_2019 /home/user/jfs/build/bin/jfs --help
```

To run JFS on a SMT-LIBv2 file that exists outside the container (`/path/to/simple.smt2` in this example) run this command below.

```
docker run --rm -t -v /path/to/simple.smt2:/tmp/simple.smt2 delcypher/jfs_build:fse_2019 /home/user/jfs/build/bin/jfs /tmp/simple.smt2
```

Note that the `docker run` command creates a new container and destroys it
afterwards which has notable overhead. For better performance consider running
JFS outside of a docker container or creating a single container and spawning a
shell inside it and then launch JFS from there.

## Building JFS

JFS has been tested on Linux and macOS.
Windows support would likely require a lot more work and is dependent on getting
LibFuzzer to work on Windows.

### Using Docker (the easy way)

The easiest way is just to use our Dockerfile. To do this simply run

```
scripts/Dockerfiles/build.sh
```

once the script completes you will have a Docker image on your system
named `jfs_build:ubuntu1604`. In this image you will find the JFS binaries
in the `/home/user/jfs/build/bin` directory.

## From source (the hard way)

JFS has the following build dependencies:

* LLVM/Clang/compiler-rt 6.0
* Z3 4.6.0
* CMake
* Ninja


Here are the steps to build JFS.

1. Build Z3 4.6.0. Note you must build this using Z3's CMake build system
and not its legacy build system because JFS's build system depends on files
emitted by Z3's CMake build system.

A convenience script is provided for this

```bash
export Z3_SRC_DIR=/home/user/z3/src
export Z3_BUILD_DIR=/home/user/z3/build
export Z3_BUILD_TYPE=Release
scripts/dist/build_z3.sh
```

Set the `Z3_SRC_DIR`, `Z3_BUILD_DIR` to paths to empty or non-existant
directories. The `Z3_BUILD_TYPE` can be set to `Release`, `RelWithDebInfo`,
or `Debug`.

2. Build or install LLVM, Clang, and compiler-rt 6.0


A convenience script is provided to build LLVM.

```bash
export LLVM_SRC_DIR=/home/user/llvm/src
export LLVM_BUILD_DIR=/home/user/llvm/src
export LLVM_BUILD_TYPE=Release
scripts/dist/build_llvm.sh
```

Set the `LLVM_SRC_DIR`, `LLVM_BUILD_DIR` to paths to empty or non-existant
directories. The `LLVM_BUILD_TYPE` can be set to `Release`, `RelWithDebInfo`,
or `Debug`.

3. Build JFS

A convenience script is provided to build JFS.

```bash
export JFS_SRC_DIR=/home/user/jfs/src
export JFS_BUILD_DIR=/home/user/jfs/build
export JFS_BUILD_TYPE=Release
scripts/dist/build_jfs.sh
```

`JFS_SRC_DIR` should be the absolute path to an already cloned copy of the JFS
repo. `JFS_BUILD_DIR` should be a path to an empty or non-existant directory.
The `JFS_BUILD_TYPE` can be set to `Release`, `RelWithDebInfo`, or `Debug`.

Note that `Z3_BUILD_DIR` and `LLVM_BUILD_DIR` must also be set.

4. Test JFS

```
cd ${JFS_BUILD_DIR}
ninja check
```


## FAQs

### Aren't there already a bunch of search based floating-point constraint solvers?

Yes. However as far as we're aware, JFS is the first to try to use an
"off the shelf" coverage guided fuzzer as a search strategy.

Here's a non-exhaustive list:

* [coral][2] is a constraint solver that
  supports various search strategies over floating point constraints.  It uses
  its own constraint language which is only partially overlaps with `QF_FP`
  constraints in the SMT-LIBv2 language. The [smt2coral][3] tool provides a way
  to run coral on SMT-LIBv2 constraints.

* [XSat][4] transform constraints into a mathematical global optimization
 problem. Unfortunately this tool is not open source.

* [goSAT][5] takes the ideas behind XSat but
  uses different optimization libraries and uses LLVM's JIT to generate code.

We are currently in the process of performing an evaluation of JFS against
these solvers and we will report these results in the not to distant future.

[2]: http://pan.cin.ufpe.br/coral/index.html
[3]: https://github.com/delcypher/smt2coral
[4]: https://www.researchgate.net/publication/305252908_XSat_A_Fast_Floating-Point_Satisfiability_Solver
[5]: https://github.com/abenkhadra/gosat

### How does JFS work?

To see how JFS works let's walk through a small example.

1. Parse SMT-LIB constraints using Z3.

```
(declare-fun a () (_ FloatingPoint 11 53))
(declare-fun b () (_ FloatingPoint 11 53))
(define-fun a_b_rne () (_ FloatingPoint 11 53) (fp.div RNE a b))
(define-fun a_b_rtp () (_ FloatingPoint 11 53) (fp.div RTP a b))
(assert (not (fp.isNaN a)))
(assert (not (fp.isNaN b)))
(assert (not (fp.eq a_b_rne a_b_rtp)))
(assert (not (fp.isNaN a_b_rne)))
(assert (not (fp.isNaN a_b_rtp)))
(check-sat)
```

2. Perform some simplifications on the constraints (e.g. constant folding).

**NOTE: You can use the jfs-opt tool to experiment with these simplifications.**

3. Generate a C++ program where the reachability of an `abort()` statement is
equivalent to finding a satisfying assignment to the constraints.

**NOTE: You can use the `jfs-smt2cxx` tool to convert SMT-LIBv2 constraints
into a program.**

```c++
extern "C" int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  if (size < 16) {
    return 0;
  }
  BufferRef<const uint8_t> jfs_buffer_ref =
      BufferRef<const uint8_t>(data, size);
  const Float<11, 53> a = makeFloatFrom<11, 53>(jfs_buffer_ref, 0, 63);
  const Float<11, 53> b = makeFloatFrom<11, 53>(jfs_buffer_ref, 64, 127);
  const bool jfs_ssa_0 = a.isNaN();
  const bool jfs_ssa_1 = !(jfs_ssa_0);
  if (jfs_ssa_1) {
  } else {
    return 0;
  }
  const bool jfs_ssa_2 = b.isNaN();
  const bool jfs_ssa_3 = !(jfs_ssa_2);
  if (jfs_ssa_3) {
  } else {
    return 0;
  }
  const Float<11, 53> jfs_ssa_4 = a.div(JFS_RM_RNE, b);
  const Float<11, 53> jfs_ssa_5 = a.div(JFS_RM_RTP, b);
  const bool jfs_ssa_6 = jfs_ssa_4.ieeeEquals(jfs_ssa_5);
  const bool jfs_ssa_7 = !(jfs_ssa_6);
  if (jfs_ssa_7) {
  } else {
    return 0;
  }
  const bool jfs_ssa_8 = jfs_ssa_4.isNaN();
  const bool jfs_ssa_9 = !(jfs_ssa_8);
  if (jfs_ssa_9) {
  } else {
    return 0;
  }
  const bool jfs_ssa_10 = jfs_ssa_5.isNaN();
  const bool jfs_ssa_11 = !(jfs_ssa_10);
  if (jfs_ssa_11) {
  } else {
    return 0;
  }
  // Fuzzing target
  abort();
}
```

4. This program is then compiled by Clang with coverage instrumentation
  and linked against LibFuzzer and a small runtime library. The runtime
  library implements the `Float` and `BitVector` SMT-LIBv2 types.

5. A set of seeds are generated for the fuzzer.

6. The compiled binary is invoked with the given seeds.
  If the fuzzer generates an input that reaches the `abort()` a satisfying
  assignment has been found and JFS terminates reporting `sat`.

Note this strategy will never find a satisfying assignment if one does not exist
(i.e. the constraints are unsatisfiable). This is why we say JFS is "incomplete"
because it cannot show that unsatisfiable constraints are unsatisfiable.

There is one exception to this. JFS can show unsatisfiable constraints to be
unsatisfiable if its simplications show one or more constraints to be `false`
(i.e. trivially unsatisfiable).
