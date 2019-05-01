# HolBA - Binary analysis in HOL 

## Software versions

- HOL4 (`https://github.com/kth-step/HOL`)
  - branch: for_holba (i.e. tags/kananaskis-12 + holsmt-arrays + syntax-errors)
- Poly/ML (e.g. current Poly/ML version packaged for Ubuntu, 5.7.1)


## How to compile

### As bash commands
```
git clone https://github.com/kth-step/HolBA.git
cd HolBA

./scripts/setup/install_all.sh

. ./scripts/setup/env.sh

make main
make tests

cd src/examples/aes
${HOLBA_HOLMAKE}
```

### With explanations
* To setup all dependencies in your working directory, change to the root directory (`{HOLBA_DIR}`) and run `./scripts/setup/install_all.sh`. This downloads and builds the correct polyml and HOL4 versions in the subdirectory `{HOLBA_DIR}/opt`.

* For convenience the environment should be augmented with `. ./scripts/setup/env.sh`. This allows easy calls to the build system.

* To build HolBA, run `make main`. For more specific targets run `make [tests|examples|benchmarks|...]` according to your needs (use `make show-rules` to see existing rules).

* For specific source directories, `cd` there and run `${HOLBA_HOLMAKE}`.

* If one of the previous steps fails, try to clean your Git working directory by
  `make cleanslate` in the project root directory. **Be careful though**, this
  command is quite dangerous as it can easily eat your files (`Holmakefile`s are
  auto-generated from `Holmakefile.gen` files, so they are removed by this
  command).

* With this setup, you should run the `. ./scripts/setup/env.sh` before working with HolBA each time you open a new shell. You could also put this into `~/.bashrc`.

_Note_: You can use `make --directory=${HOLBA_DIR} rule`.

### Shared dependencies and `~/.bashrc`

To setup dependencies and develop HolBA conveniently, you need:
* One HolBA directory with the setup scripts. We call this `{HOLBA_DIR}`.
* A directory where you want to install and place the shared dependencies. We call this `{HOLBA_OPT_DIR}`.
* Add the following to your `~/.bashrc` file:
```
export HOLBA_DIR=/path/to/{HOLBA_DIR}
export HOLBA_OPT_DIR=/path/to/{HOLBA_OPT_DIR}

${HOLBA_DIR}/scripts/setup/install_all.sh
. ${HOLBA_DIR}/scripts/setup/env.sh
```


## Branch policy

### tags

tags should have as many **completed features** as possible:
 - no cheat
 - must correctly compile
 - self tests must succeed
 - code should be tested

Follow these instructions whenever you merge to master:
  - `grep` for "cheat"
  - check that the `README` is up to date (especially tool status)
  - find a reviewer for your Pull Request

### `master` branch

`master` is the branch where every feature is available, but not necessarily finalized:
  - Can cheat, but has to be avoided
  - Code should not be be commented out
  - **Holmake must work**
  - bug-fixes are ok
  - 1 review is needed in order to merge into `master`

However, **no development happens on this branch**, but rather on separate
feature branches.

**In order to prevent mayhem**, define good interfaces for your code, so that
development won't break existing code.

### Feature branches

Every "somewhat" working tool should be available in the `master` branch, but new
features or any development must go on new branches prefixed with `dev_`.
 - branch names must be short and explicit (prefer explicit over short)
 - every feature branch should involve small developments
 - rebase feature branches on `master` **often**, by using `git rebase` or `git merge`
 - **merge feature branches on `master` often**: work on small features

Some rules for feature branches:
 - commits in a feature branch must compile, unless explicitly stated in commit
   message (with the prefix `[WIP] ...` for instance)
 - further subbranch to do implementation experiments (keep them small)

If you want to violate the rules for temporary development or experiments (only
for feature branches):
  1. Fork
  2. Do a good mess
  3. Merge in feature branch after history rewrite


## Folders and organization

```
├─ doc
└─ src
   ├─ core: core BIR language
   ├─ libs: general BIR libraries, used by tools
   │  └─ examples: Examples showcasing the use of libs/ libraries.
   ├─ theories: various supporting theories
   ├─ tools
   │  ├─ cfg: Control Flow Graph utilities
   │  │  └─ examples: CFG-related small examples
   │  ├─ exec: concrete execution
   │  │  └─ examples: concrete execution-related small examples
   │  ├─ lifter: proof-producing binary lifter
   │  │  ├─ benchmark
   │  │  └─ examples: lifter-related small examples
   │  ├─ pass: Passification utility
   │  │  └─ examples: Passification-related small examples
   │  └─ wp: weakest precondition propagation
   │     ├─ benchmark
   │     └─ examples: WP-related small examples
   └─ examples: to showcase HolBA features
```

### Tools status:

- `tools/cfg`:
  * non proof-producing
  * no clear interface yet
  * GraphViz exporter working
- `tools/exec`:
  * proof-producing
  * unstable BIR evaluation utilities
  * quite easy to use
- `tools/lifter`:
  * merged in `master` => very stable
  * proof-producing
  * widely used in examples
  * supports: ARMv8, Cortex-M0
- `tools/wp`:
  * proof-producing
  * experimental implementation
    * includes prototype of substitution simplification
  * interface in progress
- `tools/pass`:
  * non proof-producing
  * experimental passification transformation to SSA

### Dependency graph and PolyML heaps

![Dependency diagram](./doc/diagrams/dependencies.png?raw=true)

Key:
 - Blue edges represent dependencies between HolBA modules.
 - Green edges represent the chain of PolyML heaps. See HOL's Description Manual
   for more information about PolyML heaps.

_Note_:
- You can temporarily change the heap chain order if you don't need a dependency
  in order to reduce build times.

## Coding style

* HOL source code
  - Spaces, no tabs
  - No unicode
  - `snake_case` (e.g. `bir_number_of_mem_splits_def`)
