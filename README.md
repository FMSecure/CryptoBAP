# CryptoBAP2 (beta)

CryptoBAP2 is a binary-to-protocol-model pipeline.  It lifts selected machine
code into HOL/BIR artifacts, symbolically executes the selected code, records a
binary model, writes Sapic output, and can export a configured Tamarin source to
Squirrel.

Squirrel output is not produced from a raw binary alone.  A case that targets
Squirrel must provide `artifacts.tamarin_source`; generated Sapic is not treated
as `.spthy` input.

## Functionality

CryptoBAP2 is driven by YAML case files in `cases/`.  A case describes the input
binary or HolBA-compatible `.da` disassembly, the architecture, selected
symbols/fragments, library and adversary functions, and the cryptographic
meaning of selected calls.

The production pipeline is:

1. disassemble a binary to HolBA-compatible `.da` text when the input is a raw
   binary,
2. lift the `.da` file into BIR/HOL,
3. run HOL symbolic execution over the selected entry points or fragments,
4. write a binary model and Sapic process for the symbolic execution result,
5. optionally stage a configured Tamarin `.spthy` file and export it to
   Squirrel `.sp`.

The main generated artifacts for a case are:

- `bir/<case>.da`: disassembly used for lifting,
- `model/<case>.binary-model.json`: symbolic-execution model metadata,
- `sapic/<case>.sapic`: generated Sapic process,
- `spthy/<case>.spthy`: staged Tamarin source, when configured,
- `squirrel/<case>.sp`: Squirrel export, when configured,
- `manifest.json`: tool paths, stage metadata, artifact hashes, and diagnostics.

Generated proof statuses are intentionally conservative.  New case artifacts are
marked `generated_unchecked` until they have been reviewed and validated.

## Dependencies

CryptoBAP2 coordinates several tools rather than replacing them.  The expected
dependencies are:

| Dependency | Used for | Configuration |
| --- | --- | --- |
| Python 3 | Running the `cryptobap2` CLI | `python3` on `PATH` |
| PyYAML | Reading YAML case files | `toolchain/requirements.txt` |
| [HOL4](https://github.com/HOL-Theorem-Prover/HOL) | Building generated and support HOL theories | `HOLMAKE` or `--holmake` |
| [HolBA](https://github.com/kth-step/HolBA) | Lifting `.da` disassembly into BIR/HOL | `HOLBA_DIR`, `HOLBADIR`, or `--holba` |
| [Tamarin prover (Squirrel export fork)](https://github.com/yflxx/tamarin-prover-sqrl) | Staging and exporting configured `.spthy` sources | `TAMARIN` or `--tamarin` |
| [Squirrel prover](https://github.com/squirrel-prover/squirrel-prover) | Validating generated Squirrel files | `SQUIRREL` or `--squirrel` |
| [Ghidra](https://github.com/NationalSecurityAgency/ghidra) | Disassembling raw binaries to HolBA-compatible `.da` text | `GHIDRA_HEADLESS`, `GHIDRA_HOME`, or `--ghidra` |
| Java/JDK 21+ | Running Ghidra | `java` on `PATH` |

HolBA and `Holmake` are required for the lift and symbolic-execution stages.
Tamarin and Squirrel are required for Squirrel export and validation.  Ghidra and
Java are only required when the input is a raw binary; cases that already point
to a `.da` file can run without Ghidra.

Configure tool paths either with environment variables or with global CLI
options. CryptoBAP2 does not assume dependency checkouts inside the repository.

```sh
./cryptobap2 \
  --holba "$HOLBA_DIR" \
  --holmake "$HOLMAKE" \
  --tamarin "$TAMARIN" \
  --squirrel "$SQUIRREL" \
  --ghidra "$GHIDRA_HEADLESS" \
  doctor
```

## Build

Run commands from the CryptoBAP2 directory.

CryptoBAP2's CLI is Python, so there is no separate native build step for the
tool itself.  Install the Python dependency and check the external tools:

```sh
python3 -m pip install -r toolchain/requirements.txt
./cryptobap2 doctor
```

`doctor` checks HolBA, `Holmake`, Tamarin, Squirrel, Ghidra, Java, PyYAML, and
registered case metadata.  Ghidra needs Java/JDK 21 or newer.  If Ghidra is
missing and you want to start from raw binaries, install the pinned portable
copy:

```sh
./cryptobap2 install-ghidra
```

The HOL pieces are built by `Holmake` as part of the pipeline stages.  To make
sure external tools and registered case metadata are available, run:

```sh
./cryptobap2 doctor --strict
```

Then run the production pipeline with an explicit build root:

```sh
./cryptobap2 --build-root _build/xor run cases/xor.yaml --target squirrel --install-ghidra
```

If you only need the binary model and Sapic output, stop after model extraction:

```sh
./cryptobap2 --build-root _build/xor extract-model cases/xor.yaml --install-ghidra
```

Global options such as `--build-root`, `--holba`, `--holmake`, `--tamarin`,
`--squirrel`, and `--ghidra` go before the subcommand.

## Example Case

The smallest registered example is `cases/xor.yaml`.  It models a small AArch64
program that creates a key, encrypts a value with XOR-style encryption, and sends
selected values on the public channel.

The checked-in cases include the input disassembly and backend fixtures they
reference under `examples/`, so the registered examples can be checked without
depending on paths outside this directory.

The important parts of the case are:

```yaml
name: xor
arch: arm8
channel: Channel
input:
  da: examples/binaries/protocols/xor/xor.da
  theory: XORexample
  symbols: [new_key, senc, send, main]
execution:
  entry_label: 60
  exit_labels: [132]
functions:
  library: [senc, new_key, send]
  adversary: [recv]
  crypto:
    send: MEMcpy
    new_key: OTP
    senc: XOR
artifacts:
  sapic_source: examples/protocols/xor/Sapic_Translation.txt
  tamarin_source: examples/backend-results/xor.spthy
backends: [tamarin, squirrel]
```

Run the full case:

```sh
BUILD_ROOT=_build/xor
CASE=cases/xor.yaml

./cryptobap2 --build-root "$BUILD_ROOT" run "$CASE" --target squirrel --install-ghidra
```

After a successful run, the main outputs are under `_build/xor/xor/`:

- `bir/xor.da`
- `model/xor.binary-model.json`
- `sapic/xor.sapic`
- `spthy/xor.spthy`
- `squirrel/xor.sp`
- `manifest.json`

The build root also gets `_cryptobap2-support-cache/`, a shared Holmake cache
for CryptoBAP2's stable HOL support sources.  Per-case directories stay small:
they contain generated runners, local HOL objects, logs, and a copy of the case
configuration used for the run.

## New Binaries

For a new binary, start with `extract-model`:

```sh
./cryptobap2 --build-root _build/my-program extract-model my-program.elf --arch arm8 --install-ghidra
```

This disassembles the binary, infers fragments, runs symbolic execution, and
writes `work/inferred-case.yaml`.  Pass `--symbols` when you know the entry
points:

```sh
./cryptobap2 --build-root _build/my-program extract-model my-program.elf --arch arm8 --symbols main,helper --install-ghidra
```

If you already have HolBA-compatible disassembly, pass the `.da` file:

```sh
./cryptobap2 --build-root _build/my-program extract-model my-program.da --arch arm8 --symbols main,helper
```

For a whole-disassembly model, use `--scope all-functions`:

```sh
./cryptobap2 --build-root _build/my-program extract-model my-program.da --arch arm8 --scope all-functions
```

Use `--write-case my-program.yaml` if you want to keep the inferred YAML.
Review inferred fragments and function classifications before relying on the
model.

To inspect labels before editing fragment boundaries:

```sh
BUILD_ROOT=_build/xor
CASE=cases/xor.yaml

./cryptobap2 --build-root "$BUILD_ROOT" lift "$CASE" --install-ghidra
sed -n '1,120p' "$BUILD_ROOT/xor/bir/xor.da"
sed -n '1,120p' "$BUILD_ROOT/xor/bir/lifted-program-labels.txt"
```

## Squirrel Export

Squirrel export needs a Tamarin source in the case file:

```yaml
artifacts:
  tamarin_source: examples/backend-results/xor.spthy
```

Then run either:

```sh
BUILD_ROOT=_build/xor
CASE=cases/xor.yaml

./cryptobap2 --build-root "$BUILD_ROOT" run "$CASE" --target squirrel
```

or stage the backend step separately:

```sh
./cryptobap2 --build-root "$BUILD_ROOT" extract-model "$CASE"
./cryptobap2 --build-root "$BUILD_ROOT" export "$CASE" --target squirrel
```

Add `--readable-squirrel` to `run` or `export` to also write
`squirrel/<case>.readable.sp`.  That file is for inspection only; validation
uses `<case>.sp`.

## Checks

`run` invokes `check` after building the requested backend.  In this artifact,
`check` validates the generated artifacts for a case and can report expected
warnings or errors when a stage has not been run yet:

- Squirrel export depends on `artifacts.tamarin_source` in the case file.
- Local generated `.hol` directories may be reported if they are left in the
  source tree.

Run checks directly with:

```sh
./cryptobap2 --build-root "$BUILD_ROOT" check "$CASE"
./cryptobap2 --build-root "$BUILD_ROOT" check "$CASE" --json
```

## Useful Commands

```sh
./cryptobap2 list-cases
./cryptobap2 doctor
./cryptobap2 install-ghidra
./cryptobap2 disassemble my-program.elf --arch arm8 --output _build/my-program.da
./cryptobap2 scaffold-case my-program.elf --arch arm8 --symbols main --install-ghidra
./cryptobap2 lift my-case.yaml
./cryptobap2 symexec my-case.yaml
./cryptobap2 extract-model my-case.yaml
./cryptobap2 export squirrel-case.yaml --target squirrel
./cryptobap2 run squirrel-case.yaml --target squirrel
./cryptobap2 check my-case.yaml
```

## Repository Layout

- `cryptobap2`: Python entry point.
- `bin/cryptobap2`: wrapper for adding CryptoBAP2 to `PATH`.
- `toolchain/cryptobap2/`: Python CLI and pipeline code.
- `src/sapic/`: Sapic and Dolev-Yao syntax/semantics.
- `src/translate_to_sapic/`: symbolic-execution tree to Sapic translation.
- `src/tree/`: symbolic-execution tree helpers.
- `src/pretty_print/`: Sapic rendering and pipeline entry points.
- `src/pipeline_support/`: maintained HOL symbolic-execution support code.
- `cases/`: registered CLI cases.
- `scripts/ghidra/`: Ghidra export scripts used for disassembly.
