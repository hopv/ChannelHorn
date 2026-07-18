# ChannelHorn

ChannelHorn translates message-passing concurrent programs into
constrained Horn clauses (CHCs) in SMT-LIB 2 format. By default, it generates
clauses for checking whether a `fail` statement is reachable. It can also
generate clauses for deadlock-freedom checking.

## Requirements

- Rust 1.85 or later and Cargo (the crate uses the Rust 2024 edition)

Generating CHCs and executing an input program do not require an external SMT
solver. To solve the generated file, install a CHC-capable solver such as
[Z3](https://github.com/Z3Prover/z3) or
[Catalia](https://zenodo.org/records/16220747) separately.

Z3 and Catalia are optional; neither is required to build the translator or
generate CHCs.

## Build

```console
cargo build --release
```

The resulting executable is `target/release/channel-horn`.

## Usage

Run the tool directly through Cargo:

```console
cargo run --release -- --file tests/core/spawn.txt --output output.smt2
```

Or run the built executable:

```console
./target/release/channel-horn --file tests/core/spawn.txt --output output.smt2
```

`--file` is required. If `--output` is omitted, the generated SMT-LIB 2 text is
written to standard output.

For the Rust-like sugar syntax, pass `--sugar`:

```console
cargo run --release -- \
  --file tests/catamorphism/constant.sugar \
  --sugar \
  --output output.smt2
```

The `--sugar` option also prints the desugared core program to standard output.

To generate CHCs for deadlock-freedom checking instead of fail reachability:

```console
cargo run --release -- \
  --file tests/core/spawn.txt \
  --deadlock \
  --output deadlock.smt2
```

The generated file includes `(check-sat)` and can be passed directly to a
solver, for example:

```console
z3 -smt2 output.smt2
```

## Command-line options

```text
Usage: channel-horn [OPTIONS] --file <FILE>
```

| Option | Description |
| --- | --- |
| `-f, --file <FILE>` | Read the input program from `FILE` (required). |
| `-o, --output <OUTPUT>` | Write the generated CHCs to `OUTPUT`; otherwise, print them to standard output. |
| `-s, --sugar` | Parse the input using the Rust-like sugar syntax and print the desugared core program. |
| `-e, --exec` | Execute the input program before generating its CHCs. |
| `--no-timestamps` | Generate CHCs without message timestamps. |
| `--deadlock` | Generate CHCs for deadlock-freedom checking instead of fail reachability. |
| `-h, --help` | Print command-line help. |
| `-V, --version` | Print the program version. |

`--exec` does not disable CHC generation. After execution finishes (or reports
an execution error), the tool still generates the CHCs and writes them to the
selected destination.
