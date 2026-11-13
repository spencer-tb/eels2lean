# eels2lean

Translate the
[Ethereum Execution Layer Specification (EELS)](https://github.com/ethereum/execution-specs)
from Python into [Lean 4](https://lean-lang.org).

**Status:** stage 1 started and stage 2 begun, pinned to EELS
`forks/amsterdam` at `1689800091` (see `eels.toml`). `max_message_call_gas`,
`calculate_memory_gas_cost`, `init_code_cost` and `ceil32` translate,
compile, and match EELS on about 2,000 boundary and random inputs each. So
do the functions of the EIP-8037 gas meter, which change a dataclass, and
`taylor_exponential`, which loops. See [Stage 2 so far](#stage-2-so-far).

## Usage

Needs [uv](https://docs.astral.sh/uv/), [just](https://just.systems),
[elan](https://github.com/leanprover/elan) and an EELS checkout with its
virtual environment (`EELS`, default `~/ethereum/execution-specs`).

```sh
just check                                     # translate, build, compare with EELS
just survey ethereum.forks.amsterdam.vm.gas    # what translates, and why the rest does not
just expected-update                           # after a change to the generated Lean
```

The Lean runtime in `lean/EelsRuntime.lean` gives Python's
`ethereum_types` arithmetic its meaning, written by hand. Generated files
under `lean/Eels/` are not committed.

## Why

[eels-proofs](https://github.com/spencer-tb/eels-proofs) proves that
execution clients compute exactly what EELS computes. Those proofs need
EELS in Lean. A hand-written Lean copy would need a matching change for
every EELS change, and only tests would catch the two drifting apart. A
translator keeps the Lean equal to EELS by construction, for every fork and
every EIP branch.

## How

- Reads EELS fork modules with Python's `ast` and the mypy types. EELS is
  strict mypy, so every type is known.
- Writes one Lean module per EELS module, keeping EELS names, so every
  Lean definition matches its EELS function one to one.
- Deterministic. No LLM in the translation.
- An unsupported Python construct is a hard error, never a guess.

| EELS (Python) | Lean |
|---|---|
| fork module | namespace per fork, imports mirror EELS |
| `@dataclass` | `structure` |
| `Uint` | `Nat` |
| `U64`, `U256` | fixed width, raise on overflow unless `wrapping_*` |
| `Bytes` | `ByteArray` |
| changes to the EVM and state | `EStateM`, with the changed dataclass as its state |
| `raise`, `try`, `except` | `Except`, or `EStateM` where there is state |
| `for`, `while` | recursion over lists, or a step limit |
| `dict`, `set` | finite maps and sets |
| keccak, secp256k1, BLS, KZG | opaque axioms, real code through FFI for running fixtures |

## Stages

1. Pure functions, such as gas formulas.
2. Opcodes and precompiles over an EVM state monad.
3. The whole fork through the EEST fixtures: state, child frames,
   journaling, trie.

## Stage 2 so far

A function that assigns to a field of a dataclass parameter is translated
into `EStateM Exc σ`, with that dataclass as the state `σ`. A run ends in a
value or an exception, and either way in the state it left. So a write made
before a `raise` stays written, as in Python. A function that only reads
its dataclass stays in `Except Exc` and takes the dataclass as a value.

A `while` becomes a function of its own that counts its steps down from
`fuel`, because Lean needs every function to end. It raises `OutOfFuel` when
no step is left. `OutOfFuel` is not a Python exception: it says the limit
was too small. Every function that reaches a `while` takes `fuel` as its
first argument.

`Exc` is an inductive type with one constructor per exception class the
translator can raise.

Covered now, and in the differential check:

- The `GasMeter` dataclass and the twelve functions of `vm/gas.py` that
  take one. Eleven change it. One of them, `withhold_create_gas`, is where
  `CREATE` and `CREATE2` apply the 63/64 rule.
- `taylor_exponential`, and `calculate_blob_gas_price` which calls it.
- `tests/cases`: functions written for the check, for behavior that no
  checked EELS function reaches. Today there is one, a write followed by a
  raise.

`tests/expected` holds the Lean generated for the gas meter and the loop,
so a change to the translator shows up as a change to them in review.
`just check` compares them, and `just expected-update` rewrites them.

Not yet, and a hard error today:

- A call to a function that changes its argument. The next step needs it:
  the `Evm` frame with its `GasMeter` inside, so that `charge_gas` and the
  four call opcodes translate. Those are the other sites of the 63/64
  rule, `CALL`, `CALLCODE`, `DELEGATECALL` and `STATICCALL`, where the gas
  the rule sees is what the frame has left after its earlier charges.
- A `while` in a function that changes a dataclass, `for` and `try`.
- A function that changes two dataclasses, or gives the one it changes a
  second name.
- Exception classes that have no constructor in `Exc` yet, and `except`
  by base class.

## Checking the translation

- The generated Lean type-checks.
- The EEST fixtures run through the compiled Lean and must match EELS.
- Per-function differential tests run random inputs through the Python
  and the Lean.

This may move into EELS as a workspace package later, run in EELS CI next
to `ethereum-spec-lint`.

## License

[CC0-1.0](LICENSE)
