# eels2lean

Translate the
[Ethereum Execution Layer Specification (EELS)](https://github.com/ethereum/execution-specs)
from Python into [Lean 4](https://lean-lang.org).

**Status:** not started. The package is empty.

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
| changes to the EVM and state | state monad |
| `raise`, `try`, `except` | `Except` |
| `for`, `while` | recursion over lists, or a step limit |
| `dict`, `set` | finite maps and sets |
| keccak, secp256k1, BLS, KZG | opaque axioms, real code through FFI for running fixtures |

## Stages

1. Pure functions, such as gas formulas.
2. Opcodes and precompiles over an EVM state monad.
3. The whole fork through the EEST fixtures: state, child frames,
   journaling, trie.

## Checking the translation

- The generated Lean type-checks.
- The EEST fixtures run through the compiled Lean and must match EELS.
- Per-function differential tests run random inputs through the Python
  and the Lean.

This may move into EELS as a workspace package later, run in EELS CI next
to `ethereum-spec-lint`.

## License

[CC0-1.0](LICENSE)
