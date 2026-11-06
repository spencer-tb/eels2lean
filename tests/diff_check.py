"""
Differential check: pinned EELS Python against the generated Lean.

Run with a Python that has the EELS dependencies installed, for example
the EELS virtual environment:

    PYTHON -I tests/diff_check.py --src SRC --lean lean

Every function in `eels-check.json` gets boundary and random inputs. A
result is either `ok <number>` or `err <ExceptionName>`, and both sides
must agree on every input.
"""

import argparse
import importlib
import json
import random
import subprocess
import sys
from pathlib import Path

BOUNDARIES = sorted({
    0, 1, 2, 3, 31, 32, 33, 63, 64, 65, 127, 128, 511, 512, 513,
    2**16, 2**32 - 1, 2**32, 2**63 - 1, 2**63, 2**64 - 1, 2**64, 2**64 + 1,
    2**128, 2**255, 2**256 - 1, 2**256, 2**300,
})


def inputs(arity: int, rng: random.Random, count: int) -> list[tuple[int, ...]]:
    """Return boundary inputs plus `count` random ones of mixed sizes."""
    if arity == 1:
        cases = [(b,) for b in BOUNDARIES]
    else:
        cases = [tuple(rng.choice(BOUNDARIES) for _ in range(arity))
                 for _ in range(len(BOUNDARIES) * arity)]
    for _ in range(count):
        cases.append(tuple(rng.getrandbits(rng.choice((8, 16, 32, 64, 65, 128, 256)))
                           for _ in range(arity)))
    return cases


def run_python(function: str, args: tuple[int, ...]) -> str:
    from ethereum_types.numeric import Uint

    module_name, _, name = function.rpartition(".")
    fn = getattr(importlib.import_module(module_name), name)
    try:
        return f"ok {int(fn(*(Uint(a) for a in args)))}"
    except Exception as error:  # noqa: BLE001, every exception is a result
        return f"err {type(error).__name__}"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--src", type=Path, required=True)
    parser.add_argument("--lean", type=Path, required=True)
    parser.add_argument("--random", type=int, default=2000)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()

    sys.path.insert(0, str(args.src.resolve()))
    manifest = json.loads((args.lean / "eels-check.json").read_text())
    exe = args.lean / ".lake" / "build" / "bin" / "eels-check"
    rng = random.Random(args.seed)

    failures = 0
    for entry in manifest:
        function = entry["function"]
        cases = inputs(len(entry["params"]), rng, args.random)
        expected = [run_python(function, c) for c in cases]
        stdin = "".join(
            f"{function} {' '.join(map(str, c))}\n" for c in cases
        )
        got = subprocess.run(
            [str(exe)], input=stdin, capture_output=True, text=True, check=True
        ).stdout.splitlines()
        bad = [
            (c, e, g) for c, e, g in zip(cases, expected, got) if e != g
        ]
        if len(got) != len(cases):
            bad.append(((), f"{len(cases)} results", f"{len(got)} results"))
        errors = sum(e.startswith("err") for e in expected)
        status = "ok  " if not bad else "FAIL"
        print(f"{status} {function}: {len(cases)} inputs, {errors} raise, "
              f"{len(bad)} differ")
        for case, e, g in bad[:5]:
            print(f"     {case}: python {e}, lean {g}")
        failures += len(bad)
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
