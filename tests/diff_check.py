"""
Differential check: pinned EELS Python against the generated Lean.

Run with a Python that has the EELS dependencies installed, for example
the EELS virtual environment:

    PYTHON -I tests/diff_check.py --src SRC --lean lean

Every function in `eels-check.json` gets boundary and random inputs. A
result is either `ok <number>...` or `err <ExceptionName>`. For a function
that changes a dataclass, ` | <number>...` follows: the fields of that
dataclass after the call, whether it returned or raised. Both sides must
agree on every input.

An input is one integer per number, in parameter order. A dataclass
parameter takes one integer per field.
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


def inputs(
    kinds: list[str], rng: random.Random, count: int
) -> list[tuple[int, ...]]:
    """
    Return boundary inputs plus `count` random ones of mixed sizes.

    An `int` is negative half of the time.
    """
    arity = len(kinds)
    if arity == 1:
        cases = [(b,) for b in BOUNDARIES]
    else:
        cases = [tuple(rng.choice(BOUNDARIES) for _ in range(arity))
                 for _ in range(len(BOUNDARIES) * arity)]
    for _ in range(count):
        cases.append(tuple(rng.getrandbits(rng.choice((0, 8, 16, 32, 64, 65, 128, 256)))
                           for _ in range(arity)))
    if "int" not in kinds:
        return cases
    return [
        tuple(-n if kind == "int" and rng.random() < 0.5 else n
              for kind, n in zip(kinds, case))
        for case in cases
    ]


def find(name: str):
    """Return the Python object called `name`."""
    module_name, _, attribute = name.rpartition(".")
    return getattr(importlib.import_module(module_name), attribute)


def convert(kind: str, number: int):
    """Return `number` as the Python type the check calls `kind`."""
    from ethereum_types import numeric

    return number if kind == "int" else getattr(numeric, kind)(number)


def run_python(entry: dict, args: tuple[int, ...]) -> str:
    fn = find(entry["function"])
    numbers = iter(args)
    # A dataclass takes one integer per field. It is built before the call,
    # so the one the function changes can be read back after a raise.
    values = []
    state = None
    for param in entry["params"]:
        if "class" in param:
            value = find(param["class"])(
                *(convert(f["kind"], next(numbers)) for f in param["fields"])
            )
            values.append(lambda value=value: value)
            if param["name"] == entry["state"]:
                state = [(value, f["name"]) for f in param["fields"]]
        else:
            values.append(
                lambda kind=param["kind"], n=next(numbers): convert(kind, n)
            )
    try:
        result = fn(*(value() for value in values))
        names = entry["fields"]
        results = [result] if names is None else [getattr(result, n) for n in names]
        out = ["ok", *(str(int(n)) for n in results)]
    except Exception as error:  # noqa: BLE001, every exception is a result
        out = ["err", type(error).__name__]
    if state is not None:
        out += ["|", *(str(int(getattr(value, name))) for value, name in state)]
    return " ".join(out)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--src", type=Path, required=True, action="append")
    parser.add_argument("--lean", type=Path, required=True)
    parser.add_argument("--random", type=int, default=2000)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()

    for src in reversed(args.src):
        sys.path.insert(0, str(src.resolve()))
    manifest = json.loads((args.lean / "eels-check.json").read_text())
    exe = args.lean / ".lake" / "build" / "bin" / "eels-check"
    rng = random.Random(args.seed)

    failures = 0
    for entry in manifest:
        function = entry["function"]
        kinds = [
            f["kind"] for p in entry["params"] for f in p.get("fields", [p])
        ]
        cases = inputs(kinds, rng, args.random)
        expected = [run_python(entry, c) for c in cases]
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
