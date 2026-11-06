"""
Command line entry point.

Translate EELS functions into Lean:

    eels2lean --src SRC --out LEAN --pin COMMIT FUNCTION...

Each FUNCTION is a fully qualified EELS name, for example
`ethereum.forks.amsterdam.vm.gas.max_message_call_gas`. With `--check`,
also write a Lean executable and a manifest for the differential test.

Survey which functions of a module translate:

    eels2lean --src SRC --survey MODULE
"""

import argparse
import ast
import json
import sys
from pathlib import Path

from .translate import (
    LEAN_ROOT,
    Project,
    Translator,
    Unsupported,
    ident,
    lean_module_name,
    render,
)


def write_modules(out: Path, sources: dict[str, str], root: str) -> None:
    """Write one Lean file per module and the umbrella module."""
    for module, source in sources.items():
        path = out.joinpath(root, *module.split(".")).with_suffix(".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source)
    umbrella = "".join(
        f"import {lean_module_name(m, root)}\n" for m in sorted(sources)
    )
    (out / f"{root}.lean").write_text(umbrella)


def write_check(out: Path, t: Translator, functions: list[str]) -> None:
    """
    Write `EelsCheck.lean` and `eels-check.json`.

    Only functions whose parameters and result are all `Uint`-based take
    part, because the check passes plain numbers.
    """
    checked = []
    for fq in functions:
        sig = t.signatures[t.canonical(fq)]
        kinds = [t.base(p) for _, p in sig.params] + [t.base(sig.returns)]
        if all(k == "Uint" for k in kinds):
            checked.append((t.canonical(fq), [n for n, _ in sig.params]))
    arms = []
    for fq, params in checked:
        names = [f"a{i}" for i in range(len(params))]
        ref = ".".join(ident(p) for p in fq.split("."))
        call = " ".join([ref, *names])
        arms.append(
            f'  | "{fq}", [{", ".join(names)}] => some ({call})'
        )
    source = (
        f"import {LEAN_ROOT}\nopen EelsRuntime\n\n"
        "/-- Call a generated function by name on natural numbers. -/\n"
        "def callFn : String → List Nat → Option (Except Exc Nat)\n"
        + "\n".join(arms)
        + "\n  | _, _ => none\n\n"
        "/-- Read `name arg...` lines, print `ok value` or `err Exception`. -/\n"
        "def main : IO Unit := do\n"
        "  let stdin ← IO.getStdin\n"
        "  let stdout ← IO.getStdout\n"
        "  repeat\n"
        "    let line ← stdin.getLine\n"
        "    if line.isEmpty then break\n"
        "    match (line.trimAscii.toString.splitOn \" \") with\n"
        "    | name :: args =>\n"
        "      match callFn name (args.filterMap String.toNat?) with\n"
        "      | some (.ok v) => stdout.putStrLn s!\"ok {v}\"\n"
        "      | some (.error e) => stdout.putStrLn s!\"err {e.name}\"\n"
        "      | none => stdout.putStrLn \"unknown\"\n"
        "    | [] => pure ()\n"
    )
    (out / "EelsCheck.lean").write_text(source)
    manifest = [{"function": fq, "params": params} for fq, params in checked]
    (out / "eels-check.json").write_text(json.dumps(manifest, indent=2) + "\n")


def survey(project: Project, module_name: str) -> int:
    """Try every top-level function of a module on its own, report each."""
    module = project.module(module_name)
    if module is None:
        print(f"no module {module_name}", file=sys.stderr)
        return 1
    ok = 0
    names = [
        n for n, d in module.defs.items() if isinstance(d, ast.FunctionDef)
    ]
    for name in names:
        t = Translator(project)
        try:
            t.require(f"{module_name}.{name}")
        except Unsupported as error:
            print(f"no   {name}: {error}")
        else:
            ok += 1
            print(f"ok   {name}")
    print(f"{ok}/{len(names)} functions translate")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(prog="eels2lean")
    parser.add_argument("--src", type=Path, required=True,
                        help="directory holding the `ethereum` package")
    parser.add_argument("--out", type=Path, help="Lean project directory")
    parser.add_argument("--pin", default="unknown", help="EELS commit")
    parser.add_argument("--root", default=LEAN_ROOT,
                        help="root Lean module for the generated files")
    parser.add_argument("--check", action="store_true",
                        help="also write the differential check")
    parser.add_argument("--survey", metavar="MODULE")
    parser.add_argument("functions", nargs="*")
    args = parser.parse_args()

    project = Project(args.src)
    if args.survey:
        return survey(project, args.survey)
    if args.out is None or not args.functions:
        parser.error("--out and at least one function are required")

    t = Translator(project)
    try:
        for fq in args.functions:
            t.require(fq)
        sources = render(t.items, args.pin, args.root)
    except Unsupported as error:
        print(f"unsupported: {error}", file=sys.stderr)
        return 1
    write_modules(args.out, sources, args.root)
    if args.check:
        write_check(args.out, t, args.functions)
    for module in sorted(sources):
        print(f"wrote {lean_module_name(module, args.root)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
