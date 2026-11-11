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

    A function takes part when its parameters are `Uint`, `U64` or `U256`
    based, and its result is `Uint` based or a dataclass of `Uint` based
    fields. The check passes plain numbers and prints the result's numbers.
    """
    numeric = {"Uint", "U64", "U256"}
    bits = {"U64": 64, "U256": 256}
    arms = []
    manifest = []
    for fq in functions:
        fq = t.canonical(fq)
        sig = t.signatures[fq]
        kinds = [t.base(p) for _, p in sig.params]
        result = t.base(sig.returns)
        if result in t.records:
            fields = [n for n, ft in t.records[result] if t.base(ft) == "Uint"]
            if len(fields) != len(t.records[result]):
                continue
        elif result == "Uint":
            fields = None
        else:
            continue
        if not all(k in numeric for k in kinds):
            continue
        names = [f"a{i}" for i in range(len(kinds))]
        lines = []
        args = []
        for i, kind in enumerate(kinds):
            if kind in bits:
                lines.append(f"let v{i} ← EelsRuntime.Fixed.ofNat {bits[kind]} a{i}")
                args.append(f"v{i}")
            else:
                args.append(f"a{i}")
        ref = ".".join(ident(p) for p in fq.split("."))
        lines.append(f"let r ← {ref} {' '.join(args)}")
        values = ", ".join(f"r.{ident(f)}" for f in fields) if fields else "r"
        lines.append(f"return [{values}]")
        body = "".join(f"\n      {line}" for line in lines)
        arms.append(f'  | "{fq}", [{", ".join(names)}] => some (do{body})')
        manifest.append({
            "function": fq,
            "params": [{"name": n, "kind": k} for (n, _), k in zip(sig.params, kinds)],
            "fields": fields,
        })
    source = (
        f"import {LEAN_ROOT}\nopen EelsRuntime\n\n"
        "/-- Call a generated function by name on natural numbers. -/\n"
        "def callFn : String → List Nat → Option (Except Exc (List Nat))\n"
        + "\n".join(arms)
        + "\n  | _, _ => none\n\n"
        "/-- Read `name arg...` lines, print `ok value...` or `err Exception`. -/\n"
        "def main : IO Unit := do\n"
        "  let stdin ← IO.getStdin\n"
        "  let stdout ← IO.getStdout\n"
        "  repeat\n"
        "    let line ← stdin.getLine\n"
        "    if line.isEmpty then break\n"
        "    match (line.trimAscii.toString.splitOn \" \") with\n"
        "    | name :: args =>\n"
        "      match callFn name (args.filterMap String.toNat?) with\n"
        "      | some (.ok vs) => stdout.putStrLn (\"ok \" ++ \" \".intercalate (vs.map toString))\n"
        "      | some (.error e) => stdout.putStrLn s!\"err {e.name}\"\n"
        "      | none => stdout.putStrLn \"unknown\"\n"
        "    | [] => pure ()\n"
    )
    (out / "EelsCheck.lean").write_text(source)
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
