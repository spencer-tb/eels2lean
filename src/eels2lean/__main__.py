"""
Command line entry point.

Translate EELS functions into Lean:

    eels2lean --src SRC [--src MORE] --out LEAN --pin COMMIT FUNCTION...

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
    FIXED_BYTES,
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


# Kinds of number the differential check can pass in and read back.
CHECK_BITS = {"U8": 8, "U64": 64, "U256": 256}
CHECK_FIELDS = ("Uint", "int")
CHECK_PARAMS = (*CHECK_FIELDS, *CHECK_BITS)
# The step limit the check gives a function with a `while`.
CHECK_FUEL = 256

CHECK_PRELUDE = """\
/-- What one call gave: numbers or an exception, and the changed dataclass. -/
structure Outcome where
  result : Except Exc (List Int)
  state : Option (List Int) := none

/-- Run a call that changes a dataclass, then read the dataclass back. -/
def runWith {σ : Type} (call : EStateM Exc σ (List Int)) (start : σ)
    (fields : σ → List Int) : Outcome :=
  match call.run start with
  | .ok values s => ⟨.ok values, some (fields s)⟩
  | .error e s => ⟨.error e, some (fields s)⟩

"""

CHECK_MAIN = """\
/--
Read `name integer...` lines. Print `ok number...` or `err Exception`, then
` | number...` for the fields of the changed dataclass, if there is one.
-/
def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    match (line.trimAscii.toString.splitOn " ") with
    | name :: args =>
      match callFn name (args.filterMap String.toInt?) with
      | some outcome =>
        let result := match outcome.result with
          | .ok values => "ok" :: values.map toString
          | .error e => ["err", e.name]
        let state := match outcome.state with
          | some fields => "|" :: fields.map toString
          | none => []
        stdout.putStrLn (" ".intercalate (result ++ state))
      | none => stdout.putStrLn "unknown"
    | [] => pure ()
"""


def check_number(lean: str, kind: str) -> str:
    """Return Lean for the integer the check prints for `lean`."""
    if kind == "Uint":
        return f"Int.ofNat {lean}"
    if kind in CHECK_BITS:
        return f"Int.ofNat {lean}.val"
    return lean


def check_default(t: Translator, py_type: str) -> tuple[str, dict] | None:
    """
    Return a fixed value of a field that is no number, in Lean and for the
    manifest: empty bytes, zero bytes of a fixed size, an empty tuple,
    `None`, or such a value of the first type of a union.
    """
    kind = t.base(py_type)
    if kind == "Bytes":
        return "ByteArray.empty", {"bytes": None}
    size = FIXED_BYTES.fullmatch(kind)
    if size:
        n = int(size.group(1))
        return f"⟨⟨Array.replicate {n} 0⟩, by decide⟩", {"bytes": n}
    if kind.startswith("Tuple["):
        return "[]", {"tuple": True}
    if kind in t.optionals:
        return "none", {"none": True}
    if kind in t.compound and " | " in kind:
        first = check_default(t, kind.split(" | ")[0])
        if first is None:
            return None
        return f"(.inl {first[0]})", first[1]
    return None


def check_arm(t: Translator, fq: str) -> tuple[str, dict] | None:
    """Return the `callFn` arm and the manifest entry of one function."""
    sig = t.signatures[fq]
    result = t.base(sig.returns)
    if result in t.records:
        fields = [(n, t.base(ft)) for n, ft in t.records[result]]
        if not all(kind in CHECK_FIELDS for _, kind in fields):
            return None
        values = [check_number(f"r.{ident(n)}", kind) for n, kind in fields]
        names: list[str] | None = [n for n, _ in fields]
    elif result in CHECK_PARAMS:
        values = [check_number("r", result)]
        names = None
    elif result in t.optionals and t.base(t.optionals[result]) in CHECK_PARAMS:
        # `None` prints as no number at all.
        inner = t.base(t.optionals[result])
        values = None
        names = None
    elif result == "None":
        values = []
        names = []
    else:
        return None

    # One integer per number, in parameter order. A dataclass takes one
    # per field.
    inputs: list[str] = []

    def number(kind: str) -> str:
        inputs.append(f"a{len(inputs)}")
        return inputs[-1] if kind == "int" else f"{inputs[-1]}.toNat"

    lines = []
    args = []
    params = []
    state = ""
    for name, py_type in sig.params:
        kind = t.base(py_type)
        if kind in t.records:
            fields = [(n, t.base(ft)) for n, ft in t.records[kind]]
            if not all(k in CHECK_FIELDS for _, k in fields):
                return None
            lean_type = ".".join(ident(p) for p in kind.split("."))
            value = ", ".join(f"{ident(n)} := {number(k)}" for n, k in fields)
            if name == sig.state:
                read = ", ".join(check_number(f"s.{ident(n)}", k) for n, k in fields)
                state = (
                    f" (σ := {lean_type})", f"{{ {value} }}", f"(fun s => [{read}])"
                )
            else:
                args.append(f"({{ {value} }} : {lean_type})")
            params.append({
                "name": name,
                "class": kind,
                "fields": [{"name": n, "kind": k} for n, k in fields],
            })
        elif kind in t.unions:
            found = check_union(t, kind, inputs)
            if found is None:
                return None
            lines += found[0]
            args.append(found[1])
            params.append({"name": name, **found[2]})
        elif kind in CHECK_BITS:
            lines.append(
                f"let v{len(inputs)} ← "
                f"EelsRuntime.Fixed.ofNat {CHECK_BITS[kind]} {number(kind)}"
            )
            args.append(f"v{len(inputs) - 1}")
            params.append({"name": name, "kind": kind})
        elif kind in CHECK_FIELDS:
            args.append(number(kind))
            params.append({"name": name, "kind": kind})
        else:
            return None
    if sig.fuel:
        args.insert(0, str(CHECK_FUEL))
    call = " ".join([".".join(ident(p) for p in fq.split(".")), *args])
    if values is None:
        lines.append(f"let r ← {call}")
        lines.append(
            f"return (match r with | some x => [{check_number('x', inner)}]"
            " | none => [])"
        )
    else:
        lines.append(f"let r ← {call}" if values else call)
        lines.append(f"return [{', '.join(values)}]")
    body = "".join(f"\n      {line}" for line in lines)
    pattern = f'  | "{fq}", [{", ".join(inputs)}] => some '
    if state:
        arm = (
            f"{pattern}(runWith{state[0]} (do{body})\n"
            f"      {state[1]}\n      {state[2]})"
        )
    else:
        arm = f"{pattern}⟨(do{body}), none⟩"
    entry = {
        "function": fq,
        "params": params,
        "fields": names,
        "state": sig.state,
        "fuel": CHECK_FUEL if sig.fuel else None,
    }
    return arm, entry


def check_union(
    t: Translator, kind: str, inputs: list[str]
) -> tuple[list[str], str, dict] | None:
    """
    Return the lines that build a value of a named union, its Lean, and
    its manifest entry.

    The first integer picks the class, modulo the number of classes. One
    integer per number field follows, as many as the class with the most
    of them needs. A field that is no number gets a fixed value.
    """
    members = []
    for member in t.unions[kind]:
        fields = []
        for name, py_type in t.records[member]:
            field_kind = t.base(py_type)
            if field_kind in CHECK_PARAMS:
                fields.append((name, field_kind, None))
                continue
            default = check_default(t, py_type)
            if default is None:
                return None
            fields.append((name, None, default))
        members.append((member, fields))
    width = max(sum(k is not None for _, k, _ in f) for _, f in members)
    first = len(inputs)
    inputs += [f"a{first + i}" for i in range(width + 1)]
    tag, numbers = inputs[first], inputs[first + 1:]

    lean_kind = ".".join(ident(p) for p in kind.split("."))
    arms = []
    entries = []
    for index, (member, fields) in enumerate(members):
        body = []
        assigned = []
        used = iter(numbers)
        entry_fields = []
        for name, field_kind, default in fields:
            if field_kind is None:
                assigned.append(f"{ident(name)} := {default[0]}")
                entry_fields.append({"name": name, "default": default[1]})
                continue
            number = next(used)
            if field_kind in CHECK_BITS:
                body.append(
                    f"let {number}' ← EelsRuntime.Fixed.ofNat "
                    f"{CHECK_BITS[field_kind]} {number}.toNat"
                )
                assigned.append(f"{ident(name)} := {number}'")
            elif field_kind == "Uint":
                assigned.append(f"{ident(name)} := {number}.toNat")
            else:
                assigned.append(f"{ident(name)} := {number}")
            entry_fields.append({"name": name, "kind": field_kind})
        short = ident(member.rpartition(".")[2])
        body.append(f"pure ({lean_kind}.{short} {{ {', '.join(assigned)} }})")
        pattern = "_" if index == len(members) - 1 else str(index)
        arms.append(
            f"| {pattern} => do\n"
            + "".join(f"          {line}\n" for line in body)
        )
        entries.append({"class": member, "fields": entry_fields})
    value = f"u{first}"
    lines = [f"let {value} ← (match {tag}.toNat % {len(members)} with\n"
             + "".join(f"        {arm}" for arm in arms).rstrip("\n") + ")"]
    return lines, value, {"union": entries, "width": width}


def write_check(out: Path, t: Translator, functions: list[str]) -> None:
    """
    Write `EelsCheck.lean` and `eels-check.json`.

    A function takes part when each parameter is a `Uint`, `U8`, `U64`,
    `U256` or `int` based number, a dataclass of `Uint` and `int` based
    numbers, or a named union of dataclasses. Its result is `None`, such a
    number, such a number or `None`, or such a dataclass.

    The check passes plain integers in parameter order, one per number
    and one per field of a dataclass. It prints the result's numbers.
    For a function that changes a dataclass it then prints the fields of
    that dataclass as the call left them, whether it returned or raised.
    A function with a `while` gets `CHECK_FUEL` as its step limit.
    """
    arms = []
    manifest = []
    for fq in functions:
        found = check_arm(t, t.canonical(fq))
        if found is not None:
            arms.append(found[0])
            manifest.append(found[1])
    source = (
        f"import {LEAN_ROOT}\nopen EelsRuntime\n\n"
        + CHECK_PRELUDE
        + "/-- Call a generated function by name on integers. -/\n"
        "def callFn : String → List Int → Option Outcome\n"
        + "\n".join(arms)
        + "\n  | _, _ => none\n\n"
        + CHECK_MAIN
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
    parser.add_argument("--src", type=Path, required=True, action="append",
                        help="directory holding the `ethereum` package; "
                             "repeat to add directories of other modules")
    parser.add_argument("--out", type=Path, help="Lean project directory")
    parser.add_argument("--pin", default="unknown", help="EELS commit")
    parser.add_argument("--root", default=LEAN_ROOT,
                        help="root Lean module for the generated files")
    parser.add_argument("--check", action="store_true",
                        help="also write the differential check")
    parser.add_argument("--survey", metavar="MODULE")
    parser.add_argument("functions", nargs="*")
    args = parser.parse_args()

    project = Project(*args.src)
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
