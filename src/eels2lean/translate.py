"""
Translate EELS functions, and everything they reference, into Lean 4.

The translator reads EELS source with `ast`. It starts from the requested
functions and follows every name they use to its definition, across
modules. Each EELS module becomes one Lean module, and each definition
keeps its EELS name inside a namespace equal to its EELS module path.

A function that only computes returns `Except Exc α`. A function that
assigns to a field of a dataclass parameter returns `EStateM Exc σ α`, with
that parameter as the state `σ`, so a write made before a raise is kept.

Anything outside the supported subset raises `Unsupported`, naming the file
and line. The translator never guesses.
"""

import ast
from dataclasses import dataclass, field
from pathlib import Path

RUNTIME = "EelsRuntime"
LEAN_ROOT = "Eels"

# Types from `ethereum_types.numeric`, mapped to runtime types.
NUMERIC = {
    "ethereum_types.numeric.Uint": "Uint",
    "ethereum_types.numeric.U64": "U64",
    "ethereum_types.numeric.U256": "U256",
}
FIXED_BITS = {"U64": 64, "U256": 256}
BUILTIN_TYPES = {"int": "Int", "bool": "Bool"}
LEAN_TYPES = {
    "Uint": "Uint", "U64": "U64", "U256": "U256", "None": "Unit",
    **BUILTIN_TYPES,
}

# Exception classes with a constructor in the runtime's `Exc`. Keep the two
# in step: the Lean build fails on a name the runtime does not have.
EXCEPTIONS = (
    "AssertionError", "OverflowError", "ZeroDivisionError", "OutOfGasError",
)

LEAN_KEYWORDS = {
    "at", "by", "calc", "class", "def", "do", "else", "end", "example",
    "export", "fun", "have", "if", "import", "in", "instance", "let",
    "match", "mutual", "namespace", "open", "section", "show", "structure",
    "then", "theorem", "universe", "variable", "where", "with", "from",
}


class Unsupported(Exception):
    """A Python construct the translator does not handle."""


def ident(name: str) -> str:
    """Return `name` as a Lean identifier, escaping keywords."""
    return f"«{name}»" if name in LEAN_KEYWORDS else name


@dataclass
class Module:
    """One parsed EELS module."""

    name: str
    path: Path
    tree: ast.Module
    is_package: bool
    imports: dict[str, str] = field(default_factory=dict)
    defs: dict[str, ast.stmt] = field(default_factory=dict)

    def where(self, node: ast.AST) -> str:
        """Return `file:line` for `node`."""
        return f"{self.path}:{getattr(node, 'lineno', '?')}"


@dataclass
class Item:
    """One Lean declaration to emit."""

    fq: str
    module: str
    lean: str
    deps: set[str]


@dataclass
class Constant:
    """A translated constant, and whether reading it can raise."""

    lean_type: str
    py_type: str
    failable: bool


@dataclass
class Signature:
    """
    Parameter and return types of a translated function.

    `state` names the dataclass parameter the function changes, if any.
    """

    params: list[tuple[str, str]]
    returns: str
    state: str | None = None


class Project:
    """All modules under the source roots, loaded on demand."""

    def __init__(self, *srcs: Path) -> None:
        self.srcs = srcs
        self.modules: dict[str, Module] = {}

    def module(self, name: str) -> Module | None:
        """Load the module called `name`, or return `None`."""
        if name in self.modules:
            return self.modules[name]
        for src in self.srcs:
            base = src.joinpath(*name.split("."))
            for path, is_package in (
                (base.with_suffix(".py"), False),
                (base / "__init__.py", True),
            ):
                if path.is_file():
                    tree = ast.parse(path.read_text(), filename=str(path))
                    module = Module(name, path, tree, is_package)
                    self._index(module)
                    self.modules[name] = module
                    return module
        return None

    def _index(self, module: Module) -> None:
        package = (
            module.name
            if module.is_package
            else module.name.rpartition(".")[0]
        )
        for stmt in self._top_level(module.tree.body):
            if isinstance(stmt, ast.ImportFrom):
                if stmt.level:
                    parts = package.split(".")
                    parts = parts[: len(parts) - (stmt.level - 1)]
                    origin = ".".join(parts + ([stmt.module] if stmt.module else []))
                else:
                    origin = stmt.module or ""
                for alias in stmt.names:
                    module.imports[alias.asname or alias.name] = (
                        f"{origin}.{alias.name}"
                    )
            elif isinstance(stmt, ast.Import):
                for alias in stmt.names:
                    module.imports[alias.asname or alias.name] = alias.name
            elif isinstance(stmt, (ast.FunctionDef, ast.ClassDef)):
                module.defs[stmt.name] = stmt
            elif isinstance(stmt, ast.Assign):
                for target in stmt.targets:
                    if isinstance(target, ast.Name):
                        module.defs[target.id] = stmt
            elif isinstance(stmt, ast.AnnAssign):
                if isinstance(stmt.target, ast.Name):
                    module.defs[stmt.target.id] = stmt

    @staticmethod
    def _top_level(body: list[ast.stmt]) -> list[ast.stmt]:
        """Flatten `if TYPE_CHECKING:` blocks into the top level."""
        out: list[ast.stmt] = []
        for stmt in body:
            if (
                isinstance(stmt, ast.If)
                and isinstance(stmt.test, ast.Name)
                and stmt.test.id == "TYPE_CHECKING"
            ):
                out.extend(stmt.body)
            else:
                out.append(stmt)
        return out

    def resolve(self, fq: str) -> tuple[Module, list[str]] | None:
        """
        Find the module that defines `fq`, following re-exports.

        Return the module and the remaining attribute path.
        """
        parts = fq.split(".")
        for cut in range(len(parts) - 1, 0, -1):
            module = self.module(".".join(parts[:cut]))
            if module is None:
                continue
            rest = parts[cut:]
            if rest[0] in module.defs:
                return module, rest
            if rest[0] in module.imports:
                target = module.imports[rest[0]]
                return self.resolve(".".join([target, *rest[1:]]))
            return None
        return None


class Translator:
    """Translate a closure of EELS definitions into Lean modules."""

    def __init__(self, project: Project) -> None:
        self.project = project
        self.items: dict[str, Item] = {}
        self.constants: dict[str, Constant] = {}
        self.signatures: dict[str, Signature] = {}
        self.aliases: dict[str, str] = {}
        self.records: dict[str, list[tuple[str, str]]] = {}
        self.in_progress: set[str] = set()

    # Names and types.

    def global_fq(self, module: Module, name: str) -> str | None:
        """Return the fully qualified name `name` refers to in `module`."""
        if name in module.defs:
            return f"{module.name}.{name}"
        if name in module.imports:
            return module.imports[name]
        return None

    def py_type(self, module: Module, node: ast.expr | None) -> str:
        """Translate a type annotation into a Python type key."""
        if node is None:
            raise Unsupported(f"{module.where(module.tree)}: missing annotation")
        if (
            isinstance(node, ast.Subscript)
            and isinstance(node.value, ast.Name)
            and node.value.id == "Final"
        ):
            return self.py_type(module, node.slice)
        if isinstance(node, ast.Name):
            if node.id in BUILTIN_TYPES:
                return node.id
            fq = self.global_fq(module, node.id)
            if fq in NUMERIC:
                return NUMERIC[fq]
            if fq is not None:
                self.require(fq)
                fq = self.canonical(fq)
                if fq in self.aliases or fq in self.records:
                    return fq
        raise Unsupported(
            f"{module.where(node)}: type annotation {ast.unparse(node)}"
        )

    def base(self, py_type: str) -> str:
        """Follow `NewType` aliases down to a runtime type."""
        while py_type in self.aliases:
            py_type = self.aliases[py_type]
        return py_type

    def lean_type(self, py_type: str) -> str:
        """Return the Lean name of a Python type key."""
        if py_type in LEAN_TYPES:
            return LEAN_TYPES[py_type]
        return py_type

    def canonical(self, fq: str) -> str:
        """Return the defining path of `fq`, following re-exports."""
        found = self.project.resolve(fq)
        if found is None:
            return fq
        module, rest = found
        return ".".join([module.name, *rest])

    # The closure.

    def require(self, fq: str) -> None:
        """Translate the definition `fq` and everything it needs."""
        if fq in self.items or fq in self.in_progress or fq in NUMERIC:
            return
        found = self.project.resolve(fq)
        if found is None:
            raise Unsupported(f"cannot find the definition of {fq}")
        module, rest = found
        fq = ".".join([module.name, *rest])
        if fq in self.items or fq in self.in_progress:
            return
        self.in_progress.add(fq)
        try:
            node = module.defs[rest[0]]
            if len(rest) == 2 and isinstance(node, ast.ClassDef):
                item = self.class_constant(module, node, rest[1])
            elif len(rest) == 1 and isinstance(node, ast.FunctionDef):
                item = FunctionTranslator(self, module, node).translate()
            elif len(rest) == 1 and isinstance(node, ast.ClassDef):
                item = self.record(module, node)
            elif len(rest) == 1 and isinstance(node, ast.Assign):
                item = self.module_assign(module, node, rest[0])
            else:
                raise Unsupported(f"{module.where(node)}: definition of {fq}")
        finally:
            self.in_progress.discard(fq)
        self.items[fq] = item

    def module_assign(self, module: Module, node: ast.Assign, name: str) -> Item:
        """Translate `X = NewType("X", Base)`."""
        call = node.value
        if (
            isinstance(call, ast.Call)
            and isinstance(call.func, ast.Name)
            and self.global_fq(module, call.func.id) == "typing.NewType"
            and len(call.args) == 2
        ):
            base = self.py_type(module, call.args[1])
            fq = f"{module.name}.{name}"
            self.aliases[fq] = base
            lean = f"/-- `{name} = NewType(\"{name}\", ...)` -/\nabbrev {ident(name)} := {self.lean_type(base)}\n"
            return Item(fq, module.name, lean, self.type_deps(base))
        raise Unsupported(f"{module.where(node)}: module-level {name}")

    def type_deps(self, py_type: str) -> set[str]:
        """Return the declarations a type key depends on."""
        if py_type in self.aliases or py_type in self.records:
            return {py_type}
        return set()

    def record(self, module: Module, cls: ast.ClassDef) -> Item:
        """Translate a `@dataclass` of annotated fields, with their defaults."""
        decorators = [
            self.global_fq(module, d.id)
            for d in cls.decorator_list
            if isinstance(d, ast.Name)
        ]
        if len(decorators) != len(cls.decorator_list) or (
            "dataclasses.dataclass" not in decorators
        ) or not set(decorators) <= {"dataclasses.dataclass", "typing.final"}:
            raise Unsupported(f"{module.where(cls)}: class {cls.name}")
        if cls.bases or cls.keywords:
            raise Unsupported(f"{module.where(cls)}: base classes of {cls.name}")
        fields: list[tuple[str, str]] = []
        rendered = ""
        expr = ExprTranslator(self, module, {})
        for stmt in cls.body:
            if (
                isinstance(stmt, ast.Expr)
                and isinstance(stmt.value, ast.Constant)
                and isinstance(stmt.value.value, str)
            ):
                # The docstring of the class or of the field above.
                continue
            if not (
                isinstance(stmt, ast.AnnAssign)
                and isinstance(stmt.target, ast.Name)
            ):
                raise Unsupported(f"{module.where(stmt)}: body of {cls.name}")
            name = stmt.target.id
            py_type = self.py_type(module, stmt.annotation)
            default = ""
            if stmt.value is not None:
                if self.base(expr.type_of(stmt.value)) != self.base(py_type):
                    raise Unsupported(f"{module.where(stmt)}: default of {name}")
                value = expr.expr(stmt.value)
                if "←" in value:
                    raise Unsupported(
                        f"{module.where(stmt)}: raising default of {name}"
                    )
                default = f" := {value}"
            fields.append((name, py_type))
            rendered += f"  {ident(name)} : {self.lean_type(py_type)}{default}\n"
        fq = f"{module.name}.{cls.name}"
        self.records[fq] = fields
        lean = f"/-- `@dataclass {cls.name}` -/\nstructure {ident(cls.name)} where\n{rendered}"
        deps = set(expr.deps)
        for _, t in fields:
            deps |= self.type_deps(t)
        return Item(fq, module.name, lean, deps)

    def class_constant(self, module: Module, cls: ast.ClassDef, name: str) -> Item:
        """Translate one annotated constant in a constants class."""
        for stmt in cls.body:
            if (
                isinstance(stmt, ast.AnnAssign)
                and isinstance(stmt.target, ast.Name)
                and stmt.target.id == name
                and stmt.value is not None
            ):
                break
        else:
            raise Unsupported(f"{module.where(cls)}: {cls.name}.{name}")
        fq = f"{module.name}.{cls.name}.{name}"
        py_type = self.py_type(module, stmt.annotation)
        scope = ClassScope(cls, {
            s.target.id
            for s in cls.body
            if isinstance(s, ast.AnnAssign) and isinstance(s.target, ast.Name)
        })
        expr = ExprTranslator(self, module, {}, scope)
        value = expr.expr(stmt.value)
        lean_type = self.lean_type(py_type)
        failable = "←" in value
        short = f"{cls.name}.{name}"
        if failable:
            lean = (
                f"/-- `{short}` -/\n"
                f"def {cls.name}.{ident(name)} : Except Exc {lean_type} := do\n"
                f"  return {value}\n"
            )
        else:
            lean = (
                f"/-- `{short}` -/\n"
                f"def {cls.name}.{ident(name)} : {lean_type} :=\n  {value}\n"
            )
        self.constants[fq] = Constant(lean_type, py_type, failable)
        return Item(fq, module.name, lean, expr.deps | self.type_deps(py_type))


@dataclass
class ClassScope:
    """Names visible inside a constants class body."""

    cls: ast.ClassDef
    names: set[str]


class ExprTranslator:
    """Translate expressions inside one function or constant."""

    def __init__(
        self,
        translator: Translator,
        module: Module,
        locals_: dict[str, str],
        scope: ClassScope | None = None,
    ) -> None:
        self.t = translator
        self.module = module
        self.locals = locals_
        self.scope = scope
        self.state: str | None = None
        self.deps: set[str] = set()

    def fail(self, node: ast.AST, what: str) -> Unsupported:
        return Unsupported(f"{self.module.where(node)}: {what}: {ast.unparse(node)}")

    # Types of expressions.

    def type_of(self, node: ast.expr) -> str:
        """Return the Python type key of `node`."""
        if isinstance(node, ast.Constant):
            if isinstance(node.value, bool):
                return "bool"
            if isinstance(node.value, int):
                return "int"
        if isinstance(node, ast.Name):
            if node.id in self.locals:
                return self.locals[node.id]
            fq = self.ref_fq(node)
            if fq is not None and fq not in NUMERIC:
                self.t.require(fq)
            if fq in self.t.constants:
                return self.t.constants[fq].py_type
        if isinstance(node, ast.Attribute):
            field = self.record_field(node)
            if field is not None:
                return field
            fq = self.attr_fq(node)
            if fq is not None:
                self.t.require(fq)
            if fq in self.t.constants:
                return self.t.constants[fq].py_type
        if isinstance(node, ast.BinOp):
            left = self.type_of(node.left)
            right = self.type_of(node.right)
            if self.t.base(left) != self.t.base(right):
                raise self.fail(node, f"mixed operand types {left} and {right}")
            return left
        if isinstance(node, (ast.Compare, ast.BoolOp)):
            return "bool"
        if isinstance(node, ast.UnaryOp):
            return "bool" if isinstance(node.op, ast.Not) else self.type_of(node.operand)
        if isinstance(node, ast.IfExp):
            return self.type_of(node.body)
        if isinstance(node, ast.Call):
            return self.call_type(node)
        raise self.fail(node, "cannot type")

    def call_type(self, node: ast.Call) -> str:
        """Return the Python type key of a call's result."""
        if isinstance(node.func, ast.Name):
            name = node.func.id
            if name == "int":
                return "int"
            if name in ("min", "max"):
                return self.type_of(node.args[0])
            fq = self.ref_fq(node.func)
            if fq in NUMERIC:
                return NUMERIC[fq]
            if fq is not None:
                self.t.require(fq)
                fq = self.canonical(fq)
                if fq in self.t.aliases or fq in self.t.records:
                    return fq
                if fq in self.t.signatures:
                    return self.t.signatures[fq].returns
        raise self.fail(node, "cannot type call")

    def record_field(self, node: ast.Attribute) -> str | None:
        """Return the type of `local.field` for a local dataclass value."""
        if isinstance(node.value, ast.Name) and node.value.id in self.locals:
            kind = self.locals[node.value.id]
            for name, py_type in self.t.records.get(kind, []):
                if name == node.attr:
                    return py_type
            raise self.fail(node, "attribute of a local")
        return None

    # Name resolution.

    def canonical(self, fq: str) -> str:
        found = self.t.project.resolve(fq)
        if found is None:
            return fq
        module, rest = found
        return ".".join([module.name, *rest])

    def ref_fq(self, node: ast.Name) -> str | None:
        if self.scope is not None and node.id in self.scope.names:
            return f"{self.module.name}.{self.scope.cls.name}.{node.id}"
        fq = self.t.global_fq(self.module, node.id)
        if fq in NUMERIC or fq is None:
            return fq
        return self.canonical(fq)

    def attr_fq(self, node: ast.Attribute) -> str | None:
        if isinstance(node.value, ast.Name) and node.value.id not in self.locals:
            base = self.t.global_fq(self.module, node.value.id)
            if base is not None:
                return self.canonical(f"{base}.{node.attr}")
        return None

    def lean_ref(self, fq: str) -> str:
        """Return a Lean reference to the declaration `fq`."""
        self.t.require(fq)
        self.deps.add(fq)
        return ".".join(ident(p) for p in fq.split("."))

    # Expressions.

    def expr(self, node: ast.expr) -> str:
        """Return Lean for `node`, lifting raising calls with `←`."""
        if isinstance(node, ast.Constant):
            if isinstance(node.value, bool):
                return "true" if node.value else "false"
            if isinstance(node.value, int) and node.value >= 0:
                return str(node.value)
            raise self.fail(node, "constant")
        if isinstance(node, ast.Name):
            if node.id == self.state:
                # Only its fields are read: a second name for the dataclass
                # would not see later writes.
                raise self.fail(node, "the changed dataclass used as a value")
            if node.id in self.locals:
                return ident(node.id)
            fq = self.ref_fq(node)
            if fq is not None:
                return self.constant_ref(node, fq)
            raise self.fail(node, "unknown name")
        if isinstance(node, ast.Attribute):
            if self.record_field(node) is not None:
                return f"{ident(node.value.id)}.{ident(node.attr)}"
            fq = self.attr_fq(node)
            if fq is not None:
                return self.constant_ref(node, fq)
            raise self.fail(node, "attribute")
        if isinstance(node, ast.BinOp):
            return self.binop(node)
        if isinstance(node, ast.Compare):
            return self.compare(node)
        if isinstance(node, ast.BoolOp):
            op = " && " if isinstance(node.op, ast.And) else " || "
            parts = [self.expr(v) for v in node.values]
            if any("←" in p for p in parts[1:]):
                raise self.fail(node, "raising operand after a short circuit")
            return "(" + op.join(parts) + ")"
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
            return f"(!{self.expr(node.operand)})"
        if isinstance(node, ast.IfExp):
            body, orelse = self.expr(node.body), self.expr(node.orelse)
            if "←" in body or "←" in orelse:
                raise self.fail(node, "raising branch in a conditional expression")
            return f"(if {self.expr(node.test)} then {body} else {orelse})"
        if isinstance(node, ast.Call):
            return self.call(node)
        raise self.fail(node, "expression")

    def constant_ref(self, node: ast.expr, fq: str) -> str:
        ref = self.lean_ref(fq)
        if fq in self.t.constants:
            return f"(← {ref})" if self.t.constants[fq].failable else ref
        raise self.fail(node, f"reference to {fq}")

    def binop(self, node: ast.BinOp) -> str:
        kind = self.t.base(self.type_of(node))
        left, right = self.expr(node.left), self.expr(node.right)
        op = type(node.op)
        if kind == "Uint":
            pure = {ast.Add: "+", ast.Mult: "*", ast.Pow: "^"}
            if op in pure:
                return f"({left} {pure[op]} {right})"
            if op in (ast.FloorDiv, ast.Mod):
                symbol = "/" if op is ast.FloorDiv else "%"
                if self.nonzero_literal(node.right):
                    return f"({left} {symbol} {right})"
                name = "floorDiv" if op is ast.FloorDiv else "mod"
                return f"(← {RUNTIME}.Uint.{name} {left} {right})"
            if op is ast.Sub:
                return f"(← {RUNTIME}.Uint.sub {left} {right})"
        if kind in FIXED_BITS:
            names = {
                ast.Add: "add", ast.Sub: "sub", ast.Mult: "mul",
                ast.FloorDiv: "floorDiv", ast.Mod: "mod", ast.Pow: "pow",
            }
            if op in names:
                return f"(← {RUNTIME}.Fixed.{names[op]} {left} {right})"
        if kind == "int":
            pure = {ast.Add: "+", ast.Sub: "-", ast.Mult: "*"}
            if op in pure:
                return f"({left} {pure[op]} {right})"
            if op in (ast.FloorDiv, ast.Mod):
                name = "floorDiv" if op is ast.FloorDiv else "mod"
                return f"(← {RUNTIME}.Int.{name} {left} {right})"
        raise self.fail(node, f"operator {op.__name__} on {kind}")

    @staticmethod
    def nonzero_literal(node: ast.expr) -> bool:
        """Return whether `node` is `Uint(n)` or `n` for a literal `n > 0`."""
        if (
            isinstance(node, ast.Call)
            and isinstance(node.func, ast.Name)
            and len(node.args) == 1
        ):
            node = node.args[0]
        return (
            isinstance(node, ast.Constant)
            and type(node.value) is int
            and node.value > 0
        )

    def compare(self, node: ast.Compare) -> str:
        if len(node.ops) != 1:
            raise self.fail(node, "chained comparison")
        symbols = {
            ast.Eq: "=", ast.NotEq: "≠", ast.Lt: "<",
            ast.LtE: "≤", ast.Gt: ">", ast.GtE: "≥",
        }
        op = type(node.ops[0])
        if op not in symbols:
            raise self.fail(node, "comparison")
        lhs, rhs = node.left, node.comparators[0]
        left = self.t.base(self.type_of(lhs))
        right = self.t.base(self.type_of(rhs))
        rendered_l, rendered_r = self.expr(lhs), self.expr(rhs)
        if left != right:
            # `Unsigned.__eq__` and friends compare with an `int` numerically.
            literal = lambda n: isinstance(n, ast.Constant) and type(n.value) is int
            numeric = ("Uint", *FIXED_BITS)
            if literal(rhs) and left in numeric and op in (ast.Eq, ast.NotEq):
                rendered_l = f"{rendered_l}.val" if left in FIXED_BITS else rendered_l
            elif literal(lhs) and right in numeric and op in (ast.Eq, ast.NotEq):
                rendered_r = f"{rendered_r}.val" if right in FIXED_BITS else rendered_r
            else:
                raise self.fail(node, f"comparison of {left} and {right}")
        elif left in FIXED_BITS:
            rendered_l, rendered_r = f"{rendered_l}.val", f"{rendered_r}.val"
        return f"(decide ({rendered_l} {symbols[op]} {rendered_r}))"

    def call(self, node: ast.Call) -> str:
        if node.keywords or not isinstance(node.func, ast.Name):
            raise self.fail(node, "call")
        name = node.func.id
        args = node.args
        if name in ("min", "max") and len(args) == 2:
            return f"({name} {self.expr(args[0])} {self.expr(args[1])})"
        if name == "int" and len(args) == 1:
            kind = self.t.base(self.type_of(args[0]))
            inner = self.expr(args[0])
            if kind == "Uint":
                return f"(Int.ofNat {inner})"
            if kind in FIXED_BITS:
                return f"(Int.ofNat {inner}.val)"
            if kind == "int":
                return inner
            raise self.fail(node, "int() argument")
        fq = self.ref_fq(node.func)
        if fq in NUMERIC and len(args) == 1:
            return self.construct(node, NUMERIC[fq], args[0])
        if fq is None:
            raise self.fail(node, "unknown function")
        self.t.require(fq)
        fq = self.canonical(fq)
        if fq in self.t.aliases and len(args) == 1:
            target = self.t.base(fq)
            if self.t.base(self.type_of(args[0])) != target:
                raise self.fail(node, f"{fq} of a non-{target}")
            self.deps.add(fq)
            return self.expr(args[0])
        if fq in self.t.records:
            fields = self.t.records[fq]
            if len(args) != len(fields):
                raise self.fail(node, f"{fq} needs {len(fields)} arguments")
            for arg, (_, py_type) in zip(args, fields):
                if self.t.base(self.type_of(arg)) != self.t.base(py_type):
                    raise self.fail(node, f"argument type for {fq}")
            ref = self.lean_ref(fq)
            rendered = " ".join(self.expr(a) for a in args)
            return f"({ref}.mk {rendered})"
        if fq in self.t.signatures:
            if self.t.signatures[fq].state is not None:
                raise self.fail(node, "call to a function that changes its argument")
            ref = self.lean_ref(fq)
            rendered = " ".join(self.expr(a) for a in args)
            return f"(← {ref} {rendered})"
        raise self.fail(node, "call target")

    def construct(self, node: ast.Call, kind: str, arg: ast.expr) -> str:
        """Translate `Uint(x)`, `U64(x)` or `U256(x)`."""
        source = self.t.base(self.type_of(arg))
        inner = self.expr(arg)
        if kind == "Uint":
            if isinstance(arg, ast.Constant) or source == "Uint":
                return f"({inner} : Uint)"
            if source in FIXED_BITS:
                return f"{inner}.val"
            if source == "int":
                return f"(← {RUNTIME}.Uint.ofInt {inner})"
        bits = FIXED_BITS[kind] if kind in FIXED_BITS else None
        if bits is not None:
            if isinstance(arg, ast.Constant) or source == "Uint":
                return f"(← {RUNTIME}.Fixed.ofNat {bits} {inner})"
            if source in FIXED_BITS:
                return f"(← {RUNTIME}.Fixed.ofNat {bits} {inner}.val)"
            if source == "int":
                return f"(← {RUNTIME}.Fixed.ofInt {bits} {inner})"
        raise self.fail(node, f"{kind}() of {source}")


class FunctionTranslator:
    """Translate one EELS function into a Lean `def`."""

    def __init__(self, t: Translator, module: Module, node: ast.FunctionDef) -> None:
        self.t = t
        self.module = module
        self.node = node
        self.locals: dict[str, str] = {}
        self.mutable: set[str] = set()
        self.declared: set[str] = set()
        self.params: set[str] = set()
        self.shadowed: set[str] = set()
        self.expr = ExprTranslator(t, module, self.locals)
        # The dataclass parameter the function changes, if any.
        self.state: str | None = None
        # Writes to the state on the path so far, and per open block the
        # count at which the block last read the state into a local.
        self.writes = 0
        self.snapshots: list[int | None] = []
        # Open blocks, innermost last, and the names local to each.
        self.blocks: list[list[ast.stmt]] = []
        self.block_locals: list[set[str]] = []

    def fail(self, node: ast.AST, what: str) -> Unsupported:
        return Unsupported(f"{self.module.where(node)}: {what}")

    def translate(self) -> Item:
        node = self.node
        fq = f"{self.module.name}.{node.name}"
        if node.decorator_list or node.args.vararg or node.args.kwarg:
            raise self.fail(node, f"signature of {node.name}")
        if node.args.kwonlyargs or node.args.posonlyargs:
            raise self.fail(node, f"signature of {node.name}")
        params = []
        for arg in node.args.args:
            py_type = self.t.py_type(self.module, arg.annotation)
            params.append((arg.arg, py_type))
            self.locals[arg.arg] = py_type
            self.declared.add(arg.arg)
            self.params.add(arg.arg)
        defaults: dict[str, str] = {}
        firsts = len(params) - len(node.args.defaults)
        for (name, py_type), value in zip(params[firsts:], node.args.defaults):
            if self.t.base(self.expr.type_of(value)) != self.t.base(py_type):
                raise self.fail(value, f"default of {name}")
            rendered_default = self.expr.expr(value)
            if "←" in rendered_default:
                raise self.fail(value, f"raising default of {name}")
            defaults[name] = rendered_default
        if isinstance(node.returns, ast.Constant) and node.returns.value is None:
            returns = "None"
        else:
            returns = self.t.py_type(self.module, node.returns)
        self.state = self.expr.state = self.find_state(params)
        self.t.signatures[fq] = Signature(params, returns, self.state)
        self.mutable = self.find_mutable(node.body)
        prologue = "".join(
            f"  let mut {ident(n)} := {ident(n)}\n"
            for n, _ in params
            if n in self.mutable
        )
        body = prologue + self.block(self.strip_docstring(node.body), 1)
        rendered = "".join(
            f" ({ident(name)} : {self.t.lean_type(t)}"
            + (f" := {defaults[name]})" if name in defaults else ")")
            for name, t in params
            if name != self.state
        )
        if self.state is None:
            monad = "Except Exc"
            doc = f"/-- `{node.name}` from `{self.module.name}` -/\n"
        else:
            monad = f"EStateM Exc {self.t.lean_type(self.locals[self.state])}"
            doc = (
                f"/-- `{node.name}` from `{self.module.name}`. "
                f"The state is `{self.state}`. -/\n"
            )
        lean = (
            f"{doc}def {ident(node.name)}{rendered} : "
            f"{monad} {self.t.lean_type(returns)} := do\n{body}"
        )
        deps = set(self.expr.deps)
        for _, py_type in params:
            deps |= self.t.type_deps(py_type)
        deps |= self.t.type_deps(returns)
        return Item(fq, self.module.name, lean, deps)

    @staticmethod
    def strip_docstring(body: list[ast.stmt]) -> list[ast.stmt]:
        if (
            body
            and isinstance(body[0], ast.Expr)
            and isinstance(body[0].value, ast.Constant)
            and isinstance(body[0].value.value, str)
        ):
            return body[1:]
        return body

    def find_state(self, params: list[tuple[str, str]]) -> str | None:
        """Return the dataclass parameter whose fields the function assigns."""
        records = {name for name, t in params if t in self.t.records}
        changed = sorted({
            n.value.id
            for n in ast.walk(self.node)
            if isinstance(n, ast.Attribute)
            and isinstance(n.ctx, ast.Store)
            and isinstance(n.value, ast.Name)
            and n.value.id in records
        })
        if len(changed) > 1:
            raise self.fail(
                self.node, f"changes more than one dataclass: {', '.join(changed)}"
            )
        return changed[0] if changed else None

    def reads_state(self, node: ast.stmt) -> bool:
        """Return whether `node` itself, not a block inside it, names the state."""
        root = node.test if isinstance(node, ast.If) else node
        return any(
            isinstance(n, ast.Name) and n.id == self.state for n in ast.walk(root)
        )

    def find_mutable(self, body: list[ast.stmt]) -> set[str]:
        """Return names assigned more than once or inside nested blocks."""
        counts: dict[str, int] = {}
        nested: set[str] = set()

        def visit(stmts: list[ast.stmt], depth: int) -> None:
            for stmt in stmts:
                for name in self.assigned(stmt):
                    counts[name] = counts.get(name, 0) + 1
                    if depth > 0:
                        nested.add(name)
                for child in ("body", "orelse"):
                    if hasattr(stmt, child) and not isinstance(stmt, ast.FunctionDef):
                        visit(getattr(stmt, child), depth + 1)

        visit(body, 0)
        return {n for n, c in counts.items() if c > 1} | nested

    @staticmethod
    def assigned(stmt: ast.stmt) -> list[str]:
        if isinstance(stmt, ast.Assign):
            return [t.id for t in stmt.targets if isinstance(t, ast.Name)]
        if isinstance(stmt, (ast.AnnAssign, ast.AugAssign)) and isinstance(
            stmt.target, ast.Name
        ):
            return [stmt.target.id]
        return []

    def block(self, stmts: list[ast.stmt], depth: int) -> str:
        if not stmts:
            return "  " * depth + "pure ()\n"
        self.blocks.append(stmts)
        self.block_locals.append(set())
        self.snapshots.append(None)
        try:
            return "".join(self.stmt(s, depth) for s in stmts)
        finally:
            self.snapshots.pop()
            self.blocks.pop()
            for name in self.block_locals.pop():
                del self.locals[name]
                self.declared.discard(name)

    def read(self, depth: int) -> str:
        """
        Return the line that reads the state into a local of its own name.

        Field reads then look as they do in Python. The line is empty when
        a read still in scope is current: nothing was written since.
        """
        if self.writes in self.snapshots:
            return ""
        self.snapshots[-1] = self.writes
        return f"{'  ' * depth}let {ident(self.state)} ← get\n"

    def stmt(self, node: ast.stmt, depth: int) -> str:
        """Translate one statement, reading the state first if it names it."""
        target = getattr(node, "target", None) or getattr(node, "targets", [None])[0]
        if (
            self.state is None
            or isinstance(target, ast.Attribute)
            or not self.reads_state(node)
        ):
            return self.statement(node, depth)
        return self.read(depth) + self.statement(node, depth)

    def statement(self, node: ast.stmt, depth: int) -> str:
        pad = "  " * depth
        if isinstance(node, ast.Pass):
            return ""
        if isinstance(node, ast.Return):
            if node.value is None:
                return f"{pad}return ()\n"
            return f"{pad}return {self.expr.expr(node.value)}\n"
        if isinstance(node, (ast.Assign, ast.AnnAssign)):
            targets = node.targets if isinstance(node, ast.Assign) else [node.target]
            if len(targets) != 1:
                raise self.fail(node, "assignment target")
            if node.value is None:
                raise self.fail(node, "annotation without a value")
            if isinstance(targets[0], ast.Attribute):
                return self.store(node, targets[0], node.value, depth)
            if not isinstance(targets[0], ast.Name):
                raise self.fail(node, "assignment target")
            return self.assign(node, targets[0].id, node.value, depth)
        if isinstance(node, ast.AugAssign):
            target = node.target
            if isinstance(target, ast.Attribute):
                left: ast.expr = ast.Attribute(target.value, target.attr, ast.Load())
            elif isinstance(target, ast.Name):
                left = ast.Name(target.id, ast.Load())
            else:
                raise self.fail(node, "augmented assignment target")
            value = ast.BinOp(left=left, op=node.op, right=node.value)
            ast.copy_location(value, node)
            ast.fix_missing_locations(value)
            if isinstance(target, ast.Attribute):
                return self.store(node, target, value, depth)
            return self.assign(node, target.id, value, depth)
        if isinstance(node, ast.If):
            test = self.expr.expr(node.test)
            before = self.writes
            out = f"{pad}if {test} then\n{self.block(node.body, depth + 1)}"
            if node.orelse:
                # The other branch starts from the state the test saw.
                after, self.writes = self.writes, before
                out += f"{pad}else\n{self.block(node.orelse, depth + 1)}"
                self.writes = max(after, self.writes)
            return out
        if isinstance(node, ast.Raise):
            return f"{pad}throw Exc.{self.exception_name(node)}\n"
        if isinstance(node, ast.Assert):
            test = self.expr.expr(node.test)
            return f"{pad}if !{test} then\n{pad}  throw Exc.AssertionError\n"
        raise self.fail(node, f"statement {type(node).__name__}")

    def store(
        self, node: ast.stmt, target: ast.Attribute, value: ast.expr, depth: int
    ) -> str:
        """
        Translate `state.field = value`.

        A value that cannot raise is computed from the state as it is at the
        write. One that can is computed first, from a read of the state, so
        that a raise leaves the state alone.
        """
        if not (isinstance(target.value, ast.Name) and target.value.id == self.state):
            raise self.fail(node, "assignment target")
        field = self.expr.record_field(target)
        if self.t.base(field) != self.t.base(self.expr.type_of(value)):
            raise self.fail(node, f"{target.attr} changes type")
        rendered = self.expr.expr(value)
        pad = "  " * depth
        state = ident(self.state)
        update = f"{{ {state} with {ident(target.attr)} := {rendered} }}"
        if "←" in rendered:
            out = f"{self.read(depth)}{pad}set {update}\n"
        else:
            out = f"{pad}modify fun {state} => {update}\n"
        self.writes += 1
        return out

    def names(self, stmts: list[ast.stmt], name: str) -> int:
        """Count the places in `stmts` that read or assign `name`."""
        return sum(
            isinstance(n, ast.Name) and n.id == name
            for stmt in stmts
            for n in ast.walk(stmt)
        )

    def assign(self, node: ast.stmt, name: str, value: ast.expr, depth: int) -> str:
        pad = "  " * depth
        if name == self.state:
            raise self.fail(node, f"reassignment of {name}")
        py_type = self.expr.type_of(value)
        if name in self.locals and self.t.base(self.locals[name]) != self.t.base(py_type):
            raise self.fail(node, f"{name} changes type")
        rendered = self.expr.expr(value)
        if name in self.declared:
            if name in self.mutable:
                return f"{pad}{ident(name)} := {rendered}\n"
            if name in self.params and name not in self.shadowed and depth == 1:
                # A parameter assigned once at the top level: shadow it.
                self.shadowed.add(name)
                return f"{pad}let {ident(name)} := {rendered}\n"
            raise self.fail(node, f"reassignment of {name}")
        if depth > 1:
            # A name that lives and dies inside this block is a local of it.
            body = self.node.body
            if self.names(self.blocks[-1], name) != self.names(body, name):
                raise self.fail(node, f"{name} first assigned inside a block")
            self.block_locals[-1].add(name)
            again = sum(name in self.assigned(n) for n in ast.walk(self.node)) > 1
        else:
            again = name in self.mutable
        self.locals[name] = py_type
        self.declared.add(name)
        keyword = "let mut" if again else "let"
        return f"{pad}{keyword} {ident(name)} := {rendered}\n"

    def exception_name(self, node: ast.Raise) -> str:
        exc = node.exc
        if isinstance(exc, ast.Call):
            exc = exc.func
        if not isinstance(exc, ast.Name):
            raise self.fail(node, "raise")
        if exc.id not in EXCEPTIONS:
            raise self.fail(node, f"exception class {exc.id} is not in {RUNTIME}.Exc")
        return exc.id


def order(items: dict[str, Item]) -> list[Item]:
    """Order items so every declaration follows its dependencies."""
    done: set[str] = set()
    out: list[Item] = []

    def visit(fq: str, stack: tuple[str, ...]) -> None:
        if fq in done or fq not in items:
            return
        if fq in stack:
            raise Unsupported(f"recursive definitions: {' -> '.join(stack + (fq,))}")
        for dep in sorted(items[fq].deps):
            visit(dep, stack + (fq,))
        done.add(fq)
        out.append(items[fq])

    for fq in sorted(items):
        visit(fq, ())
    return out


def lean_module_name(module: str, root: str = LEAN_ROOT) -> str:
    return f"{root}.{module}"


def render(
    items: dict[str, Item], pin: str, root: str = LEAN_ROOT
) -> dict[str, str]:
    """Return Lean source per EELS module."""
    by_module: dict[str, list[Item]] = {}
    for item in order(items):
        by_module.setdefault(item.module, []).append(item)
    out: dict[str, str] = {}
    for module, module_items in by_module.items():
        imports = {
            items[dep].module
            for item in module_items
            for dep in item.deps
            if dep in items and items[dep].module != module
        }
        lines = [f"import {RUNTIME}"]
        lines += [f"import {lean_module_name(m, root)}" for m in sorted(imports)]
        header = (
            f"/-!\nGenerated by eels2lean from `{module}` at EELS {pin}.\n"
            f"Do not edit.\n-/\n"
        )
        body = "\n".join(i.lean for i in module_items)
        out[module] = (
            "\n".join(lines)
            + "\n\n"
            + header
            + f"\nnamespace {module}\nopen {RUNTIME}\n\n"
            + body
            + f"\nend {module}\n"
        )
    return out
