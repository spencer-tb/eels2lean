/-!
# EELS runtime

Hand-written Lean semantics for the Python that eels2lean translates. Every
generated function returns `Except Exc α`, so a Python exception is an
`Except.error` carrying the exception's class.

The arithmetic follows `ethereum_types.numeric`:

- `Uint` is unbounded and never negative. `a - b` below zero raises
  `OverflowError`, and `//` or `%` by zero raises `ZeroDivisionError`.
- `U64` and `U256` are fixed width. Any result out of range raises
  `OverflowError`.
-/

namespace EelsRuntime

/--
A Python exception, identified by its class.

One constructor per class that translated code can raise so far: the
builtins this runtime raises itself, then the classes EELS defines. The
translator refuses a `raise` of any other class.
-/
inductive Exc where
  | AssertionError
  | OverflowError
  | ZeroDivisionError
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The Python name of the exception's class. -/
def Exc.name : Exc → String
  | .AssertionError => "AssertionError"
  | .OverflowError => "OverflowError"
  | .ZeroDivisionError => "ZeroDivisionError"

/-- Raise the Python exception `e`. -/
def raise {α : Type} (e : Exc) : Except Exc α :=
  .error e

/-- `ethereum_types.numeric.Uint`. -/
abbrev Uint := Nat

namespace Uint

/-- `a - b`, raising `OverflowError` below zero. -/
def sub (a b : Uint) : Except Exc Uint :=
  if b ≤ a then .ok (a - b) else raise .OverflowError

/-- `a // b`, raising `ZeroDivisionError` when `b` is zero. -/
def floorDiv (a b : Uint) : Except Exc Uint :=
  if b = 0 then raise .ZeroDivisionError else .ok (a / b)

/-- `a % b`, raising `ZeroDivisionError` when `b` is zero. -/
def mod (a b : Uint) : Except Exc Uint :=
  if b = 0 then raise .ZeroDivisionError else .ok (a % b)

/-- `Uint(i)` for a Python `int`, raising `OverflowError` below zero. -/
def ofInt (i : Int) : Except Exc Uint :=
  if i < 0 then raise .OverflowError else .ok i.toNat

end Uint

/-- `ethereum_types.numeric.FixedUnsigned` with `bits` bits. -/
structure Fixed (bits : Nat) where
  val : Nat
  lt : val < 2 ^ bits
  deriving DecidableEq

/-- `ethereum_types.numeric.U64`. -/
abbrev U64 := Fixed 64

/-- `ethereum_types.numeric.U256`. -/
abbrev U256 := Fixed 256

namespace Fixed

variable {bits : Nat}

/-- Construct from a natural number, raising `OverflowError` out of range. -/
def ofNat (bits : Nat) (n : Nat) : Except Exc (Fixed bits) :=
  if h : n < 2 ^ bits then .ok ⟨n, h⟩ else raise .OverflowError

/-- Construct from a Python `int`, raising `OverflowError` out of range. -/
def ofInt (bits : Nat) (i : Int) : Except Exc (Fixed bits) :=
  if i < 0 then raise .OverflowError else ofNat bits i.toNat

/-- `a + b`. -/
def add (a b : Fixed bits) : Except Exc (Fixed bits) :=
  ofNat bits (a.val + b.val)

/-- `a - b`. -/
def sub (a b : Fixed bits) : Except Exc (Fixed bits) :=
  if b.val ≤ a.val then ofNat bits (a.val - b.val) else raise .OverflowError

/-- `a * b`. -/
def mul (a b : Fixed bits) : Except Exc (Fixed bits) :=
  ofNat bits (a.val * b.val)

/-- `a // b`. -/
def floorDiv (a b : Fixed bits) : Except Exc (Fixed bits) :=
  if b.val = 0 then raise .ZeroDivisionError else ofNat bits (a.val / b.val)

/-- `a % b`. -/
def mod (a b : Fixed bits) : Except Exc (Fixed bits) :=
  if b.val = 0 then raise .ZeroDivisionError else ofNat bits (a.val % b.val)

/-- `a ** b`. -/
def pow (a b : Fixed bits) : Except Exc (Fixed bits) :=
  ofNat bits (a.val ^ b.val)

instance : LT (Fixed bits) := ⟨fun a b => a.val < b.val⟩
instance : LE (Fixed bits) := ⟨fun a b => a.val ≤ b.val⟩
instance (a b : Fixed bits) : Decidable (a < b) := inferInstanceAs (Decidable (a.val < b.val))
instance (a b : Fixed bits) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.val ≤ b.val))
instance : ToString (Fixed bits) := ⟨fun a => toString a.val⟩

end Fixed

namespace Int

/-- Python `a // b` on `int`, flooring, raising `ZeroDivisionError`. -/
def floorDiv (a b : _root_.Int) : Except Exc _root_.Int :=
  if b = 0 then raise .ZeroDivisionError else .ok (_root_.Int.fdiv a b)

/-- Python `a % b` on `int`, flooring, raising `ZeroDivisionError`. -/
def mod (a b : _root_.Int) : Except Exc _root_.Int :=
  if b = 0 then raise .ZeroDivisionError else .ok (_root_.Int.fmod a b)

end Int

end EelsRuntime
