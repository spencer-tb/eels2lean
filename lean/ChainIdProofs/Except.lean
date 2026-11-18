import EelsRuntime

/-!
How `Except` runs a `do` block. All of these hold by definition (`rfl`):
they only let `simp` step through the generated code.
-/

@[simp] theorem ok_bind {ε α β} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

@[simp] theorem error_bind {ε α β} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = Except.error e := rfl

@[simp] theorem throw_eq {ε α} (e : ε) : (throw e : Except ε α) = .error e := rfl

@[simp] theorem pure_eq {ε α} (a : α) : (pure a : Except ε α) = .ok a := rfl

@[simp] theorem map_ok {ε α β} (f : α → β) (a : α) :
    (f <$> (Except.ok a : Except ε α)) = .ok (f a) := rfl

@[simp] theorem map_error {ε α β} (f : α → β) (e : ε) :
    (f <$> (Except.error e : Except ε α)) = .error e := rfl
