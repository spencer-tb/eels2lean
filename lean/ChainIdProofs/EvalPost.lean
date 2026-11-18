import ChainIdPost
open EelsRuntime ethereum.forks.amsterdam.transactions

/-- A legacy transaction with signature value `v`, and zeros elsewhere. -/
def legacy (v : U256) : Transaction :=
  .LegacyTransaction {
    nonce := ⟨0, by decide⟩, gas_price := 0, gas := 0,
    to := .inl ⟨ByteArray.empty, rfl⟩, value := ⟨0, by decide⟩,
    data := ByteArray.empty, v := v, r := ⟨1, by decide⟩, s := ⟨1, by decide⟩ }

/-- Print a result the way `eels_ground_truth.py` does. -/
def pretty (r : Except Exc (Option U64)) : String :=
  match r with
  | .ok (some x) => s!"ok {x.val}"
  | .ok none => "ok None"
  | .error e => e.name

#eval pretty (chain_id (legacy ⟨2 ^ 65 + 34, by decide⟩))
#eval pretty (chain_id (legacy ⟨2 ^ 65 + 35, by decide⟩))
#eval pretty (chain_id (legacy ⟨2 ^ 256 - 1, by decide⟩))
