import ChainIdProofs.Pre
open EelsRuntime ethereum.forks.amsterdam.transactions

/-- Print a result the way `eels_ground_truth.py` does. -/
def pretty (r : Except Exc (Option U64)) : String :=
  match r with
  | .ok (some x) => s!"ok {x.val}"
  | .ok none => "ok None"
  | .error e => e.name

#eval pretty (chain_id (Pre.legacy ⟨2 ^ 65 + 34, by decide⟩))
#eval pretty (chain_id (Pre.legacy ⟨2 ^ 65 + 35, by decide⟩))
#eval pretty (chain_id (Pre.legacy ⟨2 ^ 256 - 1, by decide⟩))
