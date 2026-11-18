import ChainIdPre
import ChainIdProofs.Except
open EelsRuntime ethereum.forks.amsterdam.transactions

-- Pre has no `2 ^ 64 - 1 <` check, so the `above_max` facts go unused there.
set_option linter.unusedSimpArgs false

/-!
The same theorems and the same proofs as `Post.lean`, against EELS
`16898000911` (before #3828), the commit eels2lean pins.
Expected to FAIL: this file is not part of the `ChainIdProofs` build.
-/

namespace Pre

/-- The allowlist: the only exception `chain_id` may raise is the one its
own `raise` statements name, `InvalidSignatureError("bad v")`. -/
theorem only_raises_bad_v (tx : Transaction) (e : Exc)
    (h : chain_id tx = .error e) : e = .InvalidSignatureError := by
  cases tx with
  | LegacyTransaction tx =>
    obtain ⟨_, _, _, _, _, _, ⟨n, hn⟩, _, _⟩ := tx
    by_cases unprotected : n = 27 ∨ n = 28
    · -- `v` is 27 or 28: no chain id, nothing raised.
      rcases unprotected with rfl | rfl <;> simp [chain_id] at h
    have not27 : n ≠ 27 := by omega
    have not28 : n ≠ 28 := by omega
    by_cases small : n < 35
    · -- `v < 35`: the code raises InvalidSignatureError first.
      simp [chain_id, Fixed.ofNat, Fixed.sub, Fixed.shr, not27, not28,
        small] at h
      simp [← h]
    · -- Otherwise `v - 35` and `(v - 35) >> 1` stay inside U256 ...
      have big : 35 ≤ n := by omega
      have sub_ok : n - 35 < 2 ^ 256 := by omega
      have shr_ok : (n - 35) >>> 1 < 2 ^ 256 := by
        rw [Nat.shiftRight_eq_div_pow]; omega
      simp only [Nat.reducePow] at sub_ok shr_ok
      -- ... so everything turns on whether the chain id fits in U64.
      by_cases fits : (n - 35) >>> 1 < 2 ^ 64
      · have not_above_max : ¬ 2 ^ 64 - 1 < (n - 35) >>> 1 := by omega
        simp only [Nat.reducePow, Nat.reduceSub] at fits not_above_max
        simp [chain_id, Fixed.ofNat, Fixed.sub, Fixed.shr, raise, not27,
          not28, small, big, sub_ok, shr_ok, fits, not_above_max] at h
          <;> simp [← h]
      · have above_max : 2 ^ 64 - 1 < (n - 35) >>> 1 := by omega
        simp only [Nat.reducePow, Nat.reduceSub] at fits above_max
        simp [chain_id, Fixed.ofNat, Fixed.sub, Fixed.shr, raise, not27,
          not28, small, big, sub_ok, shr_ok, fits, above_max] at h
          <;> simp [← h]
  -- Typed transactions carry a `U64` chain id: nothing to raise.
  | _ => simp [chain_id] at h

/-- The #3828 crash, as a corollary: `OverflowError` is not on the list. -/
theorem never_overflows (tx : Transaction) :
    chain_id tx ≠ .error .OverflowError := by
  intro h
  cases only_raises_bad_v tx _ h

end Pre

#print axioms Pre.only_raises_bad_v
#print axioms Pre.never_overflows
