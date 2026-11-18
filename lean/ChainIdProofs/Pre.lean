import ChainIdPre
import ChainIdProofs.Except
open EelsRuntime ethereum.forks.amsterdam.transactions

/-!
EELS `16898000911` (before #3828, the commit eels2lean pins): `chain_id`
can raise `OverflowError`.
-/

namespace Pre

/-- A legacy transaction with signature value `v`, and zeros elsewhere. -/
def legacy (v : U256) : Transaction :=
  .LegacyTransaction {
    nonce := ⟨0, by decide⟩, gas_price := 0, gas := 0,
    to := .inl ⟨ByteArray.empty, rfl⟩, value := ⟨0, by decide⟩,
    data := ByteArray.empty, v := v, r := ⟨1, by decide⟩, s := ⟨1, by decide⟩ }

/-- The counterexample from #3828: `v = 2 ** 65 + 35`. -/
theorem overflows_at :
    chain_id (legacy ⟨2 ^ 65 + 35, by decide⟩) = .error .OverflowError := by
  rfl

/-- So some transaction makes `chain_id` raise `OverflowError`. -/
theorem overflow_reachable :
    ∃ tx : Transaction, chain_id tx = .error .OverflowError :=
  ⟨_, overflows_at⟩

/-- Exactly the legacy `v` from `2 ** 65 + 35` up raise `OverflowError`. -/
theorem overflows_iff (tx : LegacyTransaction) :
    chain_id (.LegacyTransaction tx) = .error .OverflowError ↔
      2 ^ 65 + 35 ≤ tx.v.val := by
  obtain ⟨_, _, _, _, _, _, ⟨n, hn⟩, _, _⟩ := tx
  by_cases unprotected : n = 27 ∨ n = 28
  · rcases unprotected with rfl | rfl <;> simp [chain_id]
  have not27 : n ≠ 27 := by omega
  have not28 : n ≠ 28 := by omega
  by_cases small : n < 35
  · have : ¬ 2 ^ 65 + 35 ≤ n := by omega
    simp [chain_id, Fixed.ofNat, Fixed.sub, Fixed.shr, not27, not28, small,
      this]
  · have big : 35 ≤ n := by omega
    have sub_ok : n - 35 < 2 ^ 256 := by omega
    have shr_ok : (n - 35) >>> 1 < 2 ^ 256 := by
      rw [Nat.shiftRight_eq_div_pow]; omega
    have fits_iff : (n - 35) >>> 1 < 2 ^ 64 ↔ ¬ 2 ^ 65 + 35 ≤ n := by
      rw [Nat.shiftRight_eq_div_pow]; omega
    simp only [Nat.reducePow, Nat.reduceAdd] at sub_ok shr_ok fits_iff ⊢
    by_cases fits : (n - 35) >>> 1 < 18446744073709551616
    · simp [chain_id, Fixed.ofNat, Fixed.sub, Fixed.shr, raise, not27, not28,
        small, big, sub_ok, shr_ok, fits, fits_iff.mp fits]
    · have : 36893488147419103267 ≤ n := by
        rw [fits_iff] at fits; omega
      simp [chain_id, Fixed.ofNat, Fixed.sub, Fixed.shr, raise, not27, not28,
        small, big, sub_ok, shr_ok, fits, this]

end Pre

#print axioms Pre.overflows_at
#print axioms Pre.overflow_reachable
#print axioms Pre.overflows_iff
