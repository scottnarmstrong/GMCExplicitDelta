module

public import GMCExplicitDelta.Averaging.MatrixAverageClass

/-! # Agreement of the averaging normalization with the contract -/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace GMCExplicitDelta.Averaging

/-- The two independently defined associated Stirling recurrences agree at order 32. -/
theorem assocStirling_contract_thirtyTwo :
    (List.range 16).map (fun k => assocStirling 32 (k + 1)) =
      (List.range 16).map (fun k => Contract.assocStirling 32 (k + 1)) := by
  decide +kernel

theorem assocStirling_contract_thirtyTwo_apply {k : ℕ} (hk : k < 16) :
    assocStirling 32 (k + 1) = Contract.assocStirling 32 (k + 1) := by
  have h := congrArg (fun l : List ℕ => l[k]!) assocStirling_contract_thirtyTwo
  simpa [List.getElem!_eq_getElem?_getD, hk] using h

/-- A3's `avgBound` is exactly the contract's `Bbar32`. -/
theorem avgBound_eq_Bbar32 (n : ℕ) (D F : ℝ) :
    avgBound 32 n (Contract.Tvarpi D F) = Contract.Bbar32 n D F := by
  unfold avgBound avgBoundPow Contract.Bbar32
  congr 1
  symm
  refine Finset.sum_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_
  · intro k hk
    have hk' := Finset.mem_range.mp hk
    simp only [Finset.mem_Icc]
    omega
  · intro a _ b _ hab
    omega
  · intro b hb
    have hb' := Finset.mem_Icc.mp hb
    exact ⟨b - 1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro k hk
    have hk' := Finset.mem_range.mp hk
    rw [assocStirling_contract_thirtyTwo_apply hk']
    have he : ((k + 1 : ℕ) : ℤ) - (32 : ℕ) = -((31 - k : ℕ) : ℤ) := by omega
    rw [he, _root_.zpow_neg, _root_.zpow_natCast]
    simp only [Nat.add_sub_cancel, div_eq_mul_inv]
    ring

end GMCExplicitDelta.Averaging
