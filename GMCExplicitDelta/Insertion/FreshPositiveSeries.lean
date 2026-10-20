module

public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.BigOperators.Fin

/-! # Nonnegative series in the spatial competitor expansion -/

@[expose] public section

open scoped ENNReal

namespace GMCExplicitDelta.Insertion

/-- Expand a finite product of nonnegative series without summability side
conditions. Tonelli applies to these joint Taylor terms in I3. -/
theorem tsum_fin_product (k : ℕ) (a : Fin k → ℕ → ℝ≥0∞) :
    (∑' n : Fin k → ℕ, ∏ i : Fin k, a i (n i)) =
      ∏ i : Fin k, ∑' n : ℕ, a i n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => ℕ)).tsum_eq]
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_mul_right, ih]

end GMCExplicitDelta.Insertion
