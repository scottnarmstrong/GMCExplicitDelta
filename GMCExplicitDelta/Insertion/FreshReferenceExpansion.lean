module

public import GMCExplicitDelta.Insertion.FreshOldReference
public import GMCExplicitDelta.Insertion.FreshFunctionalExpand

/-! # Exact finite expansion of the band evaluation for comparison with the competitor -/

@[expose] public section

open scoped ENNReal

namespace GMCExplicitDelta.Insertion

/-- The exact band value is the positive double binomial sum appearing after
symmetrization and deterministic-weight transfer. -/
theorem bandSeriesEval_eq_even_double_sum (δ : ℝ) (h : ℕ) {j : ℝ} (hj : 0 ≤ j) :
    ENNReal.ofReal (Contract.bandSeriesEval δ h j) = ∑ l ∈ Finset.range (32 + 1),
      if Even l then ENNReal.ofReal (Nat.choose 32 l : ℝ) *
        ∑ k ∈ Finset.range (32 - l + 1),
          ENNReal.ofReal (j ^ (32 - l - k) * (Nat.choose (32 - l) k : ℝ) *
            (j + 1) ^ k * Real.sqrt (j * (j + 2)) ^ l) *
              bandMomentApply δ h ((formalCosh - 1) ^ k * formalSinh ^ l)
      else 0 := by
  have hb := bandMomentApply_add_pow δ h (oldEvenReference_coeff_nonneg hj)
    (oldOddReference_coeff_nonneg j) (rescale_neg_oldEvenReference j)
    (rescale_neg_oldOddReference j) 32
  rw [oldReference_add_eq, bandMomentApply_shiftedFormalCosh δ h hj] at hb
  refine hb.trans ?_
  apply Finset.sum_congr rfl
  intro l _
  split_ifs
  · congr 1
    change coefficientFunctional (bandMomentFunctional δ h)
      ((PowerSeries.C j + PowerSeries.C (j + 1) * (formalCosh - 1)) ^ (32 - l) *
        (PowerSeries.C (Real.sqrt (j * (j + 2))) * formalSinh) ^ l) = _
    exact coefficientFunctional_const_add_pow_mul _ formalCosh_sub_one_coeff_nonneg
      formalSinh_coeff_nonneg hj (add_nonneg hj (by norm_num)) (Real.sqrt_nonneg _) (32 - l) l
  · rfl

end GMCExplicitDelta.Insertion
