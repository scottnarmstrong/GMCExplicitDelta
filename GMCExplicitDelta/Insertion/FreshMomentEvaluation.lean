module

public import GMCExplicitDelta.Insertion.FreshFormalShift
public import GMCExplicitDelta.Insertion.FreshMomentFunctional
public import GMCExplicitDelta.Insertion.CoshGenerator

/-! # Evaluation of the S9 functional on the scalar hyperbolic reference -/

@[expose] public section

open Polynomial
open scoped ENNReal

namespace GMCExplicitDelta.Insertion

/-- The even-moment functional applied coefficientwise to a nonnegative Taylor series. -/
noncomputable def bandMomentApply (δ : ℝ) (h : ℕ) (f : PowerSeries ℝ) : ℝ≥0∞ :=
  ∑' N : ℕ, ENNReal.ofReal (PowerSeries.coeff N f) * bandMomentFunctional δ h N

/-- Odd Taylor coefficients play no role in the symmetric moment comparison. -/
theorem bandMomentApply_eq_even (δ : ℝ) (h : ℕ) (f : PowerSeries ℝ) :
    bandMomentApply δ h f = ∑' n : ℕ,
      ENNReal.ofReal (PowerSeries.coeff (2 * n) f) * bandMomentFunctional δ h (2 * n) := by
  unfold bandMomentApply
  rw [← tsum_even_add_odd ENNReal.summable ENNReal.summable]
  simp only [bandMomentFunctional_odd, mul_zero, tsum_zero, add_zero]

/-- The scalar reference gives exactly the contract's band-series evaluation. -/
theorem bandMomentApply_shiftedFormalCosh (δ : ℝ) (h : ℕ) {j : ℝ} (hj : 0 ≤ j) :
    bandMomentApply δ h ((shiftedFormalCosh j - 1) ^ 32) =
      ENNReal.ofReal (Contract.bandSeriesEval δ h j) := by
  rw [bandMomentApply_eq_even]
  have hn (n : ℕ) : 0 ≤ (δ ^ 2) ^ n * PowerSeries.coeff n (Contract.bandSeries ^ h) *
      (((coshL ^ n) (X ^ 32 : ℝ[X])).eval j) :=
    mul_nonneg (mul_nonneg (pow_nonneg (sq_nonneg _) _)
      (Contract.bandSeries_pow_coeff_bounds h n).1) (coshL_pow_eval_nonneg n 32 hj)
  unfold Contract.bandSeriesEval
  rw [ENNReal.ofReal_tsum_of_nonneg hn (Contract.bandSeriesEval_summable δ h j)]
  apply tsum_congr
  intro n
  rw [bandMomentFunctional_even]
  have hB : 0 ≤ ((2 * n).factorial : ℝ) * (δ ^ 2) ^ n *
      PowerSeries.coeff n (Contract.bandSeries ^ h) / 2 ^ n :=
    div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (sq_nonneg _) _))
      (Contract.bandSeries_pow_coeff_bounds h n).1) (by positivity)
  rw [mul_comm, ← ENNReal.ofReal_mul hB]
  congr 1
  have hc := shiftedFormalCosh_even_coeff hj 32 n
  calc
    _ = (((2 * n).factorial : ℝ) *
        PowerSeries.coeff (2 * n) ((shiftedFormalCosh j - 1) ^ 32)) /
        2 ^ n * ((δ ^ 2) ^ n * PowerSeries.coeff n (Contract.bandSeries ^ h)) := by ring
    _ = (2 ^ n * (((coshL ^ n) (X ^ 32 : ℝ[X])).eval j)) / 2 ^ n *
        ((δ ^ 2) ^ n * PowerSeries.coeff n (Contract.bandSeries ^ h)) := by rw [hc]
    _ = _ := by field_simp

end GMCExplicitDelta.Insertion
