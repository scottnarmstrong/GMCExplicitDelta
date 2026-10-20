module

public import GMCExplicitDelta.Insertion.FreshBandOperator

@[expose] public section

open Polynomial
open scoped Matrix.Norms.Operator

namespace GMCExplicitDelta.Contract

/-- I4(a), coefficient form, with the exact statement. -/
theorem bandRow_eq_bandSeriesCoeff_proof (δ : ℝ) (h : ℕ) (r : Fin 33) :
    bandRow δ h r = bandSeriesCoeff δ h r := by
  unfold bandRow
  rw [bandMatrix_eq_tsum]
  have hp := congrArg (fun A : Matrix (Fin 33) (Fin 33) ℝ => A 32 r)
    (bandSeries_tsum_pow ((δ ^ 2) • generatorMatrix) h)
  refine hp.trans ?_
  refine (matrix_tsum_apply _ (bandSeries_summable_norm ((δ ^ 2) • generatorMatrix) h).of_norm 32 r).trans ?_
  unfold bandSeriesCoeff
  apply tsum_congr
  intro n
  rw [smul_pow, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
    generatorMatrix_pow_apply]
  simp only [show ((32 : Fin 33) : ℕ) = 32 by decide]
  ring

/-- I4(a), evaluation form, with the exact statement. -/
theorem bandSeriesEval_eq_sum_proof (δ : ℝ) (h : ℕ) (y : ℝ) :
    bandSeriesEval δ h y = ∑ r : Fin 33, bandRow δ h r * y ^ (r : ℕ) := by
  classical
  simp_rw [bandRow_eq_bandSeriesCoeff_proof, bandSeriesCoeff, ← tsum_mul_right]
  rw [← Summable.tsum_finsetSum (fun r _ => (bandSeriesCoeff_summable δ h r).mul_right _)]
  unfold bandSeriesEval
  apply tsum_congr
  intro n
  rw [coshL_pow_eval_fin_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

end GMCExplicitDelta.Contract
