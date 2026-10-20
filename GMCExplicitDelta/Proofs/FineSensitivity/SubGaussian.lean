module

public import GMCExplicitDelta.Source.ExpMomentSeries
public import GMCExplicitDelta.Source.SubGaussian

/-! # The sub-Gaussian MGF consequence of symmetric Gaussian even moments -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace GMCExplicitDelta.Assembly

/-- All Gaussian even-moment bounds and sign symmetry imply the matching MGF bound. -/
theorem fine_hasSubgaussianMGF_of_even {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (hsym : IdentDistrib X (fun ω => -X ω) μ μ)
    (hpow : ∀ k : ℕ, Integrable (fun ω => X ω ^ (2 * k)) μ)
    (hmoment : ∀ k : ℕ, ∫ ω, X ω ^ (2 * k) ∂μ ≤
      ((2 * k - 1).doubleFactorial : ℝ) * (c : ℝ) ^ k) :
    HasSubgaussianMGF X c μ := by
  have hb (t : ℝ) : ∀ k : ℕ, ∫ ω, (t * X ω) ^ (2 * k) ∂μ ≤
      ((2 * k - 1).doubleFactorial : ℝ) * ((c : ℝ) * t ^ 2) ^ k := by
    intro k
    simp_rw [mul_pow]
    rw [integral_const_mul]
    calc
      _ ≤ t ^ (2 * k) * (((2 * k - 1).doubleFactorial : ℝ) * (c : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_left (hmoment k) (by rw [pow_mul]; positivity)
      _ = _ := by ring
  have hp (t : ℝ) (k : ℕ) : Integrable (fun ω => (t * X ω) ^ (2 * k)) μ := by
    simpa only [mul_pow] using (hpow k).const_mul (t ^ (2 * k))
  have hs (t : ℝ) : IdentDistrib (fun ω => t * X ω) (fun ω => -(t * X ω)) μ μ := by
    simpa only [Function.comp_def, Pi.mul_apply, id_eq, mul_neg] using
      hsym.comp (show Measurable (fun y : ℝ => t * y) from measurable_const.mul measurable_id)
  have hi (t : ℝ) : Integrable (fun ω => Real.exp (t * X ω)) μ :=
    Source.integrable_exp_of_even_moments (hs t) (hp t) (a := (c : ℝ) * t ^ 2)
      (s := 1) (by simpa only [mul_one] using hb t)
  refine ⟨hi, fun t => ?_⟩
  have hf := Source.hasSum_even_moments_exp (hs t) (hi t) (hp t)
  have hg := NormedSpace.expSeries_div_hasSum_exp ((c : ℝ) * t ^ 2 / 2)
  rw [Real.exp_eq_exp_ℝ]
  change (∫ ω, Real.exp (t * X ω) ∂μ) ≤ NormedSpace.exp ((c : ℝ) * t ^ 2 / 2)
  refine hasSum_le (fun k => ?_) hf hg
  exact (div_le_div_of_nonneg_right (hb t k) (by positivity)).trans_eq
    (Source.doubleFactorial_div_even_factorial ((c : ℝ) * t ^ 2) k)

end GMCExplicitDelta.Assembly
