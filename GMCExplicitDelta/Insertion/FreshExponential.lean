module

public import GMCExplicitDelta.Source.ExpMomentSeries

/-! # Exponential integrability from Gaussian even moments -/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace GMCExplicitDelta.Insertion

/-- Gaussian even moments imply every real exponential moment. -/
theorem integrable_exp_mul_of_gaussian_moments {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : Ω → ℝ}
    (hsym : IdentDistrib Y (fun ω => -Y ω) μ μ)
    (hint : ∀ n : ℕ, Integrable (fun ω => Y ω ^ (2 * n)) μ)
    {v : ℝ} (hm : ∀ n : ℕ, ∫ ω, Y ω ^ (2 * n) ∂μ ≤
      ((2 * n - 1).doubleFactorial : ℝ) * v ^ n) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * Y ω)) μ := by
  have hsymt : IdentDistrib (fun ω => t * Y ω) (fun ω => -(t * Y ω)) μ μ := by
    have hm : Measurable (fun y : ℝ => t * y) := measurable_const.mul measurable_id
    simpa only [Function.comp_def, mul_neg] using hsym.comp hm
  have hit (n : ℕ) : Integrable (fun ω => (t * Y ω) ^ (2 * n)) μ := by
    simpa only [mul_pow] using (hint n).const_mul (t ^ (2 * n))
  have hmt (n : ℕ) : ∫ ω, (t * Y ω) ^ (2 * n) ∂μ ≤
      ((2 * n - 1).doubleFactorial : ℝ) * (t ^ 2 * v) ^ n := by
    simp_rw [mul_pow]
    rw [integral_const_mul]
    have ht : 0 ≤ t ^ (2 * n) := by rw [pow_mul]; positivity
    calc
      _ ≤ t ^ (2 * n) * (((2 * n - 1).doubleFactorial : ℝ) * v ^ n) :=
        mul_le_mul_of_nonneg_left (hm n) ht
      _ = _ := by rw [pow_mul]; ring
  exact Source.integrable_exp_of_even_moments hsymt hit
    (a := t ^ 2 * v) (s := 1) (by simpa only [mul_one] using hmt)

/-- Absolute exponential moments follow by adding the two signed exponentials. -/
theorem integrable_exp_mul_abs_of_gaussian_moments {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : Ω → ℝ} (hY : Measurable Y)
    (hsym : IdentDistrib Y (fun ω => -Y ω) μ μ)
    (hint : ∀ n : ℕ, Integrable (fun ω => Y ω ^ (2 * n)) μ)
    {v : ℝ} (hm : ∀ n : ℕ, ∫ ω, Y ω ^ (2 * n) ∂μ ≤
      ((2 * n - 1).doubleFactorial : ℝ) * v ^ n) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * |Y ω|)) μ := by
  have hp := integrable_exp_mul_of_gaussian_moments hsym hint hm t
  have hn := integrable_exp_mul_of_gaussian_moments hsym hint hm (-t)
  apply (hp.add hn).mono' ((continuous_abs.measurable.comp hY).const_mul t).exp.aestronglyMeasurable
  filter_upwards [] with ω
  change ‖Real.exp (t * |Y ω|)‖ ≤ Real.exp (t * Y ω) + Real.exp ((-t) * Y ω)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rcases le_total 0 (Y ω) with h | h
  · rw [abs_of_nonneg h]
    exact le_add_of_nonneg_right (Real.exp_pos _).le
  · rw [abs_of_nonpos h, mul_neg, neg_mul]
    exact le_add_of_nonneg_left (Real.exp_pos _).le

end GMCExplicitDelta.Insertion
