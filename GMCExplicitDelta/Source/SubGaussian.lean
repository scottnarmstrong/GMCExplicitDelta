module

public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.MeasureTheory.Measure.Real

/-! # Generic sub-Gaussian estimates (step S8)

The bundled MGF hypothesis includes integrability of every exponential.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace GMCExplicitDelta.Source

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {Z : Ω → ℝ} {c : ℝ≥0}

/-- S8(a): the two-sided Chernoff bound, without symmetry assumptions. -/
theorem measure_abs_ge_le_of_subgaussian (hZ : HasSubgaussianMGF Z c μ)
    {u : ℝ} (hu : 0 ≤ u) :
    μ.real {ω | u ≤ |Z ω|} ≤ 2 * exp (-u ^ 2 / (2 * c)) := by
  have hset : {ω | u ≤ |Z ω|} = {ω | u ≤ Z ω} ∪ {ω | u ≤ (-Z) ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, Pi.neg_apply, le_abs]
  rw [hset]
  calc
    _ ≤ μ.real {ω | u ≤ Z ω} + μ.real {ω | u ≤ (-Z) ω} :=
      measureReal_union_le _ _
    _ ≤ exp (-u ^ 2 / (2 * c)) + exp (-u ^ 2 / (2 * c)) :=
      add_le_add (hZ.measure_ge_le hu) (hZ.neg.measure_ge_le hu)
    _ = _ := (two_mul _).symm

/-- The elementary domination used to pass from an MGF to an absolute MGF. -/
theorem exp_mul_abs_le (t z : ℝ) :
    exp (t * |z|) ≤ exp (t * z) + exp ((-t) * z) := by
  rcases le_total 0 z with hz | hz
  · rw [abs_of_nonneg hz]
    exact le_add_of_nonneg_right (exp_pos _).le
  · rw [abs_of_nonpos hz, mul_neg, neg_mul]
    exact le_add_of_nonneg_left (exp_pos _).le

/-- S8(a): the absolute exponential is integrable. -/
theorem integrable_exp_mul_abs_of_subgaussian (hZ : HasSubgaussianMGF Z c μ) (t : ℝ) :
    Integrable (fun ω => exp (t * |Z ω|)) μ := by
  apply ((hZ.integrable_exp_mul t).add (hZ.integrable_exp_mul (-t))).mono'
    (by
      simpa only [Real.norm_eq_abs] using
        continuous_exp.comp_aestronglyMeasurable (hZ.aestronglyMeasurable.norm.const_mul t))
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact exp_mul_abs_le t (Z ω)

/-- S8(a): the absolute MGF bound; it also holds for negative `t`. -/
theorem integral_exp_mul_abs_le_of_subgaussian (hZ : HasSubgaussianMGF Z c μ) (t : ℝ) :
    ∫ ω, exp (t * |Z ω|) ∂μ ≤ 2 * exp (c * t ^ 2 / 2) := by
  calc
    _ ≤ ∫ ω, exp (t * Z ω) + exp ((-t) * Z ω) ∂μ :=
      integral_mono (integrable_exp_mul_abs_of_subgaussian hZ t)
        ((hZ.integrable_exp_mul t).add (hZ.integrable_exp_mul (-t)))
        (fun ω => exp_mul_abs_le t (Z ω))
    _ = mgf Z μ t + mgf Z μ (-t) :=
      integral_add (hZ.integrable_exp_mul t) (hZ.integrable_exp_mul (-t))
    _ ≤ exp (c * t ^ 2 / 2) + exp (c * (-t) ^ 2 / 2) :=
      add_le_add (hZ.mgf_le t) (hZ.mgf_le (-t))
    _ = _ := by rw [neg_sq, two_mul]

end GMCExplicitDelta.Source
