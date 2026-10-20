module

public import GMCExplicitDelta.Proofs.FineSensitivity.Conditional

/-! # Fixed-old-sample spatial moment transfer -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace GMCExplicitDelta.Assembly

/-- A deterministic nonnegative spatial weight retains a uniform fresh-field moment bound. -/
theorem fine_fixed_weight_moment_le {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (ν : Measure E) [IsProbabilityMeasure μ] [SFinite ν]
    {w : E → ℝ≥0∞} (hw : Measurable w) {Y : Ω → E → ℝ≥0∞}
    (hY : Measurable (Function.uncurry Y)) {C : ℝ≥0∞}
    (hC : ∀ x, ∫⁻ ω, Y ω x ^ (32 : ℝ) ∂μ ≤ C) :
    ∫⁻ ω, (∫⁻ x, w x * Y ω x ∂ν) ^ (32 : ℝ) ∂μ ≤
      (∫⁻ x, w x ∂ν) ^ (32 : ℝ) * C := by
  have hjoint : Measurable (fun p : Ω × E => w p.2 * Y p.1 p.2 ^ (32 : ℝ)) :=
    (hw.comp measurable_snd).mul (hY.pow_const (32 : ℝ))
  have hb : (∫⁻ ω, (∫⁻ x, w x * Y ω x ∂ν) ^ (32 : ℝ) ∂μ) ≤
      ∫⁻ ω, (∫⁻ x, w x ∂ν) ^ (31 : ℝ) * ∫⁻ x, w x * Y ω x ^ (32 : ℝ) ∂ν ∂μ :=
    lintegral_mono (fun ω : Ω => fine_weighted_integral_pow_le ν
      hw.aemeasurable (hY.of_uncurry_left (x := ω)).aemeasurable)
  refine hb.trans ?_
  rw [lintegral_const_mul _ hjoint.lintegral_prod_right,
    lintegral_lintegral_swap hjoint.aemeasurable]
  calc
    _ ≤ (∫⁻ x, w x ∂ν) ^ (31 : ℝ) * ∫⁻ x, w x * C ∂ν := by
      apply mul_le_mul' le_rfl
      apply lintegral_mono
      intro x
      change (∫⁻ ω, w x * Y ω x ^ (32 : ℝ) ∂μ) ≤ w x * C
      rw [lintegral_const_mul _ ((hY.of_uncurry_right (y := x)).pow_const (32 : ℝ))]
      exact mul_le_mul' le_rfl (hC x)
    _ = _ := by
      rw [lintegral_mul_const _ hw, ← mul_assoc]
      congr 1
      conv_lhs => rhs; rw [← ENNReal.rpow_one (∫⁻ x, w x ∂ν)]
      rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
      norm_num

end GMCExplicitDelta.Assembly
