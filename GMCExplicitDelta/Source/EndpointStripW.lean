module

public import GMCExplicitDelta.Source.EndpointStripField
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Moments of the regularity observable from its exponential-square bound
-/

@[expose] public section

namespace GMCExplicitDelta.Source

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Abstract: nonnegative `W` with `E exp(W²/δ²) ≤ 2` has an integrable square, `E W² ≤ δ² log 2`,
and is integrable. -/
theorem moments_of_expSq (W : Ω → ℝ) (hW0 : ∀ ω, 0 ≤ W ω) {δ : ℝ} (hδ : 0 < δ)
    [IsProbabilityMeasure μ]
    (hH : Integrable (fun ω => Real.exp (W ω ^ 2 / δ ^ 2)) μ)
    (hHb : ∫ ω, Real.exp (W ω ^ 2 / δ ^ 2) ∂μ ≤ 2) :
    AEStronglyMeasurable W μ ∧ Integrable (fun ω => W ω ^ 2) μ ∧ Integrable W μ ∧
      ∫ ω, W ω ^ 2 ∂μ ≤ δ ^ 2 * Real.log 2 := by
  have hδ2 : 0 < δ ^ 2 := by positivity
  set H : Ω → ℝ := fun ω => Real.exp (W ω ^ 2 / δ ^ 2) with hHdef
  have hH1 : ∀ ω, 1 ≤ H ω := fun ω => Real.one_le_exp (by positivity)
  have hlog : ∀ ω, Real.log (H ω) = W ω ^ 2 / δ ^ 2 := fun ω => Real.log_exp _
  have hWm : AEStronglyMeasurable W μ := by
    have : AEMeasurable (fun ω => δ * Real.sqrt (Real.log (H ω))) μ :=
      (Real.continuous_sqrt.measurable.comp_aemeasurable
        (Real.measurable_log.comp_aemeasurable hH.aestronglyMeasurable.aemeasurable)).const_mul δ
    have heq : (fun ω => δ * Real.sqrt (Real.log (H ω))) = W := by
      ext ω
      rw [hlog]
      have h1 : Real.sqrt (W ω ^ 2 / δ ^ 2) = W ω / δ := by
        rw [show W ω ^ 2 / δ ^ 2 = (W ω / δ) ^ 2 by ring]
        exact Real.sqrt_sq (div_nonneg (hW0 ω) hδ.le)
      rw [h1]; field_simp
    rw [heq] at this
    exact this.aestronglyMeasurable
  have hW2m : AEStronglyMeasurable (fun ω => W ω ^ 2) μ := hWm.pow 2
  have hW2i : Integrable (fun ω => W ω ^ 2) μ := by
    refine Integrable.mono' (g := fun ω => δ ^ 2 * H ω) (hH.const_mul _) hW2m
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : W ω ^ 2 / δ ^ 2 ≤ H ω := by
      have := Real.add_one_le_exp (W ω ^ 2 / δ ^ 2)
      rw [hHdef]; linarith
    rw [div_le_iff₀ hδ2] at h1
    linarith
  have hWi : Integrable W μ := by
    refine Integrable.mono' (g := fun ω => 1 + W ω ^ 2) ((integrable_const _).add hW2i) hWm
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hW0 ω)]
    nlinarith [sq_nonneg (W ω - 1)]
  refine ⟨hWm, hW2i, hWi, ?_⟩
  -- Jensen via the tangent line of log at c = E H
  set c : ℝ := ∫ ω, H ω ∂μ with hc
  have hc1 : 1 ≤ c := by
    have := integral_mono (integrable_const (1:ℝ)) hH hH1
    simpa using this
  have hc0 : 0 < c := by linarith
  have hpt : ∀ ω, W ω ^ 2 / δ ^ 2 ≤ Real.log c + (H ω - c) / c := by
    intro ω
    have h1 := Real.log_le_sub_one_of_pos (div_pos (lt_of_lt_of_le one_pos (hH1 ω)) hc0)
    rw [Real.log_div (by linarith [hH1 ω]) hc0.ne'] at h1
    rw [← hlog ω]
    have : (H ω - c) / c = H ω / c - 1 := by field_simp
    rw [this]; linarith
  have hint : ∫ ω, W ω ^ 2 / δ ^ 2 ∂μ ≤ ∫ ω, (Real.log c + (H ω - c) / c) ∂μ :=
    integral_mono (hW2i.div_const _) ((integrable_const _).add ((hH.sub (integrable_const _)).div_const _)) hpt
  have h2 : Integrable (fun ω => (H ω - c) / c) μ := (hH.sub (integrable_const c)).div_const c
  have hrhs : ∫ ω, (Real.log c + (H ω - c) / c) ∂μ = Real.log c := by
    rw [integral_add (integrable_const _) h2, integral_div, integral_sub hH (integrable_const _)]
    simp [hc]
  rw [hrhs, integral_div] at hint
  have hlc : Real.log c ≤ Real.log 2 := Real.log_le_log hc0 hHb
  rw [div_le_iff₀ hδ2] at hint
  nlinarith

end GMCExplicitDelta.Source
