module

public import GMCExplicitDelta.Insertion.FreshSeedNorm

/-! # Literal 32nd moments extracted from the paper's ENNReal norm -/

@[expose] public section

open MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab (paperENNRealLpNorm)
open scoped ENNReal

namespace GMCExplicitDelta.Insertion

theorem lintegral_pow_le_of_paperNorm {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ≥0∞) {B : ℝ} (hB : 0 ≤ B)
    (h : paperENNRealLpNorm μ 32 X ≤ ENNReal.ofReal B) :
    (∫⁻ ω, X ω ^ (32 : ℕ) ∂μ) ≤ ENNReal.ofReal (B ^ (32 : ℕ)) := by
  unfold paperENNRealLpNorm at h
  simp only [ENNReal.rpow_ofNat] at h
  have hr := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 32)
  rw [← ENNReal.rpow_mul, inv_mul_cancel₀ (by norm_num : (32 : ℝ) ≠ 0), ENNReal.rpow_one] at hr
  calc
    _ ≤ ENNReal.ofReal B ^ (32 : ℕ) := by simpa only [ENNReal.rpow_ofNat] using hr
    _ = _ := (ENNReal.ofReal_pow hB 32).symm

/-- A finite nonnegative moment bound gives both real integrability and the real bound. -/
theorem integrable_pow_and_integral_le_of_lintegral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} (hX : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω)
    {B : ℝ} (hB : 0 ≤ B)
    (hm : (∫⁻ ω, ENNReal.ofReal (X ω) ^ (32 : ℕ) ∂μ) ≤ ENNReal.ofReal B) :
    Integrable (fun ω => X ω ^ (32 : ℕ)) μ ∧ (∫ ω, X ω ^ (32 : ℕ) ∂μ) ≤ B := by
  have he (ω : Ω) : ‖X ω ^ (32 : ℕ)‖ₑ = ENNReal.ofReal (X ω) ^ (32 : ℕ) := by
    rw [Real.enorm_eq_ofReal (pow_nonneg (hX0 ω) _), ENNReal.ofReal_pow (hX0 ω)]
  have hint : Integrable (fun ω => X ω ^ (32 : ℕ)) μ := by
    refine ⟨(hX.pow_const 32).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    simp only [he]
    exact lt_of_le_of_lt hm (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top)
  refine ⟨hint, (ENNReal.ofReal_le_ofReal_iff hB).mp ?_⟩
  rw [ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun ω => pow_nonneg (hX0 ω) 32)]
  refine le_trans (le_of_eq (lintegral_congr fun ω => ?_)) hm
  exact ENNReal.ofReal_pow (hX0 ω) 32

end GMCExplicitDelta.Insertion
