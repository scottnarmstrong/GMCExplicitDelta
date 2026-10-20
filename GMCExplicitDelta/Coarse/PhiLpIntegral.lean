module

public import GMCExplicitDelta.Coarse.PhiLp
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# C7, integral form: `∫ J^p ≤ A^p` implies `∫ Φ_t(J)^p ≤ Φ_t(A)^p`

`integral_phi_rpow_le`: for a probability measure, `p ≥ 2`, `J ≥ 0` measurable with `J^p`
integrable and `∫ J^p ≤ A^p`, the function `Φ_t(J)^p` is integrable and `∫ Φ_t(J)^p ≤ Φ_t(A)^p`.
(Equivalently `‖Φ_t(J)‖_p ≤ Φ_t(‖J‖_p)`.)  Derived from `eLpNorm_phi_comp_le`.
-/

@[expose] public section

open MeasureTheory Real
open scoped ENNReal

namespace GMCExplicitDelta.Coarse

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem continuous_phi (t : ℝ) : Continuous (phi t) := by
  unfold phi
  fun_prop

omit [IsProbabilityMeasure μ] in
/-- Integral hypothesis implies the `L^p` bound. -/
theorem eLpNorm_le_of_integral_rpow_le {p : ℝ} (hp : 2 ≤ p) {J : Ω → ℝ} (hJ : AEMeasurable J μ)
    (hJ0 : ∀ ω, 0 ≤ J ω)
    (hJint : Integrable (fun ω => J ω ^ p) μ) {A : ℝ} (hA : 0 ≤ A)
    (hJA : ∫ ω, J ω ^ p ∂μ ≤ A ^ p) :
    eLpNorm J (ENNReal.ofReal p) μ ≤ ENNReal.ofReal A := by
  have hp0 : 0 < p := by linarith
  have hP0 : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  rw [eLpNorm_eq_eLpNorm' hP0 ENNReal.ofReal_ne_top hJ.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp0.le]
  unfold eLpNorm'
  have h1 : ∫⁻ ω, ‖J ω‖ₑ ^ p ∂μ = ENNReal.ofReal (∫ ω, J ω ^ p ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hJint
      (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (hJ0 ω) p)]
    congr 1
    funext ω
    rw [Real.enorm_eq_ofReal (hJ0 ω), ENNReal.ofReal_rpow_of_nonneg (hJ0 ω) hp0.le]
  rw [h1]
  have h2 : ENNReal.ofReal (∫ ω, J ω ^ p ∂μ) ≤ ENNReal.ofReal A ^ p := by
    rw [ENNReal.ofReal_rpow_of_nonneg hA hp0.le]
    exact ENNReal.ofReal_le_ofReal hJA
  calc (ENNReal.ofReal (∫ ω, J ω ^ p ∂μ)) ^ (1 / p) ≤ (ENNReal.ofReal A ^ p) ^ (1 / p) :=
        ENNReal.rpow_le_rpow h2 (by positivity)
    _ = ENNReal.ofReal A := by
        rw [← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one]

theorem integral_phi_rpow_le {p : ℝ} (hp : 2 ≤ p) {J : Ω → ℝ} (hJ : AEMeasurable J μ)
    (hJ0 : ∀ ω, 0 ≤ J ω) (hJint : Integrable (fun ω => J ω ^ p) μ) {t A : ℝ} (ht : 0 ≤ t)
    (hA : 0 ≤ A) (hJA : ∫ ω, J ω ^ p ∂μ ≤ A ^ p) :
    Integrable (fun ω => phi t (J ω) ^ p) μ ∧
      ∫ ω, phi t (J ω) ^ p ∂μ ≤ phi t A ^ p := by
  have hp0 : 0 < p := by linarith
  have hP0 : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  have hB := eLpNorm_phi_comp_le hp hJ hJ0 ht hA (eLpNorm_le_of_integral_rpow_le hp hJ hJ0 hJint hA hJA)
  have hf0 : ∀ ω, 0 ≤ phi t (J ω) := fun ω => phi_nonneg (hJ0 ω) ht
  have hfm : AEMeasurable (fun ω => phi t (J ω)) μ :=
    (continuous_phi t).measurable.comp_aemeasurable hJ
  have hPA : 0 ≤ phi t A := phi_nonneg hA ht
  rw [eLpNorm_eq_eLpNorm' hP0 ENNReal.ofReal_ne_top hfm.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp0.le] at hB
  unfold eLpNorm' at hB
  have hlin : ∫⁻ ω, ‖phi t (J ω)‖ₑ ^ p ∂μ ≤ ENNReal.ofReal (phi t A ^ p) := by
    have := ENNReal.rpow_le_rpow hB hp0.le
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one,
      ENNReal.ofReal_rpow_of_nonneg hPA hp0.le] at this
    exact this
  have hfp : ∀ ω, ‖phi t (J ω) ^ p‖ₑ = ‖phi t (J ω)‖ₑ ^ p := by
    intro ω
    rw [Real.enorm_eq_ofReal (Real.rpow_nonneg (hf0 ω) p), Real.enorm_eq_ofReal (hf0 ω),
      ENNReal.ofReal_rpow_of_nonneg (hf0 ω) hp0.le]
  have hmeas : AEStronglyMeasurable (fun ω => phi t (J ω) ^ p) μ :=
    (hfm.pow_const p).aestronglyMeasurable
  have hint : Integrable (fun ω => phi t (J ω) ^ p) μ := by
    refine ⟨hmeas, ?_⟩
    unfold HasFiniteIntegral
    simp only [hfp]
    exact lt_of_le_of_lt hlin ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω =>
    Real.rpow_nonneg (hf0 ω) p) hmeas]
  refine ENNReal.toReal_le_of_le_ofReal (Real.rpow_nonneg hPA p) ?_
  calc ∫⁻ ω, ENNReal.ofReal (phi t (J ω) ^ p) ∂μ
      = ∫⁻ ω, ‖phi t (J ω)‖ₑ ^ p ∂μ := by
        congr 1; funext ω
        rw [Real.enorm_eq_ofReal (hf0 ω), ENNReal.ofReal_rpow_of_nonneg (hf0 ω) hp0.le]
    _ ≤ _ := hlin

end GMCExplicitDelta.Coarse
