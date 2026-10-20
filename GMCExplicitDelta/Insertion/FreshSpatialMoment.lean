module

public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! # Jensen and Tonelli for spatial averages in the seed estimate -/

@[expose] public section

open MeasureTheory Set

namespace GMCExplicitDelta.Insertion

/-- A uniform pointwise moment bound survives averaging over a probability space. -/
theorem lintegral_pow_spatial_integral_le {Ω S : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] {μ : Measure Ω} {ν : Measure S}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {ψ : Ω → S → ℝ}
    (hψ : Measurable (Function.uncurry ψ)) (hnn : ∀ ω x, 0 ≤ ψ ω x)
    (hi : ∀ ω, Integrable (ψ ω) ν)
    (hip : ∀ ω, Integrable (fun x => ψ ω x ^ 32) ν)
    (hpi : ∀ x, Integrable (fun ω => ψ ω x ^ 32) μ)
    {B : ℝ} (hB : ∀ x, ∫ ω, ψ ω x ^ 32 ∂μ ≤ B) :
    ∫⁻ ω, ENNReal.ofReal (∫ x, ψ ω x ∂ν) ^ (32 : ℕ) ∂μ ≤ ENNReal.ofReal B := by
  have hc : ConvexOn ℝ (Ici 0) (fun x : ℝ => x ^ (32 : ℕ)) := by
    simpa only [Real.rpow_natCast] using (convexOn_rpow (p := ((32 : ℕ) : ℝ)) (by norm_num))
  have hj (ω : Ω) : ENNReal.ofReal (∫ x, ψ ω x ∂ν) ^ (32 : ℕ) ≤
      ∫⁻ x, ENNReal.ofReal (ψ ω x ^ 32) ∂ν := by
    rw [← ENNReal.ofReal_pow (integral_nonneg (hnn ω))]
    have hj := hc.map_integral_le (continuous_pow 32).continuousOn isClosed_Ici
      (Filter.Eventually.of_forall (hnn ω)) (hi ω) (hip ω)
    exact (ENNReal.ofReal_le_ofReal hj).trans_eq
      (ofReal_integral_eq_lintegral_ofReal (hip ω)
        (Filter.Eventually.of_forall fun x => pow_nonneg (hnn ω x) 32))
  calc
    _ ≤ ∫⁻ ω, ∫⁻ x, ENNReal.ofReal (ψ ω x ^ 32) ∂ν ∂μ := lintegral_mono hj
    _ = ∫⁻ x, ∫⁻ ω, ENNReal.ofReal (ψ ω x ^ 32) ∂μ ∂ν :=
      lintegral_lintegral_swap ((hψ.pow_const 32).ennreal_ofReal.aemeasurable)
    _ ≤ ∫⁻ _x, ENNReal.ofReal B ∂ν := by
      apply lintegral_mono
      intro x
      change (∫⁻ ω, ENNReal.ofReal (ψ ω x ^ 32) ∂μ) ≤ ENNReal.ofReal B
      rw [← ofReal_integral_eq_lintegral_ofReal (hpi x)
        (Filter.Eventually.of_forall fun ω => pow_nonneg (hnn ω x) 32)]
      exact ENNReal.ofReal_le_ofReal (hB x)
    _ = _ := by simp only [lintegral_const, measure_univ, mul_one]

end GMCExplicitDelta.Insertion
