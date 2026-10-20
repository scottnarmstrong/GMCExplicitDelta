module

public import GMCExplicitDelta.Insertion.FreshWeightedProducts
public import GMCExplicitDelta.Insertion.FreshHyperbolicFunctional
public import GMCExplicitDelta.Insertion.FreshJointField

/-! # Deterministic-weight hyperbolic product transfer for the actual fresh field -/

@[expose] public section

open MeasureTheory Homogenization SubdiffusiveProcess.Model
open scoped ENNReal

namespace GMCExplicitDelta.Insertion

/-- The sharp S9 spatial comparison after integration against deterministic weights.
All randomness is in the actual model's fresh layers. -/
theorem weighted_layer_sum_hyperbolic_product_le {d : ℕ} (M : GMCModel d)
    (I : Finset ℕ) {ν : Measure (Vec d)} [SigmaFinite ν] (k : ℕ)
    (w : Fin k → Vec d → ℝ≥0∞) (hw : ∀ i, Measurable (w i))
    (p : Fin k → ℕ) (hp : ∀ i, p i = 1 ∨ p i = 2)
    (heven : Even (∑ i : Fin k, p i)) :
    (∫⁻ ω : PotentialSample d, ∏ i : Fin k, ∫⁻ x,
      w i x * ENNReal.ofReal (if p i = 1 then |Real.sinh (∑ j ∈ I, ω j x)|
        else Real.cosh (∑ j ∈ I, ω j x) - 1) ∂ν ∂M.P.toMeasure) ≤
      (∏ i : Fin k, ∫⁻ x, w i x ∂ν) * bandMomentApply M.delta I.card
        (∏ i : Fin k, if p i = 1 then formalSinh else formalCosh - 1) := by
  let ψ : Fin k → PotentialSample d → Vec d → ℝ≥0∞ := fun i ω x =>
    ENNReal.ofReal (if p i = 1 then |Real.sinh (∑ j ∈ I, ω j x)|
      else Real.cosh (∑ j ∈ I, ω j x) - 1)
  have hm (i : Fin k) : Measurable (Function.uncurry (ψ i)) := by
    have hT := measurable_layer_sum_uncurry (d := d) I
    by_cases hi : p i = 1
    · change Measurable (fun q : PotentialSample d × Vec d =>
        ENNReal.ofReal (if p i = 1 then |Real.sinh (∑ j ∈ I, q.1 j q.2)|
          else Real.cosh (∑ j ∈ I, q.1 j q.2) - 1))
      simp only [ite_eq_left hi]
      exact (continuous_abs.measurable.comp hT.sinh).ennreal_ofReal
    · change Measurable (fun q : PotentialSample d × Vec d =>
        ENNReal.ofReal (if p i = 1 then |Real.sinh (∑ j ∈ I, q.1 j q.2)|
          else Real.cosh (∑ j ∈ I, q.1 j q.2) - 1))
      simp only [ite_eq_right hi]
      exact (hT.cosh.sub measurable_const).ennreal_ofReal
  exact lintegral_product_spatial_integrals_le k w hw ψ hm
    (fun x => layer_sum_hyperbolic_product_le_functional M I k x p hp heven)

end GMCExplicitDelta.Insertion
