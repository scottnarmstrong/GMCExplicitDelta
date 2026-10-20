module

public import GMCExplicitDelta.Insertion.FreshSpatialProducts

/-! # Deterministic spatial weights in the dependent moment comparison -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace GMCExplicitDelta.Insertion

/-- Integrate a uniform mixed-product bound against deterministic spatial weights.
Fresh evaluations may be arbitrarily dependent across the spatial coordinates. -/
theorem lintegral_product_spatial_integrals_le {Ω S : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] {μ : Measure Ω} [SFinite μ]
    {ν : Measure S} [SigmaFinite ν] (k : ℕ)
    (w : Fin k → S → ℝ≥0∞) (hw : ∀ i, Measurable (w i))
    (ψ : Fin k → Ω → S → ℝ≥0∞) (hψ : ∀ i, Measurable (Function.uncurry (ψ i)))
    {C : ℝ≥0∞} (hC : ∀ x : Fin k → S, ∫⁻ ω, ∏ i : Fin k, ψ i ω (x i) ∂μ ≤ C) :
    (∫⁻ ω, ∏ i : Fin k, ∫⁻ x, w i x * ψ i ω x ∂ν ∂μ) ≤
      (∏ i : Fin k, ∫⁻ x, w i x ∂ν) * C := by
  let ρ : Measure (Fin k → S) := Measure.pi (fun _ : Fin k => ν)
  have hm (ω : Ω) (i : Fin k) : Measurable (fun x => w i x * ψ i ω x) :=
    (hw i).mul ((hψ i).comp (measurable_const.prodMk measurable_id))
  have hj : Measurable (fun z : Ω × (Fin k → S) =>
      ∏ i : Fin k, w i (z.2 i) * ψ i z.1 (z.2 i)) :=
    Finset.measurable_prod Finset.univ (fun i _ =>
      ((hw i).comp ((measurable_pi_apply i).comp measurable_snd)).mul
        ((hψ i).comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))))
  have hp (x : Fin k → S) : Measurable (fun ω => ∏ i : Fin k, ψ i ω (x i)) :=
    Finset.measurable_prod Finset.univ (fun i _ =>
      (hψ i).comp (measurable_id.prodMk measurable_const))
  have hwprod : Measurable (fun x : Fin k → S => ∏ i : Fin k, w i (x i)) :=
    Finset.measurable_prod Finset.univ (fun i _ => (hw i).comp (measurable_pi_apply i))
  calc
    _ = ∫⁻ ω, ∫⁻ x : Fin k → S,
        ∏ i : Fin k, w i (x i) * ψ i ω (x i) ∂ρ ∂μ := by
      apply lintegral_congr
      intro ω
      exact (lintegral_fin_product_eq_product ν
        (fun i x => w i x * ψ i ω x) (hm ω)).symm
    _ = ∫⁻ x : Fin k → S, ∫⁻ ω,
        ∏ i : Fin k, w i (x i) * ψ i ω (x i) ∂μ ∂ρ :=
      lintegral_lintegral_swap hj.aemeasurable
    _ = ∫⁻ x : Fin k → S, (∏ i : Fin k, w i (x i)) *
        (∫⁻ ω, ∏ i : Fin k, ψ i ω (x i) ∂μ) ∂ρ := by
      apply lintegral_congr
      intro x
      simp only [Finset.prod_mul_distrib]
      exact lintegral_const_mul _ (hp x)
    _ ≤ ∫⁻ x : Fin k → S, (∏ i : Fin k, w i (x i)) * C ∂ρ :=
      lintegral_mono (fun x => mul_le_mul_right (hC x) _)
    _ = _ := by
      rw [lintegral_mul_const _ hwprod,
        lintegral_fin_product_eq_product ν w hw]

end GMCExplicitDelta.Insertion
