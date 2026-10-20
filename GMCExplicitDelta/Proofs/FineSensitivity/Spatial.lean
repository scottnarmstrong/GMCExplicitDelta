module

public import GMCExplicitDelta.Proofs.FineSensitivity.FixedWeight
public import GMCExplicitDelta.Proofs.FineSensitivity.Holder
public import Homogenization.Geometry.BoundedConvexDomain

/-! # Spatial weights for the fixed-old-sample G3 estimate -/

@[expose] public section

open MeasureTheory Homogenization Homogenization.Book.Ch02
open SubdiffusiveProcess.CoarseGrainingVocab (paperENNRealLpNorm)
open scoped ENNReal

namespace GMCExplicitDelta.Assembly

noncomputable abbrev fineDomainMeasure {d : ℕ} (U : Domain d) : Measure (Vec d) :=
  (U.isDomain.toBoundedMeasurableDomain U.nonempty).normalizedVolume

instance fineDomainMeasure_isProbabilityMeasure {d : ℕ} (U : Domain d) :
    IsProbabilityMeasure (fineDomainMeasure U) :=
  ⟨(U.isDomain.toBoundedMeasurableDomain U.nonempty).normalizedVolume_apply_univ⟩

theorem fine_average_eq_integral {d : ℕ} (U : Domain d) (f : Vec d → ℝ) :
    average U f = ∫ x, f x ∂fineDomainMeasure U := by
  rw [fineDomainMeasure, BoundedMeasurableDomain.normalizedVolume, integral_smul_measure,
    ENNReal.toReal_inv]
  rfl

theorem fine_integrable_mul_continuous {d : ℕ} {U : Domain d} {f g : Vec d → ℝ}
    (hf : Integrable f (fineDomainMeasure U)) (hg : Continuous g) :
    Integrable (fun x => f x * g x) (fineDomainMeasure U) := by
  have hc : IsCompact (closure (U : Set (Vec d))) :=
    U.isBoundedDomain.isBounded.isCompact_closure
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn hg.continuousOn
  have ha : ∀ᵐ x ∂fineDomainMeasure U, x ∈ (U : Set (Vec d)) :=
    Measure.ae_smul_measure (ae_restrict_mem U.isOpen.measurableSet) _
  exact hf.mul_bdd hg.measurable.aestronglyMeasurable
    (ha.mono fun x hx => hC x (subset_closure hx))

/-- Uniform fresh point norms transfer to a deterministic integrable old spatial weight. -/
theorem fine_fixed_weight_norm_le {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (ν : Measure E) [IsProbabilityMeasure μ] [SFinite ν]
    {w : E → ℝ} (hw : Integrable w ν) (hw0 : 0 ≤ᵐ[ν] w)
    {Y : Ω → E → ℝ} (hY : Measurable (Function.uncurry Y)) (hY0 : ∀ ω x, 0 ≤ Y ω x)
    (hprod : ∀ ω, Integrable (fun x => w x * Y ω x) ν)
    {C : ℝ}
    (hC : ∀ x, paperENNRealLpNorm μ 32 (fun ω => ENNReal.ofReal (Y ω x)) ≤ ENNReal.ofReal C) :
    paperENNRealLpNorm μ 32 (fun ω => ENNReal.ofReal (∫ x, w x * Y ω x ∂ν)) ≤
      ENNReal.ofReal ((∫ x, w x ∂ν) * C) := by
  let w' := hw.aestronglyMeasurable.mk w
  have heq : w =ᵐ[ν] w' := hw.aestronglyMeasurable.ae_eq_mk
  have hm : Measurable w' := hw.aestronglyMeasurable.measurable_mk
  have hI (ω : Ω) : ENNReal.ofReal (∫ x, w x * Y ω x ∂ν) =
      ∫⁻ x, ENNReal.ofReal (w' x) * ENNReal.ofReal (Y ω x) ∂ν := by
    rw [ofReal_integral_eq_lintegral_ofReal (hprod ω) (hw0.mono fun x hx =>
      mul_nonneg hx (hY0 ω x))]
    apply lintegral_congr_ae
    filter_upwards [heq, hw0] with x hx hnn
    rw [hx, ENNReal.ofReal_mul (hx ▸ hnn)]
  have hW : (∫⁻ x, ENNReal.ofReal (w' x) ∂ν) = ENNReal.ofReal (∫ x, w x ∂ν) := by
    rw [ofReal_integral_eq_lintegral_ofReal hw hw0]
    exact lintegral_congr_ae (heq.fun_comp ENNReal.ofReal).symm
  have hb := fine_fixed_weight_moment_le μ ν hm.ennreal_ofReal
    (Y := fun ω x => ENNReal.ofReal (Y ω x))
    (by
      change Measurable (fun p : Ω × E => ENNReal.ofReal (Y p.1 p.2))
      exact hY.ennreal_ofReal)
    (fun x => HistoryLane.lintegral_rpow_le_of_lnorm_le (by norm_num) (hC x))
  unfold paperENNRealLpNorm
  simp_rw [hI]
  refine (ENNReal.rpow_le_rpow hb (by norm_num : (0 : ℝ) ≤ (32 : ℝ)⁻¹)).trans_eq ?_
  rw [hW, ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
  norm_num only [mul_inv_cancel₀ (by norm_num : (32 : ℝ) ≠ 0), ENNReal.rpow_one]
  exact (ENNReal.ofReal_mul (integral_nonneg_of_ae hw0)).symm

end GMCExplicitDelta.Assembly
