module

public import GMCExplicitDelta.Proofs.FineSensitivity.Spatial
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Fresh moment bounds for two deterministic spatial weights -/

@[expose] public section

open MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab (paperENNRealLpNorm)
open scoped ENNReal

namespace GMCExplicitDelta.Assembly

theorem fine_two_weight_norm_le {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (ν : Measure E) [IsProbabilityMeasure μ] [SFinite ν]
    {w v : E → ℝ} (hw : Integrable w ν) (hv : Integrable v ν)
    (hmw : Measurable w) (hmv : Measurable v)
    (hw0 : ∀ x, 0 ≤ w x) (hv0 : ∀ x, 0 ≤ v x)
    {Y Z : Ω → E → ℝ} (hY : Measurable (Function.uncurry Y))
    (hZ : Measurable (Function.uncurry Z))
    (hY0 : ∀ ω x, 0 ≤ Y ω x) (hZ0 : ∀ ω x, 0 ≤ Z ω x)
    (hpY : ∀ ω, Integrable (fun x => w x * Y ω x) ν)
    (hpZ : ∀ ω, Integrable (fun x => v x * Z ω x) ν)
    {F G : ℝ} (hF : ∀ x, paperENNRealLpNorm μ 32
      (fun ω => ENNReal.ofReal (Y ω x)) ≤ ENNReal.ofReal F)
    (hG : ∀ x, paperENNRealLpNorm μ 32
      (fun ω => ENNReal.ofReal (Z ω x)) ≤ ENNReal.ofReal G) :
    paperENNRealLpNorm μ 32 (fun ω => ENNReal.ofReal
      ((∫ x, w x * Y ω x ∂ν) + ∫ x, v x * Z ω x ∂ν)) ≤
      ENNReal.ofReal ((∫ x, w x ∂ν) * F) + ENNReal.ofReal ((∫ x, v x ∂ν) * G) := by
  have hmy : Measurable (fun ω => ∫ x, w x * Y ω x ∂ν) :=
    ((hmw.comp measurable_snd).mul hY).stronglyMeasurable.integral_prod_right'.measurable
  have hmz : Measurable (fun ω => ∫ x, v x * Z ω x ∂ν) :=
    ((hmv.comp measurable_snd).mul hZ).stronglyMeasurable.integral_prod_right'.measurable
  have hy0 (ω : Ω) : 0 ≤ ∫ x, w x * Y ω x ∂ν :=
    integral_nonneg (fun x => mul_nonneg (hw0 x) (hY0 ω x))
  have hz0 (ω : Ω) : 0 ≤ ∫ x, v x * Z ω x ∂ν :=
    integral_nonneg (fun x => mul_nonneg (hv0 x) (hZ0 ω x))
  simp_rw [ENNReal.ofReal_add (hy0 _) (hz0 _)]
  exact (HistoryLane.lnorm_add_le (by norm_num) hmy.ennreal_ofReal.aemeasurable
    hmz.ennreal_ofReal.aemeasurable).trans (add_le_add
      (fine_fixed_weight_norm_le μ ν hw (Filter.Eventually.of_forall hw0) hY hY0 hpY hF)
      (fine_fixed_weight_norm_le μ ν hv (Filter.Eventually.of_forall hv0) hZ hZ0 hpZ hG))

end GMCExplicitDelta.Assembly
