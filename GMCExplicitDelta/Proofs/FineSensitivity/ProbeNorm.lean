module

public import GMCExplicitDelta.Proofs.FineSensitivity.RemainderMeas
public import GMCExplicitDelta.Proofs.FineSensitivity.TwoWeights
public import GMCExplicitDelta.Proofs.FineSensitivity.MeasuredEnergy

/-! # Conditional fresh moments of every remainder probe -/

@[expose] public section

open Homogenization Homogenization.Book.Ch02 MeasureTheory Matrix
open SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab (ScalarCoeffOnData paperENNRealLpNorm)
open scoped ENNReal

namespace GMCExplicitDelta.Assembly

variable {d : ℕ} {U : Domain d}

theorem fine_remainder_probe_norm_le {a : Vec d → ℝ}
    (h : ScalarCoeffOnData U a) (ha : Measurable a) (ha0 : ∀ x, 0 ≤ a x)
    (M : GMCModel d) {k L : ℕ} (hkL : k ≤ L) (i : Fin d)
    {η F G : ℝ} (hη : 0 < η)
    (hF : ∀ x, paperENNRealLpNorm M.P.toMeasure 32
      (fun ω => ENNReal.ofReal ((cutoffRatio M k L ω x - 1)^2)) ≤ ENNReal.ofReal F)
    (hG : ∀ x, paperENNRealLpNorm M.P.toMeasure 32
      (fun ω => ENNReal.ofReal (cutoffRatio M k L ω x + (cutoffRatio M k L ω x)⁻¹-2)) ≤
        ENNReal.ofReal G) (e : Vec d) :
    paperENNRealLpNorm M.P.toMeasure 32 (fun ω =>
      ENNReal.ofReal (Coarse.qf (fineRemainderMatrix h (cutoffRatio M k L ω) η) e)) ≤
      ENNReal.ofReal ((∫ x, a x * vecNormSq (fineMeasGradient h.toCoeffOn false e x -
          fineMeasGradient h.toCoeffOn true e x) ∂fineDomainMeasure U) / (8*η) * F) +
      ENNReal.ofReal ((∫ x, a x * vecNormSq (fineMeasGradient h.toCoeffOn true e x)
          ∂fineDomainMeasure U) / 2 * G) := by
  let V := fineMeasGradient h.toCoeffOn false e
  let W := fineMeasGradient h.toCoeffOn true e
  let w := fun x => a x * vecNormSq (V x - W x) / (8*η)
  let v := fun x => a x * vecNormSq (W x) / 2
  let Y := fun ω x => (cutoffRatio M k L ω x - 1)^2
  let Z := fun ω x => cutoffRatio M k L ω x + (cutoffRatio M k L ω x)⁻¹ - 2
  have hV := fineMeasGradient_memL2 h.toCoeffOn false e
  have hW := fineMeasGradient_memL2 h.toCoeffOn true e
  have hi₁ := (U.isDomain.toBoundedMeasurableDomain U.nonempty).integrable_normalizedVolume _
    (Coarse.integrable_energy h i (fun j => (hV j).sub (hW j)))
  have hi₂ := (U.isDomain.toBoundedMeasurableDomain U.nonempty).integrable_normalizedVolume _
    (Coarse.integrable_energy h i hW)
  have hw : Integrable w (fineDomainMeasure U) := hi₁.div_const _
  have hv : Integrable v (fineDomainMeasure U) := hi₂.div_const _
  have hmV := measurable_fineMeasGradient h.toCoeffOn false e
  have hmW := measurable_fineMeasGradient h.toCoeffOn true e
  have hmsq {f : Vec d → Vec d} (hf : Measurable f) : Measurable (fun x => vecNormSq (f x)) := by
    unfold vecNormSq vecDot
    exact Finset.measurable_sum _ (fun j _ =>
      ((measurable_pi_apply j).comp hf).mul ((measurable_pi_apply j).comp hf))
  have hmw : Measurable w := (ha.mul (hmsq (hmV.sub hmW))).div_const _
  have hmv : Measurable v := (ha.mul (hmsq hmW)).div_const _
  have hw0 (x) : 0 ≤ w x := div_nonneg (mul_nonneg (ha0 x) (vecNormSq_nonneg _)) (by positivity)
  have hv0 (x) : 0 ≤ v x := div_nonneg (mul_nonneg (ha0 x) (vecNormSq_nonneg _)) (by norm_num)
  have hr := measurable_cutoffRatio_uncurry M hkL
  have hmY : Measurable (Function.uncurry Y) := (hr.sub measurable_const).pow_const 2
  have hmZ : Measurable (Function.uncurry Z) := (hr.add hr.inv).sub measurable_const
  have hY0 (ω x) : 0 ≤ Y ω x := sq_nonneg _
  have hZ0 (ω x) : 0 ≤ Z ω x := by
    dsimp [Z]
    rw [fine_ratio_weight_eq (cutoffRatio_pos M k L ω x)]
    exact mul_nonneg (inv_nonneg.mpr (cutoffRatio_pos M k L ω x).le) (sq_nonneg _)
  have hcY (ω) : Continuous (Y ω) := ((continuous_cutoffRatio M hkL ω).sub continuous_const).pow 2
  have hcZ (ω) : Continuous (Z ω) := by
    exact (((continuous_cutoffRatio M hkL ω).add
      ((continuous_cutoffRatio M hkL ω).inv₀ fun x => (cutoffRatio_pos M k L ω x).ne')).sub continuous_const)
  have hb := fine_two_weight_norm_le M.P.toMeasure (fineDomainMeasure U) hw hv hmw hmv hw0 hv0
    hmY hmZ hY0 hZ0 (fun ω => fine_integrable_mul_continuous hw (hcY ω))
    (fun ω => fine_integrable_mul_continuous hv (hcZ ω)) hF hG
  have heq (ω) : Coarse.qf (fineRemainderMatrix h (cutoffRatio M k L ω) η) e =
      (∫ x, w x * Y ω x ∂fineDomainMeasure U) + ∫ x, v x * Z ω x ∂fineDomainMeasure U := by
    rw [fineRemainderMatrix_qf h i (cutoffRatio_pos M k L ω) (continuous_cutoffRatio M hkL ω) η e]
    congr 1 <;> apply integral_congr_ae <;> exact Filter.Eventually.of_forall (fun x => by
      dsimp [w, v, Y, Z, V, W]
      ring)
  simp_rw [heq]
  simpa only [w, v, integral_div, V, W] using hb

/-- The old energy budgets give the exact G3 unit-probe constant. -/
theorem fine_remainder_unit_probe_norm_le {a : Vec d → ℝ}
    (h : ScalarCoeffOnData U a) (ha : Measurable a) (ha0 : ∀ x, 0 ≤ a x)
    (M : GMCModel d) {k L : ℕ} (hkL : k ≤ L)
    {η F G : ℝ} (hη : 0 < η) (hF0 : 0 ≤ F) (hG0 : 0 ≤ G)
    (hF : ∀ x, paperENNRealLpNorm M.P.toMeasure 32
      (fun ω => ENNReal.ofReal ((cutoffRatio M k L ω x - 1)^2)) ≤ ENNReal.ofReal F)
    (hG : ∀ x, paperENNRealLpNorm M.P.toMeasure 32
      (fun ω => ENNReal.ofReal (cutoffRatio M k L ω x + (cutoffRatio M k L ω x)⁻¹-2)) ≤
        ENNReal.ofReal G) {e : Vec d} (he : e ⬝ᵥ e = 1) :
    paperENNRealLpNorm M.P.toMeasure 32 (fun ω =>
      ENNReal.ofReal (Coarse.qf (fineRemainderMatrix h (cutoffRatio M k L ω) η) e)) ≤
      ENNReal.ofReal ((responseJ U h.toCoeffOn e e + 1) * (F/(2*η)+G)) := by
  obtain ⟨i⟩ := Coarse.nonempty_fin_of_dot_one he
  have hb := fine_remainder_probe_norm_le h ha ha0 M hkL i hη hF hG e
  obtain ⟨hD, hU⟩ := fine_measured_energy_budgets h he
  rw [hD] at hb
  have hJ : 0 ≤ responseJ U h.toCoeffOn e e := Homogenization.Book.Ch02.responseJ_nonneg _ _ _ _
  have hE : 0 ≤ ∫ x, a x * vecNormSq (fineMeasGradient h.toCoeffOn true e x)
      ∂fineDomainMeasure U := integral_nonneg fun x => mul_nonneg (ha0 x) (vecNormSq_nonneg _)
  rw [← ENNReal.ofReal_add (by positivity) (mul_nonneg (div_nonneg hE (by norm_num)) hG0)] at hb
  apply hb.trans (ENNReal.ofReal_le_ofReal _)
  have h₁ : (2 * responseJ U h.toCoeffOn e e + 4)/(8*η)*F ≤
      (responseJ U h.toCoeffOn e e + 1)/(2*η)*F := by
    apply mul_le_mul_of_nonneg_right _ hF0
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  have h₂ := mul_le_mul_of_nonneg_right hU hG0
  calc
    _ ≤ (responseJ U h.toCoeffOn e e + 1)/(2*η)*F +
        (responseJ U h.toCoeffOn e e + 1)*G := add_le_add h₁ (by nlinarith only [h₂])
    _ = _ := by ring

end GMCExplicitDelta.Assembly
