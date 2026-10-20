module

public import GMCExplicitDelta.Proofs.FineSensitivity.Splice
public import GMCExplicitDelta.Proofs.FineSensitivity.Holder

/-! # Conditioning without a jointly measurable old maximizer -/

@[expose] public section

open MeasureTheory SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab (paperENNRealLpNorm)
open scoped ENNReal

namespace GMCExplicitDelta.Assembly

/-- Only the scalar observable needs joint measurability. Its conditional bound may
be obtained using independently chosen deterministic old competitors. -/
theorem fine_spliced_norm_le {d : ℕ} (M : GMCModel d) (k : ℕ)
    {X B : PotentialSample d → ℝ≥0∞} (hX : Measurable X) (hB : Measurable B)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hinner : ∀ old, (∫⁻ fresh, X (fineSpliceSample k (old, fresh)) ^ (32 : ℝ) ∂M.P.toMeasure) ≤
      C ^ (32 : ℝ) * (1+B old) ^ (32 : ℝ)) :
    paperENNRealLpNorm M.P.toMeasure 32 X ≤
      C * (1 + paperENNRealLpNorm M.P.toMeasure 32 B) := by
  have hi : (∫⁻ ω, X ω ^ (32 : ℝ) ∂M.P.toMeasure) ≤
      C ^ (32 : ℝ) * ∫⁻ ω, (1+B ω) ^ (32 : ℝ) ∂M.P.toMeasure := by
    rw [fine_lintegral_eq_spliced_iterated M k (hX.pow_const (32 : ℝ))]
    exact (lintegral_mono hinner).trans_eq
      (lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hC))
  have hb : paperENNRealLpNorm M.P.toMeasure 32 (fun ω => 1+B ω) ≤
      1 + paperENNRealLpNorm M.P.toMeasure 32 B := by
    simpa only [fine_lnorm_const M.P.toMeasure (by norm_num : (0 : ℝ) < 32) 1] using
      (HistoryLane.lnorm_add_le (μ := M.P.toMeasure) (X := fun _ => (1 : ℝ≥0∞))
        (by norm_num : (1 : ℝ) ≤ 32) measurable_const.aemeasurable hB.aemeasurable)
  have hr := ENNReal.rpow_le_rpow hi (by norm_num : (0 : ℝ) ≤ (32 : ℝ)⁻¹)
  change paperENNRealLpNorm M.P.toMeasure 32 X ≤ _ at hr
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul] at hr
  norm_num only [mul_inv_cancel₀ (by norm_num : (32 : ℝ) ≠ 0), ENNReal.rpow_one] at hr
  unfold paperENNRealLpNorm at hb hr ⊢
  norm_num only at hb hr ⊢
  exact hr.trans (mul_le_mul le_rfl hb bot_le bot_le)

end GMCExplicitDelta.Assembly
