module

public import GMCExplicitDelta.Proofs.FineSensitivity.Unshifted

/-! # Minkowski for the deterministic normalization shift in G4 -/

@[expose] public section

open MeasureTheory ProbabilityTheory SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal

namespace GMCExplicitDelta.Assembly

/-- Shifted exponential increments in `L^64`. -/
theorem fine_lnorm_shift_increment_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : Ω → ℝ} (hZ : AEMeasurable Z μ) (c : ℝ) :
    paperENNRealLpNorm μ 64 (fun ω => ENNReal.ofReal |Real.exp (Z ω - c) - 1|) ≤
      ENNReal.ofReal (Real.exp |c|) *
        (paperENNRealLpNorm μ 64 (fun ω => ENNReal.ofReal |Real.exp (Z ω) - 1|) +
          ENNReal.ofReal |c|) := by
  have hX : AEMeasurable (fun ω => ENNReal.ofReal |Real.exp (Z ω) - 1|) μ := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply, Pi.neg_apply] using (hZ.exp.sub aemeasurable_const).norm.ennreal_ofReal
  calc
    _ ≤ paperENNRealLpNorm μ 64 (fun ω => ENNReal.ofReal (Real.exp |c|) *
        (ENNReal.ofReal |Real.exp (Z ω) - 1| + ENNReal.ofReal |c|)) :=
      HistoryLane.lnorm_mono (by norm_num) (fun ω => by
        rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _),
          ← ENNReal.ofReal_mul (Real.exp_pos _).le]
        exact ENNReal.ofReal_le_ofReal (fine_shift_increment_le (Z ω) c))
    _ = ENNReal.ofReal (Real.exp |c|) * paperENNRealLpNorm μ 64
        (fun ω => ENNReal.ofReal |Real.exp (Z ω) - 1| + ENNReal.ofReal |c|) :=
      HistoryLane.lnorm_const_mul (by norm_num) ENNReal.ofReal_ne_top _
    _ ≤ _ := mul_le_mul' le_rfl
      ((HistoryLane.lnorm_add_le (by norm_num) hX aemeasurable_const).trans_eq
        (by rw [fine_lnorm_const μ (by norm_num)]))

/-- Shifted square-root symmetric increments in `L^64`. -/
theorem fine_lnorm_shift_symmetric_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : Ω → ℝ} (hZ : AEMeasurable Z μ) (c : ℝ) :
    paperENNRealLpNorm μ 64
        (fun ω => ENNReal.ofReal |Real.exp ((Z ω - c) / 2) - Real.exp (-(Z ω - c) / 2)|) ≤
      ENNReal.ofReal (Real.exp (|c| / 2)) *
        (paperENNRealLpNorm μ 64
            (fun ω => ENNReal.ofReal |Real.exp (Z ω / 2) - Real.exp (-Z ω / 2)|) +
          ENNReal.ofReal |c| * paperENNRealLpNorm μ 64
            (fun ω => ENNReal.ofReal (Real.exp (-Z ω / 2)))) := by
  have hX : AEMeasurable
      (fun ω => ENNReal.ofReal |Real.exp (Z ω / 2) - Real.exp (-Z ω / 2)|) μ := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply, Pi.neg_apply] using
      ((hZ.div_const 2).exp.sub (hZ.neg.div_const 2).exp).norm.ennreal_ofReal
  have hY : AEMeasurable (fun ω => ENNReal.ofReal |c| *
      ENNReal.ofReal (Real.exp (-Z ω / 2))) μ :=
    aemeasurable_const.mul ((hZ.neg.div_const 2).exp.ennreal_ofReal)
  calc
    _ ≤ paperENNRealLpNorm μ 64 (fun ω => ENNReal.ofReal (Real.exp (|c| / 2)) *
        (ENNReal.ofReal |Real.exp (Z ω / 2) - Real.exp (-Z ω / 2)| +
          ENNReal.ofReal |c| * ENNReal.ofReal (Real.exp (-Z ω / 2)))) :=
      HistoryLane.lnorm_mono (by norm_num) (fun ω => by
        rw [← ENNReal.ofReal_mul (abs_nonneg c),
          ← ENNReal.ofReal_add (abs_nonneg _)
            (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le),
          ← ENNReal.ofReal_mul (Real.exp_pos _).le]
        exact ENNReal.ofReal_le_ofReal (fine_shift_symmetric_le (Z ω) c))
    _ = ENNReal.ofReal (Real.exp (|c| / 2)) * paperENNRealLpNorm μ 64
        (fun ω => ENNReal.ofReal |Real.exp (Z ω / 2) - Real.exp (-Z ω / 2)| +
          ENNReal.ofReal |c| * ENNReal.ofReal (Real.exp (-Z ω / 2))) :=
      HistoryLane.lnorm_const_mul (by norm_num) ENNReal.ofReal_ne_top _
    _ ≤ _ := mul_le_mul' le_rfl
      ((HistoryLane.lnorm_add_le (by norm_num) hX hY).trans_eq (by
        rw [HistoryLane.lnorm_const_mul (by norm_num) ENNReal.ofReal_ne_top]))

end GMCExplicitDelta.Assembly
