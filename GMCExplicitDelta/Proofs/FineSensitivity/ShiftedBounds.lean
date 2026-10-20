module

public import GMCExplicitDelta.Proofs.FineSensitivity.ShiftNorm

/-! # Quantitative shifted square-root moments -/

@[expose] public section

open MeasureTheory ProbabilityTheory SubdiffusiveProcess.CoarseGrainingVocab
open scoped NNReal ENNReal

namespace GMCExplicitDelta.Assembly

/-- The common square-root moment amplitude before inserting the fresh-band proxy. -/
noncomputable def fineAmplitude (a : ℝ≥0) : ℝ :=
  Real.sqrt (2 * (a : ℝ)) * Real.sqrt Contract.P32 * (2 : ℝ) ^ (128 : ℝ)⁻¹

theorem fineAmplitude_nonneg (a : ℝ≥0) : 0 ≤ fineAmplitude a := by
  unfold fineAmplitude
  positivity

/-- The shifted first increment in `L^64`, ready to square. -/
theorem fine_shifted_increment_norm_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : Ω → ℝ} {a : ℝ≥0}
    (hZ : HasSubgaussianMGF Z a μ) (ha : 0 < (a : ℝ)) (c : ℝ) :
    paperENNRealLpNorm μ 64 (fun ω => ENNReal.ofReal |Real.exp (Z ω - c) - 1|) ≤
      ENNReal.ofReal (Real.exp (|c| + 64 * (a : ℝ)) * (fineAmplitude a + |c|)) := by
  have hI : paperENNRealLpNorm μ 64 (fun ω => ENNReal.ofReal |Real.exp (Z ω) - 1|) ≤
      ENNReal.ofReal (fineAmplitude a * Real.exp (64 * (a : ℝ))) := by
    simpa only [fineAmplitude, mul_assoc] using fine_lnorm_increment_le hZ ha
  refine (fine_lnorm_shift_increment_le hZ.aemeasurable c).trans ?_
  refine (mul_le_mul' le_rfl (add_le_add hI le_rfl)).trans ?_
  rw [← ENNReal.ofReal_add (mul_nonneg (fineAmplitude_nonneg a) (Real.exp_pos _).le)
    (abs_nonneg _), ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  rw [Real.exp_add]
  have he : 1 ≤ Real.exp (64 * (a : ℝ)) := Real.one_le_exp_iff.mpr (by positivity)
  have hm := mul_le_mul_of_nonneg_left he (abs_nonneg c)
  have hsum : fineAmplitude a * Real.exp (64 * (a : ℝ)) + |c| ≤
      Real.exp (64 * (a : ℝ)) * (fineAmplitude a + |c|) := by nlinarith only [hm]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsum (Real.exp_pos |c|).le

/-- The shifted square-root symmetric increment in `L^64`, ready to square. -/
theorem fine_shifted_symmetric_norm_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : Ω → ℝ} {a : ℝ≥0}
    (hZ : HasSubgaussianMGF Z a μ) (ha : 0 < (a : ℝ)) (c : ℝ) :
    paperENNRealLpNorm μ 64
        (fun ω => ENNReal.ofReal |Real.exp ((Z ω - c) / 2) - Real.exp (-(Z ω - c) / 2)|) ≤
      ENNReal.ofReal (Real.exp (|c| / 2 + 16 * (a : ℝ)) * (fineAmplitude a + |c|)) := by
  have hI : paperENNRealLpNorm μ 64
      (fun ω => ENNReal.ofReal |Real.exp (Z ω / 2) - Real.exp (-Z ω / 2)|) ≤
      ENNReal.ofReal (fineAmplitude a * Real.exp (16 * (a : ℝ))) := by
    simpa only [fineAmplitude, mul_assoc] using fine_lnorm_symmetric_le hZ ha
  have hE : paperENNRealLpNorm μ 64 (fun ω => ENNReal.ofReal (Real.exp (-Z ω / 2))) ≤
      ENNReal.ofReal (Real.exp (8 * (a : ℝ))) := by
    have h := fine_lnorm_exp_le hZ (q := 64) (by norm_num) (-1 / 2)
    convert h using 1
    · congr 1; funext ω; congr 2; ring
    · congr 2; ring
  refine (fine_lnorm_shift_symmetric_le hZ.aemeasurable c).trans ?_
  refine (mul_le_mul' le_rfl (add_le_add hI (mul_le_mul' le_rfl hE))).trans ?_
  rw [← ENNReal.ofReal_mul (abs_nonneg _),
    ← ENNReal.ofReal_add (mul_nonneg (fineAmplitude_nonneg a) (Real.exp_pos _).le)
      (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le),
    ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  rw [Real.exp_add]
  have hm := mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (show 8 * (a : ℝ) ≤ 16 * (a : ℝ) by linarith only [ha])) (abs_nonneg c)
  have hsum : fineAmplitude a * Real.exp (16 * (a : ℝ)) + |c| * Real.exp (8 * (a : ℝ)) ≤
      Real.exp (16 * (a : ℝ)) * (fineAmplitude a + |c|) := by nlinarith only [hm]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsum (Real.exp_pos (|c| / 2)).le

end GMCExplicitDelta.Assembly
