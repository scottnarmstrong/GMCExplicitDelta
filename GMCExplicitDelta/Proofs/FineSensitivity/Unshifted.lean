module

public import GMCExplicitDelta.Proofs.FineSensitivity.Moments
public import GMCExplicitDelta.Proofs.FineSensitivity.Shift

/-! # The unshifted one-point norms in G4 -/

@[expose] public section

open MeasureTheory ProbabilityTheory SubdiffusiveProcess.CoarseGrainingVocab
open scoped NNReal ENNReal

namespace GMCExplicitDelta.Assembly

/-- The common Hölder bound at `L^64` for a polynomial times an absolute exponential. -/
theorem fine_lnorm_dominated_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : Ω → ℝ} {c : ℝ≥0}
    (hZ : HasSubgaussianMGF Z c μ) (hc : 0 < (c : ℝ)) (t : ℝ)
    {T : Ω → ℝ} (hT : ∀ ω, T ω ≤ |Z ω| * Real.exp (t * |Z ω|)) :
    paperENNRealLpNorm μ 64 (fun ω => ENNReal.ofReal (T ω)) ≤
      ENNReal.ofReal ((Real.sqrt (2 * (c : ℝ)) * Real.sqrt Contract.P32) *
        ((2 : ℝ) ^ (128 : ℝ)⁻¹ * Real.exp (64 * (c : ℝ) * t ^ 2))) := by
  have hAbs : AEMeasurable (fun ω => |Z ω|) μ := by
    simpa only [Real.norm_eq_abs] using hZ.aemeasurable.norm
  have hE := fine_lnorm_exp_abs_le hZ (q := 128) (by norm_num) t
  norm_num only [show (128 : ℝ) / 2 = 64 by norm_num] at hE
  have hEr : paperENNRealLpNorm μ (2 * 64) (fun ω => ENNReal.ofReal (Real.exp (t * |Z ω|))) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (128 : ℝ)⁻¹ * Real.exp (64 * (c : ℝ) * t ^ 2)) := by
    simpa only [one_div, show (2 : ℝ) * 64 = 128 by norm_num,
      show (c : ℝ) * 128 * t ^ 2 / 2 = 64 * (c : ℝ) * t ^ 2 by ring] using hE
  calc
    _ ≤ paperENNRealLpNorm μ 64 (fun ω =>
        ENNReal.ofReal |Z ω| * ENNReal.ofReal (Real.exp (t * |Z ω|))) :=
      HistoryLane.lnorm_mono (by norm_num) (fun ω => by
        rw [← ENNReal.ofReal_mul (abs_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (hT ω))
    _ ≤ paperENNRealLpNorm μ (2 * 64) (fun ω => ENNReal.ofReal |Z ω|) *
        paperENNRealLpNorm μ (2 * 64) (fun ω => ENNReal.ofReal (Real.exp (t * |Z ω|))) :=
      fine_lnorm_mul_le (by norm_num) hAbs.ennreal_ofReal
        ((hAbs.const_mul t).exp.ennreal_ofReal)
    _ ≤ ENNReal.ofReal (Real.sqrt (2 * (c : ℝ)) * Real.sqrt Contract.P32) *
        ENNReal.ofReal ((2 : ℝ) ^ (128 : ℝ)⁻¹ * Real.exp (64 * (c : ℝ) * t ^ 2)) :=
      mul_le_mul' (by simpa only [show (2 : ℝ) * 64 = 128 by norm_num] using
        fine_lnorm_abs128_le hZ hc) hEr
    _ = _ := (ENNReal.ofReal_mul (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).symm

/-- Unshifted square-root first increment at the exponent needed by G4. -/
theorem fine_lnorm_increment_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : Ω → ℝ} {c : ℝ≥0}
    (hZ : HasSubgaussianMGF Z c μ) (hc : 0 < (c : ℝ)) :
    paperENNRealLpNorm μ 64 (fun ω => ENNReal.ofReal |Real.exp (Z ω) - 1|) ≤
      ENNReal.ofReal ((Real.sqrt (2 * (c : ℝ)) * Real.sqrt Contract.P32) *
        ((2 : ℝ) ^ (128 : ℝ)⁻¹ * Real.exp (64 * (c : ℝ)))) := by
  simpa only [one_mul, one_pow, mul_one] using
    fine_lnorm_dominated_le hZ hc 1
      (T := fun ω => |Real.exp (Z ω) - 1|)
      (fun ω => by simpa only [one_mul] using fine_abs_exp_sub_one_le (Z ω))

/-- Unshifted square-root symmetric increment at the exponent needed by G4. -/
theorem fine_lnorm_symmetric_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : Ω → ℝ} {c : ℝ≥0}
    (hZ : HasSubgaussianMGF Z c μ) (hc : 0 < (c : ℝ)) :
    paperENNRealLpNorm μ 64
        (fun ω => ENNReal.ofReal |Real.exp (Z ω / 2) - Real.exp (-Z ω / 2)|) ≤
      ENNReal.ofReal ((Real.sqrt (2 * (c : ℝ)) * Real.sqrt Contract.P32) *
        ((2 : ℝ) ^ (128 : ℝ)⁻¹ * Real.exp (16 * (c : ℝ)))) := by
  have h := fine_lnorm_dominated_le hZ hc (1 / 2)
    (T := fun ω => |Real.exp (Z ω / 2) - Real.exp (-Z ω / 2)|) (fun ω => by
      rw [show (1 / 2 : ℝ) * |Z ω| = |Z ω| / 2 by ring]
      exact fine_abs_exp_half_diff_le (Z ω))
  simpa only [show 64 * (c : ℝ) * (1 / 2 : ℝ) ^ 2 = 16 * (c : ℝ) by ring] using h

end GMCExplicitDelta.Assembly
