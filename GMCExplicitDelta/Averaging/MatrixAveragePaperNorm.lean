module

public import GMCExplicitDelta.Averaging.MatrixAverageCaps
public import SubdiffusiveProcess.CoarseGrainingVocab.Defect

/-! # Conversion between the paper's ENNReal moments and real L32 norms -/

@[expose] public section

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal Matrix.Norms.L2Operator

namespace GMCExplicitDelta.Averaging

noncomputable local instance {d : ℕ} : ContinuousENorm (Matrix (Fin d) (Fin d) ℝ) :=
  SeminormedAddGroup.toContinuousENorm

theorem paperNorm_ofReal_eq_eLpNorm {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) (hnn : ∀ ω, 0 ≤ f ω) :
    paperENNRealLpNorm μ 32 (fun ω => ENNReal.ofReal (f ω)) = eLpNorm f 32 μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  unfold paperENNRealLpNorm
  norm_num only [ENNReal.toReal_ofNat]
  congr 1
  apply lintegral_congr
  intro ω
  rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hnn ω)]

theorem paperNorm_matrix_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {d : ℕ}
    {A : Ω → Matrix (Fin d) (Fin d) ℝ} (hA : Measurable A) :
    paperENNRealLpNorm μ 32
      (fun ω => ENNReal.ofReal (‖Matrix.toEuclideanCLM (𝕜 := ℝ) (A ω)‖)) = eLpNorm A 32 μ := by
  simp only [← Matrix.cstar_norm_def]
  rw [paperNorm_ofReal_eq_eLpNorm hA.aestronglyMeasurable.norm (fun _ => norm_nonneg _),
    eLpNorm_norm A hA.aestronglyMeasurable]

theorem integral_norm_pow_eq_lpNorm_pow {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] {μ : Measure Ω} {A : Ω → E} (hm : MemLp A 32 μ) :
    (∫ ω, ‖A ω‖ ^ 32 ∂μ) = lpNorm A 32 μ ^ 32 := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hm.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, Real.rpow_ofNat]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (integral_nonneg fun _ => by positivity)]
  norm_num

end GMCExplicitDelta.Averaging
