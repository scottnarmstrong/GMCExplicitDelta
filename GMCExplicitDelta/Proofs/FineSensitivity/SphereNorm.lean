module

public import GMCExplicitDelta.Proofs.FineSensitivity.Sphere
public import GMCExplicitDelta.Averaging.MatrixAveragePaperNorm

/-! # C13 in the paper's ENNReal moment convention -/

@[expose] public section

open MeasureTheory Matrix GMCExplicitDelta.Insertion
open SubdiffusiveProcess.CoarseGrainingVocab (paperENNRealLpNorm)
open scoped ENNReal

namespace GMCExplicitDelta.Assembly

/-- A real nonnegative probe norm controls its real moment. -/
theorem fine_real_moment_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hf0 : ∀ ω, 0 ≤ f ω) (hf : MemLp f 32 μ)
    {T : ℝ} (hT0 : 0 ≤ T)
    (hT : paperENNRealLpNorm μ 32 (fun ω => ENNReal.ofReal (f ω)) ≤ ENNReal.ofReal T) :
    ∫ ω, f ω ^ (32 : ℕ) ∂μ ≤ T^32 := by
  have hi : Integrable (fun ω => f ω ^ (32 : ℕ)) μ := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hf0 _)] using
      hf.integrable_norm_pow (by norm_num : (32 : ℕ) ≠ 0)
  have hb := HistoryLane.lintegral_rpow_le_of_lnorm_le (by norm_num : (0 : ℝ) < 32) hT
  have heq : (∫⁻ ω, ENNReal.ofReal (f ω) ^ (32 : ℝ) ∂μ) =
      ENNReal.ofReal (∫ ω, f ω ^ (32 : ℕ) ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun ω => pow_nonneg (hf0 ω) _)]
    apply lintegral_congr
    intro ω
    simpa only [Real.rpow_ofNat] using
      (ENNReal.ofReal_rpow_of_nonneg (hf0 ω) (by norm_num : (0 : ℝ) ≤ 32))
  rw [heq, ENNReal.ofReal_rpow_of_nonneg hT0 (by norm_num)] at hb
  norm_num only [Real.rpow_ofNat] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (pow_nonneg hT0 _)).mp hb

/-- Sharp sphere control, stated directly as a conditional moment inequality. -/
theorem fine_psd_sphere_lintegral_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {d : ℕ} [NeZero d]
    {N : Ω → Matrix (Fin d) (Fin d) ℝ} (hN : Measurable N)
    (hP : ∀ ω, (N ω).PosSemidef)
    (hm : ∀ e : EuclideanSpace ℝ (Fin d), MemLp (fun ω => sphereQuadratic (N ω) e) 32 μ)
    {T : ℝ} (hT0 : 0 ≤ T)
    (hT : ∀ e : EuclideanSpace ℝ (Fin d), ‖e‖ = 1 →
      paperENNRealLpNorm μ 32 (fun ω => ENNReal.ofReal (sphereQuadratic (N ω) e)) ≤
        ENNReal.ofReal T) :
    (∫⁻ ω, ENNReal.ofReal (‖Matrix.toEuclideanCLM (𝕜 := ℝ) (N ω)‖) ^ (32 : ℝ) ∂μ) ≤
      ENNReal.ofReal (sphereMomentRatio d 32 * T^32) := by
  have hb := fine_psd_sphere_moment_le hN hP hm (fun e he =>
    fine_real_moment_le (fun ω => sphereQuadratic_nonneg (hP ω) e) (hm e) hT0 (hT e he))
  have hi := fine_integrable_opNorm_pow (fun ω => (hP ω).1) hm
  have heq : (∫⁻ ω, ENNReal.ofReal (‖Matrix.toEuclideanCLM (𝕜 := ℝ) (N ω)‖) ^ (32 : ℝ) ∂μ) =
      ENNReal.ofReal (∫ ω, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (N ω)‖ ^ (32 : ℕ) ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun ω => by positivity)]
    apply lintegral_congr
    intro ω
    simpa only [Real.rpow_ofNat] using
      (ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 32))
  rw [heq]
  exact ENNReal.ofReal_le_ofReal hb

end GMCExplicitDelta.Assembly
