module

public import GMCExplicitDelta.Proofs.FineSensitivity.Holder
public import GMCExplicitDelta.Proofs.FineSensitivity.Band
public import GMCExplicitDelta.Source.SubGaussianMoments

/-! # The moment norms used in G4 -/

@[expose] public section

open MeasureTheory ProbabilityTheory SubdiffusiveProcess.CoarseGrainingVocab
open scoped NNReal ENNReal

namespace GMCExplicitDelta.Assembly

/-- Absolute exponential moment in the paper norm, with its exact factor of two. -/
theorem fine_lnorm_exp_abs_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : Ω → ℝ} {c : ℝ≥0}
    (hZ : HasSubgaussianMGF Z c μ) {q : ℝ} (hq : 0 < q) (t : ℝ) :
    paperENNRealLpNorm μ q (fun ω => ENNReal.ofReal (Real.exp (t * |Z ω|))) ≤
      ENNReal.ofReal ((2 : ℝ) ^ q⁻¹ * Real.exp ((c : ℝ) * q * t ^ 2 / 2)) := by
  have hi : Integrable (fun ω => Real.exp (t * |Z ω|) ^ q) μ := by
    simp_rw [← Real.exp_mul]
    convert Source.integrable_exp_mul_abs_of_subgaussian hZ (q * t) using 1
    funext ω
    congr 1
    ring
  rw [fine_lnorm_ofReal_eq μ hq (fun ω => (Real.exp_pos _).le) hi]
  apply ENNReal.ofReal_le_ofReal
  have hb := Source.integral_exp_mul_abs_le_of_subgaussian hZ (q * t)
  have hroot := Real.rpow_le_rpow (integral_nonneg fun ω => (Real.exp_pos _).le) hb
    (inv_nonneg.mpr hq.le)
  simp_rw [← Real.exp_mul] at *
  have he : (fun ω => Real.exp (t * |Z ω| * q)) =
      (fun ω => Real.exp ((q * t) * |Z ω|)) := by funext ω; congr 1; ring
  rw [he]
  refine hroot.trans_eq ?_
  rw [Real.mul_rpow (by norm_num) (Real.exp_pos _).le, ← Real.exp_mul]
  congr 2
  field_simp

/-- The `L^128` norm of a sub-Gaussian variable in the contract normalization. -/
theorem fine_lnorm_abs128_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : Ω → ℝ} {c : ℝ≥0}
    (hZ : HasSubgaussianMGF Z c μ) (hc : 0 < (c : ℝ)) :
    paperENNRealLpNorm μ 128 (fun ω => ENNReal.ofReal |Z ω|) ≤
      ENNReal.ofReal (Real.sqrt (2 * (c : ℝ)) * Real.sqrt Contract.P32) := by
  have hi : Integrable (fun ω => |Z ω| ^ (128 : ℕ)) μ := by
    simpa only [Real.norm_eq_abs] using (hZ.memLp (128 : ℝ≥0)).integrable_norm_pow
      (by norm_num : (128 : ℕ) ≠ 0)
  have hb := Source.moment_root_le_of_gaussian_tail hZ.aemeasurable
    (Real.sqrt_pos.mpr (show 0 < 2 * (c : ℝ) by positivity)) (by norm_num : 0 < 32)
    (by norm_num; exact hi) (fun u hu => ?_)
  · have hir : Integrable (fun ω => |Z ω| ^ (128 : ℝ)) μ := by
      simpa only [Real.rpow_ofNat] using hi
    rw [fine_lnorm_ofReal_eq μ (by norm_num) (fun ω => abs_nonneg _) hir]
    apply ENNReal.ofReal_le_ofReal
    have hgamma : Real.Gamma (65 : ℝ) = (Nat.factorial 64 : ℝ) :=
      by simpa only [Nat.cast_ofNat, show (64 : ℝ) + 1 = 65 by norm_num] using
        Real.Gamma_nat_eq_factorial 64
    norm_num only [Source.subgaussianMomentFactor, Nat.cast_mul, Nat.cast_ofNat] at hb
    rw [hgamma] at hb
    norm_num only [Contract.P32, Real.rpow_ofNat] at hb ⊢
    exact hb
  · rw [Real.sq_sqrt (show 0 ≤ 2 * (c : ℝ) by positivity)]
    exact Source.measure_abs_ge_le_of_subgaussian hZ hu

/-- Signed exponentials avoid the factor of two in the absolute-exponential bound. -/
theorem fine_lnorm_exp_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : Ω → ℝ} {c : ℝ≥0}
    (hZ : HasSubgaussianMGF Z c μ) {q : ℝ} (hq : 0 < q) (t : ℝ) :
    paperENNRealLpNorm μ q (fun ω => ENNReal.ofReal (Real.exp (t * Z ω))) ≤
      ENNReal.ofReal (Real.exp ((c : ℝ) * q * t ^ 2 / 2)) := by
  have he : (fun ω => Real.exp (t * Z ω) ^ q) =
      (fun ω => Real.exp ((q * t) * Z ω)) := by
    funext ω
    rw [← Real.exp_mul]
    congr 1
    ring
  have hi : Integrable (fun ω => Real.exp (t * Z ω) ^ q) μ := by
    rw [he]
    exact hZ.integrable_exp_mul (q * t)
  rw [fine_lnorm_ofReal_eq μ hq (fun ω => (Real.exp_pos _).le) hi, he]
  apply ENNReal.ofReal_le_ofReal
  have hroot := Real.rpow_le_rpow (integral_nonneg fun ω => (Real.exp_pos _).le)
    (hZ.mgf_le (q * t)) (inv_nonneg.mpr hq.le)
  refine hroot.trans_eq ?_
  rw [← Real.exp_mul]
  congr 1
  field_simp

end GMCExplicitDelta.Assembly
