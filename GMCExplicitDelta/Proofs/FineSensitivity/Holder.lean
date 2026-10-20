module

public import GMCExplicitDelta.HistoryLane.Norm

/-! # Hölder and powers for the paper's nonnegative moment norms -/

@[expose] public section

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

namespace GMCExplicitDelta.Assembly

/-- Hölder with exponents `(2,2)`, retaining the paper norm convention. -/
theorem fine_lnorm_mul_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {p : ℝ} (hp : 0 < p) {X Y : Ω → ℝ≥0∞}
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) :
    paperENNRealLpNorm μ p (fun ω => X ω * Y ω) ≤
      paperENNRealLpNorm μ (2 * p) X * paperENNRealLpNorm μ (2 * p) Y := by
  have hc : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hc
    (hX.pow_const p) (hY.pow_const p)
  have hroot := ENNReal.rpow_le_rpow h (inv_nonneg.mpr hp.le)
  unfold paperENNRealLpNorm
  simp only [Pi.mul_apply, ← ENNReal.rpow_mul] at hroot
  simp only [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  refine hroot.trans_eq ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hp.le)]
  simp only [← ENNReal.rpow_mul]
  congr 2 <;> field_simp

/-- Squaring a random variable doubles the moment exponent. -/
theorem fine_lnorm_sq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {p : ℝ} (hp : 0 < p) (X : Ω → ℝ≥0∞) :
    paperENNRealLpNorm μ p (fun ω => X ω ^ (2 : ℝ)) =
      paperENNRealLpNorm μ (2 * p) X ^ (2 : ℝ) := by
  unfold paperENNRealLpNorm
  simp only [← ENNReal.rpow_mul]
  congr 1
  field_simp

/-- Convert the paper moment of a nonnegative real observable to the real integral formula. -/
theorem fine_lnorm_ofReal_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {p : ℝ} (hp : 0 < p) {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω)
    (hi : Integrable (fun ω => f ω ^ p) μ) :
    paperENNRealLpNorm μ p (fun ω => ENNReal.ofReal (f ω)) =
      ENNReal.ofReal ((∫ ω, f ω ^ p ∂μ) ^ p⁻¹) := by
  unfold paperENNRealLpNorm
  simp_rw [ENNReal.ofReal_rpow_of_nonneg (hf _) hp.le]
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall
    (fun ω => Real.rpow_nonneg (hf ω) p))]
  exact ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun ω => Real.rpow_nonneg (hf ω) p)
    (inv_nonneg.mpr hp.le)

/-- Constants have their usual norm on a probability space. -/
theorem fine_lnorm_const {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {p : ℝ} (hp : 0 < p) (c : ℝ≥0∞) :
    paperENNRealLpNorm μ p (fun _ : Ω => c) = c := by
  unfold paperENNRealLpNorm
  simp only [lintegral_const, measure_univ, mul_one, ← ENNReal.rpow_mul,
    mul_inv_cancel₀ hp.ne', ENNReal.rpow_one]

/-- Transfer a square-root moment estimate to the squared observable. -/
theorem fine_lnorm_square_ofReal_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {p B : ℝ} (hp : 0 < p) {f : Ω → ℝ} (hB : 0 ≤ B)
    (hf : paperENNRealLpNorm μ (2 * p) (fun ω => ENNReal.ofReal |f ω|) ≤ ENNReal.ofReal B) :
    paperENNRealLpNorm μ p (fun ω => ENNReal.ofReal (f ω ^ 2)) ≤ ENNReal.ofReal (B ^ 2) := by
  have he : (fun ω => ENNReal.ofReal |f ω| ^ (2 : ℝ)) =
      (fun ω => ENNReal.ofReal (f ω ^ 2)) := by
    funext ω
    rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num),
      Real.rpow_ofNat, sq_abs]
  rw [← he, fine_lnorm_sq μ hp]
  exact (ENNReal.rpow_le_rpow hf (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by
    rw [ENNReal.ofReal_rpow_of_nonneg hB (by norm_num), Real.rpow_ofNat])

end GMCExplicitDelta.Assembly
