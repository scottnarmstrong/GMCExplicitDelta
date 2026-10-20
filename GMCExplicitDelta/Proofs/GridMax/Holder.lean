module

public import GMCExplicitDelta.Proofs.GridMax.Norms

/-! # The two Hölder steps in the whole-sum grid estimate -/

@[expose] public section

open MeasureTheory Real SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

namespace GMCExplicitDelta.Assembly.GridMax

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Assemble the moment and exponential bounds without any independence in space. -/
theorem trial_norm_bound {M R : Ω → ℝ} (hM : Measurable M) (hR : Measurable R)
    (hM0 : ∀ ω, 0 ≤ M ω) (hR0 : ∀ ω, 0 ≤ R ω)
    {D BM BR EM ER : ℝ} (hD : 0 ≤ D) (hBM : 0 ≤ BM) (hBR : 0 ≤ BR)
    (hEM : 0 ≤ EM) (_hER : 0 ≤ ER)
    (hm : paperENNRealLpNorm μ 128 (fun ω => ENNReal.ofReal (M ω)) ≤ ENNReal.ofReal BM)
    (hr : paperENNRealLpNorm μ 128 (fun ω => ENNReal.ofReal (R ω)) ≤ ENNReal.ofReal BR)
    (hem : paperENNRealLpNorm μ 128 (fun ω => ENNReal.ofReal (exp (M ω))) ≤ ENNReal.ofReal EM)
    (her : paperENNRealLpNorm μ 128 (fun ω => ENNReal.ofReal (exp (R ω))) ≤ ENNReal.ofReal ER) :
    paperENNRealLpNorm μ 32 (fun ω =>
      ENNReal.ofReal ((M ω + R ω + D) ^ 2 * exp (M ω + R ω + D) / 2)) ≤
      ENNReal.ofReal ((BM + BR + D) ^ 2 * (exp D * (EM * ER)) / 2) := by
  let T := fun ω => M ω + R ω + D
  have hT : Measurable T := (hM.add hR).add_const D
  have hT0 (ω) : 0 ≤ T ω := add_nonneg (add_nonneg (hM0 ω) (hR0 ω)) hD
  have ht : paperENNRealLpNorm μ 128 (fun ω => ENNReal.ofReal (T ω)) ≤ ENNReal.ofReal (BM + BR + D) := by
    have heq : (fun ω => ENNReal.ofReal (T ω)) = fun ω =>
        ENNReal.ofReal (M ω) + ENNReal.ofReal (R ω) + ENNReal.ofReal D := by
      funext ω
      change ENNReal.ofReal (M ω + R ω + D) = _
      rw [ENNReal.ofReal_add (add_nonneg (hM0 ω) (hR0 ω)) hD,
        ENNReal.ofReal_add (hM0 ω) (hR0 ω)]
    rw [heq]
    refine (HistoryLane.lnorm_add_le (ξ := 128) (by norm_num)
      ((hM.ennreal_ofReal.add hR.ennreal_ofReal).aemeasurable) measurable_const.aemeasurable).trans ?_
    rw [fine_lnorm_const μ (by norm_num : (0 : ℝ) < 128)]
    refine (add_le_add ((HistoryLane.lnorm_add_le (ξ := 128) (by norm_num)
      hM.ennreal_ofReal.aemeasurable hR.ennreal_ofReal.aemeasurable).trans (add_le_add hm hr))
      (le_refl (ENNReal.ofReal D))).trans_eq ?_
    rw [← ENNReal.ofReal_add hBM hBR, ← ENNReal.ofReal_add (add_nonneg hBM hBR) hD]
  have hte : paperENNRealLpNorm μ 64 (fun ω => ENNReal.ofReal (exp (T ω))) ≤
      ENNReal.ofReal (exp D * (EM * ER)) := by
    have heq : (fun ω => ENNReal.ofReal (exp (T ω))) = fun ω =>
        ENNReal.ofReal (exp D) * (ENNReal.ofReal (exp (M ω)) * ENNReal.ofReal (exp (R ω))) := by
      funext ω
      rw [← ENNReal.ofReal_mul (exp_pos _).le, ← ENNReal.ofReal_mul (exp_pos _).le,
        ← exp_add, ← exp_add]
      unfold T
      congr 2
      ring
    rw [heq, HistoryLane.lnorm_const_mul (ξ := 64) (by norm_num) ENNReal.ofReal_ne_top]
    have hx := fine_lnorm_mul_le (μ := μ) (p := 64)
      (X := fun ω => ENNReal.ofReal (exp (M ω))) (Y := fun ω => ENNReal.ofReal (exp (R ω)))
      (by norm_num) hM.exp.ennreal_ofReal.aemeasurable hR.exp.ennreal_ofReal.aemeasurable
    norm_num only [show (2 : ℝ) * 64 = 128 by norm_num] at hx
    refine (mul_le_mul' le_rfl (hx.trans (mul_le_mul' hem her))).trans_eq ?_
    rw [← ENNReal.ofReal_mul hEM, ← ENNReal.ofReal_mul (exp_pos _).le]
  have htsq := fine_lnorm_square_ofReal_le (μ := μ) (f := T) (by norm_num : (0 : ℝ) < 64)
    (add_nonneg (add_nonneg hBM hBR) hD) (by simpa only [show (2 : ℝ) * 64 = 128 by norm_num, abs_of_nonneg (hT0 _)] using ht)
  have heq : (fun ω => ENNReal.ofReal (T ω ^ 2 * exp (T ω) / 2)) = fun ω =>
      ENNReal.ofReal (1 / 2 : ℝ) * (ENNReal.ofReal (T ω ^ 2) * ENNReal.ofReal (exp (T ω))) := by
    funext ω
    rw [← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    congr 1
    ring
  change paperENNRealLpNorm μ 32 (fun ω => ENNReal.ofReal (T ω ^ 2 * exp (T ω) / 2)) ≤ _
  rw [heq, HistoryLane.lnorm_const_mul (ξ := 32) (by norm_num) ENNReal.ofReal_ne_top]
  have hx := fine_lnorm_mul_le (μ := μ) (p := 32)
    (X := fun ω => ENNReal.ofReal (T ω ^ 2)) (Y := fun ω => ENNReal.ofReal (exp (T ω)))
    (by norm_num) (hT.pow_const 2).ennreal_ofReal.aemeasurable hT.exp.ennreal_ofReal.aemeasurable
  norm_num only [show (2 : ℝ) * 32 = 64 by norm_num] at hx
  refine (mul_le_mul' le_rfl (hx.trans (mul_le_mul' htsq hte))).trans_eq ?_
  rw [← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  congr 1
  ring

end GMCExplicitDelta.Assembly.GridMax
