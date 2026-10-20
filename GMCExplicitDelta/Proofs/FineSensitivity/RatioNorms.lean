module

public import GMCExplicitDelta.Proofs.FineSensitivity.Arithmetic

/-! # G4: the shifted one-point fresh-ratio norms -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal NNReal

namespace GMCExplicitDelta.Assembly

open Contract

variable {d : ℕ}

theorem fineRatioNorms_proof (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (M : SubdiffusiveProcess.Model.GMCModel d) {k L : ℕ} (hkL : k < L) (x : Homogenization.Vec d) :
    paperENNRealLpNorm M.P.toMeasure 32
        (fun ω => ENNReal.ofReal ((cutoffRatio M k L ω x - 1) ^ 2)) ≤
        ENNReal.ofReal (fineF d M.delta ((L - k : ℕ) : ℝ)) ∧
      paperENNRealLpNorm M.P.toMeasure 32
          (fun ω => ENNReal.ofReal (cutoffRatio M k L ω x + (cutoffRatio M k L ω x)⁻¹ - 2)) ≤
        ENNReal.ofReal (fineG d M.delta ((L - k : ℕ) : ℝ)) := by
  let r : ℝ := ((L - k : ℕ) : ℝ)
  let a : ℝ≥0 := (L - k) • fineSourceProxy M
  let c : ℝ := normShift M L - normShift M k
  let Z := fun ω : SubdiffusiveProcess.Model.PotentialSample d => fineBand k L ω x
  have hr : 1 ≤ r := by dsimp [r]; exact_mod_cast (show 1 ≤ L - k by omega)
  have hδ : 0 < M.delta := M.shellPrefix.delta_pos
  have hκ : 0 ≤ kappaH d := by
    unfold kappaH kappaQ1
    split_ifs <;> norm_num
  have haeq : (a : ℝ) = (proxyA : ℝ) * r * M.delta ^ 2 := by
    change (((L - k) • fineSourceProxy M : ℝ≥0) : ℝ) = _
    rw [NNReal.coe_nsmul]
    change (L - k) • ((proxyA : ℝ) * M.delta ^ 2) = _
    simp only [nsmul_eq_mul]
    dsimp only [r]
    ring
  have hap : 0 < (a : ℝ) := by rw [haeq]; unfold proxyA; positivity
  have hZ : HasSubgaussianMGF Z a M.P.toMeasure := fine_band_hasSubgaussianMGF M k L x
  have hc : |c| ≤ kappaH d * r * M.delta ^ 2 := fine_drift_le row hd hO M hkL.le
  have hS2 : fineAmplitude a ^ 2 = Ch * r * M.delta ^ 2 := by
    rw [fineAmplitude_sq, haeq]
    unfold Ch
    ring
  have hpoly := fine_shift_polynomial_le hδ.le hr (fineAmplitude_nonneg a) hS2 hc
  have hpolyG : (fineAmplitude a + |c|) ^ 2 ≤
      Ch * r * M.delta ^ 2 + AG d M.delta * r ^ 2 :=
    hpoly.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_right (fine_AF_le_AG d hδ.le) (sq_nonneg r)))
  have hEF : |c| + 64 * (a : ℝ) ≤ (kappaH d + 64 * (proxyA : ℝ)) * r * M.delta ^ 2 := by
    rw [haeq]
    nlinarith only [hc]
  have hEG : |c| / 2 + 16 * (a : ℝ) ≤
      (kappaH d / 2 + 16 * (proxyA : ℝ)) * r * M.delta ^ 2 := by
    rw [haeq]
    nlinarith only [hc]
  have hB (t : ℝ) : 0 ≤ Real.exp t * (fineAmplitude a + |c|) :=
    mul_nonneg (Real.exp_pos _).le (add_nonneg (fineAmplitude_nonneg _) (abs_nonneg _))
  have hI := fine_lnorm_square_ofReal_le (p := 32) (by norm_num)
    (hB (|c| + 64 * (a : ℝ)))
    (by simpa only [show (2 : ℝ) * 32 = 64 by norm_num] using
      fine_shifted_increment_norm_le hZ hap c)
  have hG := fine_lnorm_square_ofReal_le (p := 32) (by norm_num)
    (hB (|c| / 2 + 16 * (a : ℝ)))
    (by simpa only [show (2 : ℝ) * 32 = 64 by norm_num] using
      fine_shifted_symmetric_norm_le hZ hap c)
  have hrealF : (Real.exp (|c| + 64 * (a : ℝ)) * (fineAmplitude a + |c|)) ^ 2 ≤
      fineF d M.delta r := by
    rw [mul_pow, ← Real.exp_nat_mul]
    unfold fineF
    apply mul_le_mul _ hpoly (sq_nonneg _) (Real.exp_pos _).le
    apply Real.exp_le_exp.mpr
    norm_num only [Nat.cast_ofNat]
    nlinarith only [hEF]
  have hrealG : (Real.exp (|c| / 2 + 16 * (a : ℝ)) * (fineAmplitude a + |c|)) ^ 2 ≤
      fineG d M.delta r := by
    rw [mul_pow, ← Real.exp_nat_mul]
    unfold fineG
    apply mul_le_mul _ hpolyG (sq_nonneg _) (Real.exp_pos _).le
    apply Real.exp_le_exp.mpr
    norm_num only [Nat.cast_ofNat]
    nlinarith only [hEG]
  constructor
  · simp_rw [cutoffRatio_eq_exp M hkL.le]
    exact hI.trans (ENNReal.ofReal_le_ofReal hrealF)
  · simp_rw [cutoffRatio_eq_exp M hkL.le]
    have he : (fun ω => ENNReal.ofReal
        ((Real.exp (Z ω - c) + (Real.exp (Z ω - c))⁻¹ - 2))) =
        (fun ω => ENNReal.ofReal
          ((Real.exp ((Z ω - c) / 2) - Real.exp (-(Z ω - c) / 2)) ^ 2)) := by
      funext ω
      rw [fine_exp_half_diff_sq, Real.exp_neg]
    change paperENNRealLpNorm M.P.toMeasure 32
      (fun ω => ENNReal.ofReal (Real.exp (Z ω - c) + (Real.exp (Z ω - c))⁻¹ - 2)) ≤ _
    rw [he]
    exact hG.trans (ENNReal.ofReal_le_ofReal hrealG)

end GMCExplicitDelta.Assembly
