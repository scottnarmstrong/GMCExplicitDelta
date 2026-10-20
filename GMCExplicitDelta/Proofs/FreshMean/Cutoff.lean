module

public import GMCExplicitDelta.Proofs.FreshMean.Means

/-! # Fresh-band annealed comparison from the primal and dual cutoff inequalities -/

@[expose] public section

open MeasureTheory Homogenization Homogenization.Book SubdiffusiveProcess.CoarseGrainingVocab

namespace GMCExplicitDelta.Assembly

variable {d : ℕ}

/-- Finite-volume primal and dual comparisons bound both normalized trace energies. -/
theorem freshRet_alpha_beta_cutoff_le (M : SubdiffusiveProcess.Model.GMCModel d)
    (L m n : ℕ) (hLm : L ≤ m) :
    alphaMean M m n ≤ ahom M L / ahom M m * alphaMean M L n ∧
      betaMean M m n ≤ ahom M m / ahom M L *
        Real.exp (2 * SubdiffusiveProcess.Model.tauSq M.P * ((m - L : ℕ) : ℝ)) * betaMean M L n := by
  have haL := driftSeed_ahom_pos M L
  have ham := driftSeed_ahom_pos M m
  have hd : 0 < (d : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension
  rcases hLm.eq_or_lt with rfl | hLm
  · simp [haL.ne']
  have hmat := SubdiffusiveProcess.Providers.Section3.annealed_matrix_bounds.1 M
    (Ch02.cubeDomain (originCube d (n : ℤ))) m L hLm
  constructor
  · rw [freshRet_alpha_eq, freshRet_alpha_eq]
    have ht := freshRet_trace_le hmat.1
    calc
      _ ≤ (Matrix.trace (abar M L (Ch02.cubeDomain (originCube d (n : ℤ)))) / d) / ahom M m :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right ht hd.le) ham.le
      _ = _ := by
        unfold abarScalarReadout
        field_simp [haL.ne', ham.ne', hd.ne']
  · rw [freshRet_beta_eq, freshRet_beta_eq]
    have ht := freshRet_trace_le hmat.2.2.1
    rw [Matrix.trace_smul, smul_eq_mul] at ht
    have hm := mul_le_mul_of_nonneg_left ht
      (Real.exp_pos (2 * SubdiffusiveProcess.Model.tauSq M.P * ((m - L : ℕ) : ℝ))).le
    have hcancel : Real.exp (2 * SubdiffusiveProcess.Model.tauSq M.P * ((m - L : ℕ) : ℝ)) *
        Real.exp (-2 * SubdiffusiveProcess.Model.tauSq M.P * ((m - L : ℕ) : ℝ)) = 1 := by
      rw [← Real.exp_add]
      convert Real.exp_zero using 1
      congr 1
      ring
    rw [← mul_assoc, hcancel, one_mul] at hm
    calc
      _ ≤ ahom M m *
          (Real.exp (2 * SubdiffusiveProcess.Model.tauSq M.P * ((m - L : ℕ) : ℝ)) *
            Matrix.trace (abarStarInv M L (Ch02.cubeDomain (originCube d (n : ℤ))))) / d :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hm ham.le) hd.le
      _ = _ := by field_simp [haL.ne', hd.ne']

/-- The deterministic normalization increment expressed through exponentials. -/
theorem freshRet_exp_normShift_sub (M : SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ) :
    Real.exp (normShift M m - normShift M L) =
      Real.exp (((m : ℝ) - L) * SubdiffusiveProcess.Model.tauSq M.P) * ahom M m / ahom M L := by
  unfold normShift
  have heq : ((m : ℝ) + 1) * SubdiffusiveProcess.Model.tauSq M.P + Real.log (ahom M m) -
      (((L : ℝ) + 1) * SubdiffusiveProcess.Model.tauSq M.P + Real.log (ahom M L)) =
      ((m : ℝ) - L) * SubdiffusiveProcess.Model.tauSq M.P +
        (Real.log (ahom M m) - Real.log (ahom M L)) := by ring
  rw [heq, Real.exp_add, Real.exp_sub, Real.exp_log (driftSeed_ahom_pos M m),
    Real.exp_log (driftSeed_ahom_pos M L)]
  ring

/-- The fresh-field expectation bound before the elementary contract arithmetic. -/
theorem freshRet_fMean_fresh_le (M : SubdiffusiveProcess.Model.GMCModel d)
    (L m n : ℕ) (hLm : L ≤ m) {γ : ℝ}
    (hγ : ((m : ℝ) - L) * SubdiffusiveProcess.Model.tauSq M.P ≤ γ) :
    fMean M m n ≤ Real.exp γ *
      (Real.exp (-(normShift M m - normShift M L)) * alphaMean M L n +
        Real.exp (normShift M m - normShift M L) * betaMean M L n) / 2 - 1 := by
  let t := ((m : ℝ) - L) * SubdiffusiveProcess.Model.tauSq M.P
  let c := normShift M m - normShift M L
  have haL := driftSeed_ahom_pos M L
  have ham := driftSeed_ahom_pos M m
  have hE := freshRet_exp_normShift_sub M L m
  change Real.exp c = Real.exp t * ahom M m / ahom M L at hE
  have hr1 : ahom M L / ahom M m = Real.exp t * Real.exp (-c) := by
    rw [Real.exp_neg, hE]
    field_simp [haL.ne', ham.ne', (Real.exp_pos t).ne']
  have hr2 : ahom M m / ahom M L *
      Real.exp (2 * SubdiffusiveProcess.Model.tauSq M.P * ((m - L : ℕ) : ℝ)) =
        Real.exp t * Real.exp c := by
    rw [hE, Nat.cast_sub hLm]
    have he : Real.exp (2 * SubdiffusiveProcess.Model.tauSq M.P * ((m : ℝ) - L)) =
        Real.exp t * Real.exp t := by
      rw [← Real.exp_add]
      congr 1
      dsimp [t]
      ring
    rw [he]
    ring
  obtain ⟨hα, hβ⟩ := freshRet_alpha_beta_cutoff_le M L m n hLm
  rw [hr1] at hα
  rw [hr2] at hβ
  have hsum : alphaMean M m n + betaMean M m n ≤
      Real.exp t * (Real.exp (-c) * alphaMean M L n + Real.exp c * betaMean M L n) := by
    nlinarith only [hα, hβ]
  have hpos := freshRet_alpha_beta_ge_one M L n
  have hp : 0 ≤ Real.exp (-c) * alphaMean M L n + Real.exp c * betaMean M L n := by
    have ha : 0 ≤ alphaMean M L n := le_trans (by norm_num) hpos.1
    have hb : 0 ≤ betaMean M L n := le_trans (by norm_num) hpos.2
    positivity
  have hexp := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hγ) hp
  unfold fMean
  dsimp [c] at hsum hexp
  linarith only [hsum, hexp]

end GMCExplicitDelta.Assembly
