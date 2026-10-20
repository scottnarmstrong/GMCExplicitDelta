module

public import GMCExplicitDelta.Assembly.ModelInduction
public import GMCExplicitDelta.StatementProofs.SourceExpMoment
public import SubdiffusiveProcess.Section3.AnnealedMatrixBounds
public import SubdiffusiveProcess.Section5.HomogenizedCoefficientReciprocalLower
public import SubdiffusiveProcess.CoarseGrainingVocab.DykhneStationaryLimit
public import SubdiffusiveProcess.CoarseGrainingVocab.PlanarStreamFunction

/-! # Normalization drift from annealed coefficient ordering and planar duality -/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta.Assembly

open Contract

variable {d : ℕ}

/-- Positivity directly from the reciprocal lower-bound lemma. -/
theorem driftSeed_ahom_pos (M : SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) : 0 < ahom M m :=
  (Real.exp_pos _).trans_le
    (SubdiffusiveProcess.Section5.homogenized_coefficient_reciprocal_lower M m)

theorem normShift_planar_eq_zero (M : SubdiffusiveProcess.Model.GMCModel 2) (m : ℕ) :
    normShift M m = 0 := by
  have h := ahom_eq_planarLambda_of_streamFunction M m
    planarZeroNormalStreamFunctionOn_openCubeSet_originCube (driftSeed_ahom_pos M m)
  unfold normShift
  rw [h, planarLambda, Real.log_exp]
  ring

/-- Annealed primal/dual ordering controls the logarithmic normalization increment. -/
theorem normShift_increment_le_tau (M : SubdiffusiveProcess.Model.GMCModel d)
    (k m : ℕ) (hkm : k ≤ m) :
    |normShift M m - normShift M k| ≤
      ((m : ℝ) - k) * SubdiffusiveProcess.Model.tauSq M.P := by
  rcases hkm.eq_or_lt with rfl | hkm
  · simp
  have h := SubdiffusiveProcess.Section3.annealed_matrix_bounds.2 M m k hkm
  have hlog1 := Real.log_le_log (driftSeed_ahom_pos M m) h.1
  have hlog2 := Real.log_le_log (driftSeed_ahom_pos M k) h.2
  rw [Real.log_mul (Real.exp_pos _).ne' (driftSeed_ahom_pos M m).ne', Real.log_exp,
    Nat.cast_sub hkm.le] at hlog2
  unfold normShift
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

theorem normShift_abs_le_tau (M : SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) :
    |normShift M m| ≤ ((m : ℝ) + 1) * SubdiffusiveProcess.Model.tauSq M.P := by
  have hlo := SubdiffusiveProcess.Section5.homogenized_coefficient_reciprocal_lower M m
  have hlog := Real.log_le_log (Real.exp_pos _) hlo
  rw [Real.log_exp] at hlog
  have hupper := Real.log_nonpos (driftSeed_ahom_pos M m).le (ahom_le_one M m)
  have ht := M.G4.tauSq_pos.le
  have hT : 0 ≤ ((m : ℝ) + 1) * SubdiffusiveProcess.Model.tauSq M.P := by positivity
  unfold normShift
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

theorem normShift_drift_proof (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (M : SubdiffusiveProcess.Model.GMCModel d) :
    (∀ m, 0 < ahom M m) ∧
      (∀ k m : ℕ, k ≤ m →
        |normShift M m - normShift M k| ≤ kappaH d * ((m : ℝ) - k) * M.delta ^ 2) ∧
      ∀ m : ℕ, |normShift M m| ≤ kappaH d * ((m : ℝ) + 1) * M.delta ^ 2 := by
  refine ⟨driftSeed_ahom_pos M, ?_, ?_⟩
  · intro k m hkm
    by_cases hd2 : d = 2
    · subst d
      simp [normShift_planar_eq_zero, kappaH]
    · have ht := (StatementProofs.source_exp_moment (M := M) (x := 0)).2.2.2.2
      have hb := mul_le_mul_of_nonneg_left ht
        (sub_nonneg.mpr (Nat.cast_le.mpr hkm) : (0 : ℝ) ≤ m - k)
      exact (normShift_increment_le_tau M k m hkm).trans (by
        simpa [kappaH, hd2, kappaQ1, mul_assoc, mul_left_comm, mul_comm] using hb)
  · intro m
    by_cases hd2 : d = 2
    · subst d
      simp [normShift_planar_eq_zero, kappaH]
    · have ht := (StatementProofs.source_exp_moment (M := M) (x := 0)).2.2.2.2
      have hb := mul_le_mul_of_nonneg_left ht (show (0 : ℝ) ≤ m + 1 by positivity)
      exact (normShift_abs_le_tau M m).trans (by
        simpa [kappaH, hd2, kappaQ1, mul_assoc, mul_left_comm, mul_comm] using hb)

end GMCExplicitDelta.Assembly
