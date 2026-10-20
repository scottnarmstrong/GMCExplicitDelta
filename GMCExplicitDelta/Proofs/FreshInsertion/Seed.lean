module

public import GMCExplicitDelta.Insertion.FreshSeedNorm
public import GMCExplicitDelta.Proofs.FreshInsertion.BandSeries
public import GMCExplicitDelta.Proofs.Normalization.Drift

@[expose] public section

open Homogenization Homogenization.Book.Ch02
open SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab (paperENNRealLpNorm normalizedDefect ahom)

namespace GMCExplicitDelta.Assembly

open Contract

/-- K2 with the positivity and drift conclusions supplied by the separately owned N1/N2 target. -/
theorem normSeed_bound_of_normShift {d : ℕ} [NeZero d] (row : Row d) (M : GMCModel d)
    (m : ℕ) (hm : m + 1 ≤ row.h) (hpos : 0 < ahom M m)
    (hshift : |normShift M m| ≤ kappaH d * ((m : ℝ) + 1) * M.delta ^ 2)
    (n : ℕ) (z : Vec d) :
    paperENNRealLpNorm M.P.toMeasure 32 (normalizedDefect M m (cubeAt z n)) ≤
      ENNReal.ofReal (row.seed M.delta) := by
  have hκ : (0 : ℝ) ≤ (kappaQ1 : ℝ) := by norm_num [kappaQ1]
  have hγ : 0 ≤ row.gammaH M.delta := by
    unfold Row.gammaH
    positivity
  have hpoint : Real.cosh |normShift M m| - 1 ≤ row.seedPoint M.delta := by
    by_cases hd : d = 2
    · have hz : normShift M m = 0 := abs_eq_zero.mp
        (le_antisymm (by simpa only [kappaH, ite_eq_left hd, zero_mul] using hshift) (abs_nonneg _))
      simp only [Row.seedPoint, ite_eq_left hd, hz, abs_zero, Real.cosh_zero, sub_self, le_refl]
    · have hcast : (m : ℝ) + 1 ≤ (row.h : ℝ) := by exact_mod_cast hm
      have hbound : |normShift M m| ≤ row.gammaH M.delta := by
        calc
          _ ≤ (kappaQ1 : ℝ) * ((m : ℝ) + 1) * M.delta ^ 2 := by
            simpa only [kappaH, ite_eq_right hd] using hshift
          _ ≤ (kappaQ1 : ℝ) * (row.h : ℝ) * M.delta ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcast hκ) (sq_nonneg _)
          _ = _ := rfl
      simp only [Row.seedPoint, ite_eq_right hd]
      apply sub_le_sub_right
      apply Real.cosh_le_cosh.mpr
      simpa only [abs_abs, abs_of_nonneg hγ] using hbound
  have hB0 : 0 ≤ bandSeriesEval M.delta (m + 1) (Real.cosh |normShift M m| - 1) := by
    apply tsum_nonneg
    intro k
    exact mul_nonneg
      (mul_nonneg (pow_nonneg (sq_nonneg _) _) (bandSeries_pow_coeff_bounds _ _).1)
      (Insertion.coshL_pow_eval_nonneg k 32 (sub_nonneg.mpr (Real.one_le_cosh _)))
  have hmono := Insertion.bandSeriesEval_mono M.delta hm
    (sub_nonneg.mpr (Real.one_le_cosh |normShift M m|)) hpoint
  have hn := normalizedDefect_norm_le_band M m (cubeAt z n) hpos
  refine hn.trans (ENNReal.ofReal_le_ofReal ?_)
  unfold Row.seed
  rw [← bandSeriesEval_eq_sum_proof]
  exact Real.rpow_le_rpow hB0 hmono (by norm_num)

/-- K2: the affine seed bound with normalization drift supplied by N1/N2. -/
theorem normSeed_bound_proof {d : ℕ} (row : Row d)
    (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (M : SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) (hm : m + 1 ≤ row.h) :
    ∀ n, m ≤ n → ∀ z : Homogenization.Vec d,
      paperENNRealLpNorm M.P.toMeasure 32 (normalizedDefect M m (cubeAt z n)) ≤
        ENNReal.ofReal (row.seed M.delta) := by
  have hd0 : d ≠ 0 := by simp only [Finset.mem_insert, Finset.mem_singleton] at hd; omega
  let : NeZero d := ⟨hd0⟩
  have h := normShift_drift_proof row hd hO M
  intro n _hn z
  exact normSeed_bound_of_normShift row M m hm (h.1 m) (h.2.2 m) n z

end GMCExplicitDelta.Assembly
