module

public import GMCExplicitDelta.Proofs.HaarMode.Integrals

/-! # Exact means of affine-cutoff components -/

@[expose] public section

open MeasureTheory Homogenization Set

namespace GMCExplicitDelta.Localization

variable {d : ℕ}

/-- The factors in a cutoff-gradient component are continuous. -/
theorem haarMode_gfactor_continuous {ω : ℝ} (h1 : ω ≤ 1 / 2) (i k : Fin d) :
    Continuous (haarMode_atom ω (haarMode_gtype i k)) := by
  classical
  change Continuous (fun t => haarMode_atom ω (haarMode_gtype i k) t)
  by_cases h : k = i
  · norm_num [haarMode_gtype, h, haarMode_atom]
    exact Haar.cutoffSlope_continuous h1
  · norm_num [haarMode_gtype, h, haarMode_atom]
    exact (Haar.cutoffProfile_contDiff h1).continuous

/-- The exact first moment of a gradient factor. -/
theorem haarMode_gfactor_first (row : Contract.Row d) (h0 : 0 < row.omegaEff)
    (h1 : row.omegaEff ≤ 1 / 2) (i k : Fin d) :
    (∫ t in -(1 / 2 : ℝ)..1 / 2, t * haarMode_atom row.omegaEff (haarMode_gtype i k) t) =
      if k = i then -row.cosMean else 0 := by
  classical
  by_cases h : k = i
  · simpa [haarMode_gtype, h, haarMode_atom, Contract.Row.cosMean] using haarMode_moment_slope h0 h1
  · simpa [haarMode_gtype, h, haarMode_atom] using
      haarMode_first_moment_even (fun t => Haar.cutoffProfile_even h1 t)

/-- The affine-cutoff mean is the matching coefficient times the product cutoff mass. -/
theorem haarMode_field_mean (row : Contract.Row d) (h0 : 0 < row.omegaEff)
    (h1 : row.omegaEff ≤ 1 / 2) (n : ℕ) (a : Homogenization.Vec d) (i : Fin d) :
    cubeAverage (originCube d (n : ℤ)) (fun x =>
      vecDot a (fun k => x k / (3 : ℝ) ^ n) *
        haarMode_rawG row.omegaEff (fun k => x k / (3 : ℝ) ^ n) i) =
      -a i * row.cosMean ^ d := by
  classical
  unfold haarMode_rawG
  rw [haarMode_affine_linear (f := fun k => haarMode_atom row.omegaEff (haarMode_gtype i k))]
  · simp_rw [haarMode_gfactor_first row h0 h1]
    rw [Finset.sum_eq_single i]
    · simp only [ite_true]
      have hp : (∏ k ∈ Finset.univ.erase i,
          ∫ t in -(1 / 2 : ℝ)..1 / 2, haarMode_atom row.omegaEff (haarMode_gtype i k) t) =
            row.cosMean ^ (d - 1) := by
        calc
          _ = ∏ _k ∈ Finset.univ.erase i, row.cosMean := by
            apply Finset.prod_congr rfl
            intro k hk
            simpa [haarMode_gtype, Finset.ne_of_mem_erase hk, haarMode_atom] using
              (Haar.cutoff_integrals_row row h0 h1).2.2.1
          _ = _ := by simp
      have hdpos : 1 ≤ d := by have := i.isLt; omega
      have hpow := pow_succ row.cosMean (d - 1)
      rw [Nat.sub_add_cancel hdpos] at hpow
      rw [hp, hpow]
      ring
    · intro k _ hki
      simp [hki]
    · simp
  · intro k
    exact (haarMode_gfactor_continuous h1 i k).intervalIntegrable _ _
  · intro k
    exact (continuous_id.mul (haarMode_gfactor_continuous h1 i k)).intervalIntegrable _ _

/-- The affine factor itself has zero mean on the centered cube. -/
theorem haarMode_affine_mean (n : ℕ) (a : Homogenization.Vec d) :
    cubeAverage (originCube d (n : ℤ)) (fun x => vecDot a x) = 0 := by
  have heq : (fun x => vecDot a x) = (fun x : Homogenization.Vec d =>
      vecDot (fun i => (3 : ℝ) ^ n * a i) (fun i => x i / (3 : ℝ) ^ n) *
        ∏ _k : Fin d, (1 : ℝ)) := by
    funext x
    simp only [Finset.prod_const_one, mul_one, vecDot]
    apply Finset.sum_congr rfl
    intro i _
    field_simp
  rw [heq, haarMode_affine_linear (f := fun _ _ => (1 : ℝ))]
  · simp only [mul_one]
    rw [show (∫ t in -(1 / 2 : ℝ)..1 / 2, t) = 0 from
      haarMode_integral_odd (fun t => by ring)]
    simp
  · intro _
    exact intervalIntegrable_const
  · intro _
    exact (continuous_id.mul continuous_const).intervalIntegrable _ _

end GMCExplicitDelta.Localization
