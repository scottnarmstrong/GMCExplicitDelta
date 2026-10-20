module

public import GMCExplicitDelta.Proofs.HaarMode.Curvature
public import GMCExplicitDelta.Proofs.HaarMode.Quadratic
public import Mathlib.Tactic.FinCases

/-! # Moment tables for the cutoff, its slope, and its curvature -/

@[expose] public section

open MeasureTheory Homogenization Set Filter Real
open scoped ENNReal

namespace GMCExplicitDelta.Localization

/-- Scalar factors in the cutoff Hessian: profile, slope, and curvature. -/
noncomputable def haarMode_atom (ω : ℝ) (b : Fin 3) (t : ℝ) : ℝ :=
  if b = 0 then Haar.cutoffProfile ω t else if b = 1 then Haar.cutoffSlope ω t else haarMode_curvature ω t

/-- Every scalar factor is measurable. -/
theorem haarMode_atom_measurable {ω : ℝ} (hω : ω ≤ 1 / 2) (b : Fin 3) :
    Measurable (haarMode_atom ω b) := by
  have hcurv : Measurable (haarMode_curvature ω) :=
    measurable_const.mul (Measurable.ite (isOpen_lt continuous_const continuous_abs).measurableSet
      (Haar.cutoffProfile_contDiff hω).continuous.measurable measurable_const)
  fin_cases b <;> norm_num [haarMode_atom] <;>
    first | exact (Haar.cutoffProfile_contDiff hω).continuous.measurable
          | exact (Haar.cutoffSlope_continuous hω).measurable
          | exact hcurv

/-- A uniform bound for all scalar factors. -/
theorem haarMode_atom_abs_le (ω t : ℝ) (b : Fin 3) :
    |haarMode_atom ω b t| ≤ max 1 (max |π / (2 * ω)| ((π / (2 * ω)) ^ 2)) := by
  have hcurv : |haarMode_curvature ω t| ≤ (π / (2 * ω)) ^ 2 := by
    unfold haarMode_curvature
    split_ifs
    · rw [abs_mul, abs_neg, abs_sq]
      exact (mul_le_mul_of_nonneg_left (haarMode_profile_abs_le_one ω t) (sq_nonneg _)).trans_eq (mul_one _)
    · simp only [mul_zero, abs_zero]
      exact sq_nonneg _
  fin_cases b <;> norm_num [haarMode_atom]
  · exact Or.inl (haarMode_profile_abs_le_one ω t)
  · exact Or.inr (Or.inl (haarMode_slope_abs_le ω t))
  · exact Or.inr (Or.inr hcurv)

/-- All polynomial moments of pairs of scalar factors are integrable on the unit interval. -/
theorem haarMode_atom_pair_integrable {ω : ℝ} (hω : ω ≤ 1 / 2) (b c : Fin 3) (r : ℕ) :
    IntervalIntegrable (fun t => t ^ r * (haarMode_atom ω b t * haarMode_atom ω c t)) volume
      (-(1 / 2 : ℝ)) (1 / 2) := by
  let C := max 1 (max |π / (2 * ω)| ((π / (2 * ω)) ^ 2))
  have hC : 0 ≤ C := zero_le_one.trans (le_max_left _ _)
  have hmeas : Measurable (fun t => t ^ r * (haarMode_atom ω b t * haarMode_atom ω c t)) :=
    (measurable_id.pow_const r).mul ((haarMode_atom_measurable hω b).mul (haarMode_atom_measurable hω c))
  have hi : MemLp (fun t => t ^ r * (haarMode_atom ω b t * haarMode_atom ω c t)) 1
      (volume.restrict (Ioc (-(1 / 2 : ℝ)) (1 / 2))) := MemLp.of_bound hmeas.aestronglyMeasurable (C * C) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow]
    have ht1 : |t| ≤ 1 := abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hp : |t| ^ r ≤ 1 := pow_le_one₀ (abs_nonneg _) ht1
    have hab := mul_le_mul (haarMode_atom_abs_le ω t b) (haarMode_atom_abs_le ω t c) (abs_nonneg _) hC
    exact (mul_le_mul hp hab (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by norm_num)).trans_eq (one_mul _))
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).2
    (hi.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 1))

/-- Zeroth moments of squared scalar factors. -/
noncomputable def haarMode_m0 {d : ℕ} (row : Contract.Row d) (b : Fin 3) : ℝ :=
  if b = 0 then row.cosA else if b = 1 then row.cosB else row.kappaOmega ^ 4 * row.omegaEff

/-- Second moments of squared scalar factors. -/
noncomputable def haarMode_m2 {d : ℕ} (row : Contract.Row d) (b : Fin 3) : ℝ :=
  if b = 0 then row.cosC else if b = 1 then row.cosE else row.kappaOmega ^ 4 * row.cosCstar

/-- The exact zeroth moment table. -/
theorem haarMode_atom_sq_integral {d : ℕ} (row : Contract.Row d)
    (hω0 : 0 < row.omegaEff) (hω1 : row.omegaEff ≤ 1 / 2) (b : Fin 3) :
    (∫ t in -(1 / 2 : ℝ)..1 / 2, haarMode_atom row.omegaEff b t ^ 2) = haarMode_m0 row b := by
  fin_cases b <;> norm_num [haarMode_atom, haarMode_m0]
  · exact (Haar.cutoff_integrals_row row hω0 hω1).1
  · exact (Haar.cutoff_integrals_row row hω0 hω1).2.1
  · exact haarMode_curvature_sq_integral hω0 hω1

/-- The exact second moment table. -/
theorem haarMode_atom_sq_moment {d : ℕ} (row : Contract.Row d)
    (hω0 : 0 < row.omegaEff) (hω1 : row.omegaEff ≤ 1 / 2) (b : Fin 3) :
    (∫ t in -(1 / 2 : ℝ)..1 / 2, t ^ 2 * haarMode_atom row.omegaEff b t ^ 2) = haarMode_m2 row b := by
  fin_cases b <;> norm_num [haarMode_atom, haarMode_m2]
  · exact (Haar.cutoff_integrals_row row hω0 hω1).2.2.2.2.1
  · exact (Haar.cutoff_integrals_row row hω0 hω1).2.2.2.2.2.1
  · exact haarMode_curvature_sq_moment hω0 hω1

/-- Every squared scalar factor is even, so its first moment vanishes. -/
theorem haarMode_atom_sq_first {ω : ℝ} (hω : ω ≤ 1 / 2) (b : Fin 3) :
    (∫ t in -(1 / 2 : ℝ)..1 / 2, t * haarMode_atom ω b t ^ 2) = 0 := by
  fin_cases b <;> norm_num [haarMode_atom]
  · exact haarMode_profile_sq_first hω
  · exact haarMode_slope_sq_first hω
  · exact haarMode_first_moment_even (fun t => by rw [haarMode_curvature_even hω])

/-- Zeroth moments of pairs of scalar factors. -/
noncomputable def haarMode_mix0 {d : ℕ} (row : Contract.Row d) (b c : Fin 3) : ℝ :=
  if b = c then haarMode_m0 row b else
    if (b = 0 ∧ c = 2) ∨ (b = 2 ∧ c = 0) then -row.kappaOmega ^ 2 * row.omegaEff else 0

/-- First moments of pairs of scalar factors. -/
noncomputable def haarMode_mix1 {d : ℕ} (row : Contract.Row d) (b c : Fin 3) : ℝ :=
  if (b = 0 ∧ c = 1) ∨ (b = 1 ∧ c = 0) then -row.cosA / 2 else
    if (b = 1 ∧ c = 2) ∨ (b = 2 ∧ c = 1) then row.kappaOmega ^ 2 * row.cosA / 2 else 0

/-- Exact zeroth moments of all scalar-factor pairs. -/
theorem haarMode_atom_pair_integral {d : ℕ} (row : Contract.Row d)
    (hω0 : 0 < row.omegaEff) (hω1 : row.omegaEff ≤ 1 / 2) (b c : Fin 3) :
    (∫ t in -(1 / 2 : ℝ)..1 / 2, haarMode_atom row.omegaEff b t * haarMode_atom row.omegaEff c t) =
      haarMode_mix0 row b c := by
  have h01 : (∫ t in -(1 / 2 : ℝ)..1 / 2,
      Haar.cutoffProfile row.omegaEff t * Haar.cutoffSlope row.omegaEff t) = 0 :=
    haarMode_integral_odd (fun t => by rw [Haar.cutoffProfile_even hω1, haarMode_slope_odd hω1]; ring)
  have h12 : (∫ t in -(1 / 2 : ℝ)..1 / 2,
      Haar.cutoffSlope row.omegaEff t * haarMode_curvature row.omegaEff t) = 0 :=
    haarMode_integral_odd (fun t => by rw [haarMode_curvature_even hω1, haarMode_slope_odd hω1]; ring)
  fin_cases b <;> fin_cases c <;> norm_num [haarMode_atom, haarMode_mix0, haarMode_m0, ← sq]
  · exact (Haar.cutoff_integrals_row row hω0 hω1).1
  · exact h01
  · simpa only [Contract.Row.kappaOmega, neg_mul] using haarMode_profile_curvature_integral hω0 hω1
  · simpa only [mul_comm] using h01
  · exact (Haar.cutoff_integrals_row row hω0 hω1).2.1
  · exact h12
  · simpa only [mul_comm, Contract.Row.kappaOmega, neg_mul, mul_neg] using haarMode_profile_curvature_integral hω0 hω1
  · simpa only [mul_comm] using h12
  · exact haarMode_curvature_sq_integral hω0 hω1

/-- Exact first moments of all scalar-factor pairs. -/
theorem haarMode_atom_pair_moment {d : ℕ} (row : Contract.Row d)
    (hω0 : 0 < row.omegaEff) (hω1 : row.omegaEff ≤ 1 / 2) (b c : Fin 3) :
    (∫ t in -(1 / 2 : ℝ)..1 / 2, t * (haarMode_atom row.omegaEff b t * haarMode_atom row.omegaEff c t)) =
      haarMode_mix1 row b c := by
  have h02 : (∫ t in -(1 / 2 : ℝ)..1 / 2,
      t * (Haar.cutoffProfile row.omegaEff t * haarMode_curvature row.omegaEff t)) = 0 :=
    haarMode_first_moment_even (fun t => by rw [Haar.cutoffProfile_even hω1, haarMode_curvature_even hω1])
  fin_cases b <;> fin_cases c <;> norm_num [haarMode_atom, haarMode_mix1, ← sq]
  · exact haarMode_profile_sq_first hω1
  · simpa only [← mul_assoc, Contract.Row.cosA] using haarMode_profile_slope_moment hω0 hω1
  · exact h02
  · simpa only [mul_comm (Haar.cutoffSlope row.omegaEff _) (Haar.cutoffProfile row.omegaEff _),
      ← mul_assoc, Contract.Row.cosA] using haarMode_profile_slope_moment hω0 hω1
  · exact haarMode_slope_sq_first hω1
  · simpa only [← mul_assoc, Contract.Row.cosA, Contract.Row.kappaOmega] using haarMode_slope_curvature_moment hω0 hω1
  · simpa only [mul_comm (haarMode_curvature row.omegaEff _) (Haar.cutoffProfile row.omegaEff _)] using h02
  · simpa only [mul_comm (haarMode_curvature row.omegaEff _) (Haar.cutoffSlope row.omegaEff _),
      ← mul_assoc, Contract.Row.cosA, Contract.Row.kappaOmega] using haarMode_slope_curvature_moment hω0 hω1
  · exact haarMode_first_moment_even (fun t => by rw [haarMode_curvature_even hω1])

end GMCExplicitDelta.Localization
