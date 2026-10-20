module

public import GMCExplicitDelta.Haar.CutoffProfile
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-! The finite-product “exactly one failure” estimate in H7. -/
@[expose] public section

namespace GMCExplicitDelta.Haar

open scoped BigOperators

/-- The probabilities of all successes and exactly one failure have sum at most one. -/
theorem one_failure_add_all_success_le_one {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℝ) (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1) :
    (∑ i ∈ s, (1 - p i) * ∏ j ∈ s.erase i, p j) + ∏ i ∈ s, p i ≤ 1 := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Finset.prod_empty, zero_add, le_refl]
  | @insert a s ha ih =>
    have h0 : ∀ i ∈ s, 0 ≤ p i := fun i hi => hp0 i (Finset.mem_insert_of_mem hi)
    have h1 : ∀ i ∈ s, p i ≤ 1 := fun i hi => hp1 i (Finset.mem_insert_of_mem hi)
    have hpa1 := hp1 a (Finset.mem_insert_self a s)
    have hsum0 : 0 ≤ ∑ i ∈ s, (1 - p i) * ∏ j ∈ s.erase i, p j := by
      apply Finset.sum_nonneg
      intro i hi
      exact mul_nonneg (sub_nonneg.mpr (h1 i hi))
        (Finset.prod_nonneg (fun j hj => h0 j (Finset.mem_of_mem_erase hj)))
    have heq : (∑ i ∈ s, (1 - p i) * ∏ j ∈ (insert a s).erase i, p j) =
        p a * ∑ i ∈ s, (1 - p i) * ∏ j ∈ s.erase i, p j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hai : a ≠ i := by
        intro h
        subst i
        exact ha hi
      rw [Finset.erase_insert_of_ne hai,
        Finset.prod_insert (by simp only [Finset.mem_erase, not_and]; exact fun _ h => ha h)]
      ring
    rw [Finset.sum_insert ha, Finset.erase_insert ha, heq, Finset.prod_insert ha]
    have hih := ih h0 h1
    have hmul := mul_nonneg (sub_nonneg.mpr hpa1) hsum0
    nlinarith only [hih, hmul]

theorem one_failure_le_one {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℝ) (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1) :
    (∑ i ∈ s, (1 - p i) * ∏ j ∈ s.erase i, p j) ≤ 1 := by
  have h := one_failure_add_all_success_le_one s p hp0 hp1
  have hprod := Finset.prod_nonneg hp0
  linarith only [h, hprod]

/-- The tensor product cutoff in H7. -/
noncomputable def cutoffProduct {d : ℕ} (ω : ℝ) (x : Fin d → ℝ) : ℝ :=
  ∏ i, cutoffProfile ω (x i)

/-- Explicit components of its gradient. -/
noncomputable def cutoffGradient {d : ℕ} (ω : ℝ) (x : Fin d → ℝ) (i : Fin d) : ℝ :=
  cutoffSlope ω (x i) * ∏ j ∈ Finset.univ.erase i, cutoffProfile ω (x j)

/-- The formula used for the gradient really is the coordinate derivative. -/
theorem cutoffProduct_hasDerivAt_update {d : ℕ} {ω : ℝ} (hω : ω ≤ 1 / 2)
    (x : Fin d → ℝ) (i : Fin d) :
    HasDerivAt (fun y => cutoffProduct ω (Function.update x i y)) (cutoffGradient ω x i) (x i) := by
  have heq : (fun y => cutoffProduct ω (Function.update x i y)) =
      (fun y => cutoffProfile ω y * ∏ j ∈ Finset.univ.erase i, cutoffProfile ω (x j)) := by
    funext y
    unfold cutoffProduct
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [heq]
  exact (cutoffProfile_hasDerivAt hω (x i)).mul_const _

/-- The “exactly one failure” identity for the squared gradient. -/
theorem cutoffGradient_sq_sum {d : ℕ} (ω : ℝ) (x : Fin d → ℝ) :
    (∑ i, cutoffGradient ω x i ^ 2) = (Real.pi / (2 * ω)) ^ 2 *
      ∑ i, (1 - cutoffProfile ω (x i) ^ 2) *
        ∏ j ∈ Finset.univ.erase i, cutoffProfile ω (x j) ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold cutoffGradient
  rw [mul_pow, cutoffSlope_sq, Finset.prod_pow]
  ring

/-- H7's dimension-independent pointwise gradient bound. -/
theorem cutoffGradient_sq_sum_le {d : ℕ} {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1 / 2)
    (x : Fin d → ℝ) (hx : ∀ i, |x i| ≤ 1 / 2) :
    (∑ i, cutoffGradient ω x i ^ 2) ≤ (Real.pi / (2 * ω)) ^ 2 := by
  rw [cutoffGradient_sq_sum]
  have h := one_failure_le_one Finset.univ (fun i => cutoffProfile ω (x i) ^ 2)
    (fun i _ => sq_nonneg _) (fun i _ => by
      obtain ⟨h0, h1⟩ := cutoffProfile_bounds hω0 hω1 (hx i)
      exact pow_le_one₀ h0 h1)
  exact (mul_le_mul_of_nonneg_left h (sq_nonneg _)).trans_eq (mul_one _)

/-- The contract uses the same κ as the analytic cutoff. -/
theorem cutoffGradient_sq_sum_le_kappaOmega {d : ℕ} (row : Contract.Row d)
    (hω0 : 0 < row.omegaEff) (hω1 : row.omegaEff ≤ 1 / 2)
    (x : Fin d → ℝ) (hx : ∀ i, |x i| ≤ 1 / 2) :
    (∑ i, cutoffGradient row.omegaEff x i ^ 2) ≤ row.kappaOmega ^ 2 :=
  cutoffGradient_sq_sum_le hω0 hω1 x hx

theorem cutoffProduct_bounds {d : ℕ} {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1 / 2)
    (x : Fin d → ℝ) (hx : ∀ i, |x i| ≤ 1 / 2) :
    0 ≤ cutoffProduct ω x ∧ cutoffProduct ω x ≤ 1 := by
  constructor
  · exact Finset.prod_nonneg (fun i _ => (cutoffProfile_bounds hω0 hω1 (hx i)).1)
  · exact Finset.prod_le_one₀ (fun i _ => (cutoffProfile_bounds hω0 hω1 (hx i)).1)
      (fun i _ => (cutoffProfile_bounds hω0 hω1 (hx i)).2)

theorem cutoffProduct_eq_zero_of_face {d : ℕ} {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1 / 2)
    (x : Fin d → ℝ) (hface : ∃ i, x i = 1 / 2 ∨ x i = -(1 / 2)) :
    cutoffProduct ω x = 0 := by
  obtain ⟨i, hi⟩ := hface
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rcases hi with hi | hi
  · rw [hi]
    exact (cutoffProfile_endpoint hω0 hω1).1
  · rw [hi]
    exact (cutoffProfile_endpoint hω0 hω1).2

end GMCExplicitDelta.Haar
