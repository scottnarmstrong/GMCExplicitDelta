module

public import GMCExplicitDelta.Averaging.SignedSphereTangent
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Algebra.Group.Fin.Basic

/-! # Cyclic symmetrization of signed diagonal Gaussian quadratic forms -/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Set
open scoped BigOperators
open GMCExplicitDelta.Insertion

namespace GMCExplicitDelta.Averaging

/-- A diagonal quadratic form with first coefficient one. -/
noncomputable def signedDiagonalForm {n : ℕ} (a : Fin n → ℝ) (z : ℝ × (Fin n → ℝ)) : ℝ :=
  z.1 ^ 2 + ∑ i, a i * z.2 i ^ 2

/-- Its Gaussian moment of order 32. -/
noncomputable def signedDiagonalMoment {n : ℕ} (a : Fin n → ℝ) : ℝ :=
  ∫ z : ℝ × (Fin n → ℝ), signedDiagonalForm a z ^ 32
    ∂((gaussianReal 0 1).prod (gaussianPi n))

noncomputable def signedMean {n : ℕ} (a : Fin n → ℝ) : ℝ := (∑ i, a i) / n

theorem signedDiagonalForm_abs_le {n : ℕ} (a : Fin n → ℝ) (z : ℝ × (Fin n → ℝ)) :
    |signedDiagonalForm a z| ≤ (1 + ∑ i, |a i|) * (z.1 ^ 2 + sqSum z.2) := by
  have hs : 0 ≤ ∑ i, |a i| := sum_nonneg fun i _ => abs_nonneg _
  have hi (i : Fin n) : |a i| ≤ 1 + ∑ j, |a j| :=
    (single_le_sum (fun j _ => abs_nonneg (a j)) (mem_univ i)).trans (by linarith only [hs])
  calc
    _ ≤ |z.1 ^ 2| + |∑ i, a i * z.2 i ^ 2| := abs_add_le _ _
    _ ≤ z.1 ^ 2 + ∑ i, |a i| * z.2 i ^ 2 := by
      rw [abs_of_nonneg (sq_nonneg _)]
      apply add_le_add le_rfl
      exact (abs_sum_le_sum_abs _ _).trans_eq (by
        apply sum_congr rfl; intro i hi; rw [abs_mul, abs_of_nonneg (sq_nonneg (z.2 i))])
    _ ≤ (1 + ∑ i, |a i|) * z.1 ^ 2 + (1 + ∑ i, |a i|) * sqSum z.2 := by
      apply add_le_add
      · exact le_mul_of_one_le_left (sq_nonneg _) (by linarith only [hs])
      · unfold sqSum
        rw [mul_sum]
        exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hi i) (sq_nonneg _)
    _ = _ := by ring

theorem integrable_signedDiagonalForm_pow {n : ℕ} (a : Fin n → ℝ) :
    Integrable (fun z : ℝ × (Fin n → ℝ) => signedDiagonalForm a z ^ 32)
      ((gaussianReal 0 1).prod (gaussianPi n)) := by
  have hi := (integrable_signedSplit n 1).const_mul ((1 + ∑ i, |a i|) ^ 32)
  refine hi.mono' (by unfold signedDiagonalForm; fun_prop) ?_
  filter_upwards [] with z
  simpa only [Real.norm_eq_abs, abs_pow, mul_pow, one_mul] using
    pow_le_pow_left₀ (abs_nonneg _) (signedDiagonalForm_abs_le a z) 32

/-- Coordinate shifts preserve the product Gaussian law. -/
theorem integral_signedDiagonal_shift {n : ℕ} [NeZero n] (a : Fin n → ℝ) (k : Fin n) :
    (∫ z : ℝ × (Fin n → ℝ),
      (z.1 ^ 2 + ∑ i, a i * z.2 (i + k) ^ 2) ^ 32
      ∂((gaussianReal 0 1).prod (gaussianPi n))) = signedDiagonalMoment a := by
  let e : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) (Equiv.addRight (-k))
  have he (x : Fin n → ℝ) (i : Fin n) : e x i = x (i + k) := by
    have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin n => ℝ) (Equiv.addRight (-k)) x (i + k)
    simpa [e] using h
  have hpi : MeasurePreserving e (gaussianPi n) (gaussianPi n) :=
    measurePreserving_piCongrLeft (fun _ : Fin n => gaussianReal 0 1) (Equiv.addRight (-k))
  have hprod := (MeasurePreserving.id (gaussianReal 0 1)).prod hpi
  have h := hprod.integral_comp (MeasurableEmbedding.id.prodMap e.measurableEmbedding)
    (fun z => signedDiagonalForm a z ^ 32)
  simpa only [signedDiagonalForm, Prod.map_fst, Prod.map_snd, id_eq, he,
    signedDiagonalMoment] using h

/-- The cyclic mean of the complementary quadratic forms replaces every coefficient by its mean. -/
theorem signedDiagonal_cyclic_mean {n : ℕ} [NeZero n] (a : Fin n → ℝ)
    (z : ℝ × (Fin n → ℝ)) :
    (∑ k : Fin n, (n : ℝ)⁻¹ * (z.1 ^ 2 + ∑ i, a i * z.2 (i + k) ^ 2)) =
      z.1 ^ 2 + signedMean a * sqSum z.2 := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hs (i : Fin n) : (∑ k : Fin n, z.2 (i + k) ^ 2) = sqSum z.2 :=
    Equiv.sum_comp (Equiv.addLeft i) (fun k => z.2 k ^ 2)
  rw [← mul_sum, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    sum_comm]
  simp_rw [← mul_sum, hs]
  rw [← sum_mul]
  unfold signedMean
  field_simp

/-- Convexity and Gaussian coordinate symmetry reduce to a common complementary eigenvalue. -/
theorem signedSplitMoment_mean_le {n : ℕ} [NeZero n] (a : Fin n → ℝ) :
    signedSplitMoment n (signedMean a) ≤ signedDiagonalMoment a := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hp : ConvexOn ℝ univ (fun t : ℝ => t ^ 32) := (by decide : Even 32).convexOn_pow
  have hpoint (z : ℝ × (Fin n → ℝ)) :
      (z.1 ^ 2 + signedMean a * sqSum z.2) ^ 32 ≤
        ∑ k : Fin n, (n : ℝ)⁻¹ * (z.1 ^ 2 + ∑ i, a i * z.2 (i + k) ^ 2) ^ 32 := by
    have h := hp.map_sum_le (t := (univ : Finset (Fin n)))
      (w := fun _ => (n : ℝ)⁻¹)
      (p := fun k => z.1 ^ 2 + ∑ i, a i * z.2 (i + k) ^ 2)
      (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
      (by simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_inv_cancel₀ hn])
      (fun _ _ => mem_univ _)
    simpa only [smul_eq_mul, signedDiagonal_cyclic_mean] using h
  have his (k : Fin n) : Integrable
      (fun z : ℝ × (Fin n → ℝ) => (z.1 ^ 2 + ∑ i, a i * z.2 (i + k) ^ 2) ^ 32)
      ((gaussianReal 0 1).prod (gaussianPi n)) := by
    let e : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) :=
      MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) (Equiv.addRight (-k))
    have hpi : MeasurePreserving e (gaussianPi n) (gaussianPi n) :=
      measurePreserving_piCongrLeft (fun _ : Fin n => gaussianReal 0 1) (Equiv.addRight (-k))
    have hp' := (MeasurePreserving.id (gaussianReal 0 1)).prod hpi
    have hi := hp'.integrable_comp_of_integrable (integrable_signedDiagonalForm_pow a)
    have he (x : Fin n → ℝ) (i : Fin n) : e x i = x (i + k) := by
      have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin n => ℝ) (Equiv.addRight (-k)) x (i + k)
      simpa [e] using h
    simpa only [Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq, signedDiagonalForm, he] using hi
  have h := integral_mono (integrable_signedSplit n (signedMean a))
    (integrable_finsetSum univ (fun k _ => (his k).const_mul ((n : ℝ)⁻¹))) hpoint
  unfold signedSplitMoment
  refine h.trans_eq ?_
  rw [integral_finsetSum _ (fun k _ => (his k).const_mul ((n : ℝ)⁻¹))]
  simp_rw [integral_const_mul, integral_signedDiagonal_shift]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

end GMCExplicitDelta.Averaging
