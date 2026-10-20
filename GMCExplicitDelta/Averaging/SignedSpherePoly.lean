module

public import GMCExplicitDelta.Contract.DerivedAveraging
public import GMCExplicitDelta.Insertion.SphereRadial

/-!
# Gaussian representation of the signed sphere polynomial

`Contract.spherePoly` has rational input. We extend its rational coefficients
to a real polynomial and prove agreement at rational inputs. A vector in
dimension `n+1` is represented by its first coordinate and `n` independent
remaining Gaussian coordinates; `sqSum` is squared Euclidean length.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped Nat NNReal ENNReal BigOperators
open GMCExplicitDelta.Insertion

namespace GMCExplicitDelta.Averaging

/-- Real coefficient extension of the Contract sphere polynomial. -/
noncomputable def spherePolyReal (d : ℕ) (lam : ℝ) : ℝ :=
  ∑ j ∈ range 33, (Contract.spherePolyCoeff d j : ℝ) * lam ^ (32 - j)

/-- Real coefficient extension of the Contract derivative polynomial. -/
noncomputable def spherePolyDerivReal (d : ℕ) (lam : ℝ) : ℝ :=
  ∑ j ∈ range 32, (Contract.spherePolyCoeff d j : ℝ) * (32 - j : ℕ) * lam ^ (31 - j)

theorem spherePolyReal_rat (d : ℕ) (lam : ℚ) :
    spherePolyReal d (lam : ℝ) = (Contract.spherePoly d lam : ℝ) := by
  simp only [spherePolyReal, Contract.spherePoly, Rat.cast_sum, Rat.cast_mul, Rat.cast_pow]

theorem spherePolyDerivReal_rat (d : ℕ) (lam : ℚ) :
    spherePolyDerivReal d (lam : ℝ) = (Contract.spherePolyDeriv d lam : ℝ) := by
  simp only [spherePolyDerivReal, Contract.spherePolyDeriv, Rat.cast_sum, Rat.cast_mul,
    Rat.cast_pow, Rat.cast_natCast]

/-- The Gaussian quadratic-form moment with one distinguished eigenvalue 1. -/
noncomputable def signedSplitMoment (n : ℕ) (lam : ℝ) : ℝ :=
  ∫ z : ℝ × (Fin n → ℝ), (z.1 ^ 2 + lam * sqSum z.2) ^ 32
    ∂((gaussianReal 0 1).prod (gaussianPi n))

theorem signedSplit_pow_eq_sum {n : ℕ} (lam : ℝ) (z : ℝ × (Fin n → ℝ)) :
    (z.1 ^ 2 + lam * sqSum z.2) ^ 32 =
      ∑ j ∈ range 33, (Nat.choose 32 j : ℝ) * lam ^ (32 - j) *
        (z.1 ^ (2 * j) * sqSum z.2 ^ (32 - j)) := by
  rw [add_pow]
  apply sum_congr rfl
  intro j hj
  rw [mul_pow, ← pow_mul]
  ring

theorem integrable_signedSplit_term (n j : ℕ) (lam : ℝ) :
    Integrable (fun z : ℝ × (Fin n → ℝ) =>
      (Nat.choose 32 j : ℝ) * lam ^ (32 - j) *
        (z.1 ^ (2 * j) * sqSum z.2 ^ (32 - j)))
      ((gaussianReal 0 1).prod (gaussianPi n)) :=
  ((integrable_gaussianReal_even j).mul_prod (integrable_sqSum_pow n (32 - j))).const_mul _

theorem integrable_signedSplit (n : ℕ) (lam : ℝ) :
    Integrable (fun z : ℝ × (Fin n → ℝ) => (z.1 ^ 2 + lam * sqSum z.2) ^ 32)
      ((gaussianReal 0 1).prod (gaussianPi n)) := by
  simp_rw [signedSplit_pow_eq_sum]
  exact integrable_finsetSum _ fun j _ => integrable_signedSplit_term n j lam

theorem signedSplitMoment_eq_sum (n : ℕ) (lam : ℝ) :
    signedSplitMoment n lam = ∑ j ∈ range 33,
      (Nat.choose 32 j : ℝ) * lam ^ (32 - j) *
        (radialMoment 1 j * radialMoment n (32 - j)) := by
  unfold signedSplitMoment
  simp_rw [signedSplit_pow_eq_sum]
  rw [integral_finsetSum _ (fun j _ => integrable_signedSplit_term n j lam)]
  apply sum_congr rfl
  intro j hj
  rw [integral_const_mul,
    integral_prod_mul (fun x : ℝ => x ^ (2 * j)) (fun x : Fin n → ℝ => sqSum x ^ (32 - j)),
    integral_pow_gaussianReal_even, integral_sqSum_pow, radialMoment_one]

/-- Rising factorials and the radial Gaussian moment have the same normalization. -/
theorem risingQ_half_cast (d p : ℕ) :
    (2 : ℝ) ^ p * (Contract.risingQ ((d : ℚ) / 2) p : ℝ) = radialMoment d p := by
  unfold Contract.risingQ radialMoment
  push_cast
  rw [show (2 : ℝ) ^ p = ∏ _j ∈ range p, (2 : ℝ) by simp, ← prod_mul_distrib]
  apply prod_congr rfl
  intro j hj
  ring

theorem radialMoment_pos {a : ℝ} (ha : 0 < a) (p : ℕ) : 0 < radialMoment a p := by
  unfold radialMoment
  apply prod_pos
  intro j hj
  positivity

/-- Identification of each Contract coefficient with the corresponding Gaussian moment. -/
theorem spherePolyCoeff_gaussian (n j : ℕ) (hj : j ≤ 32) :
    radialMoment ((n + 1 : ℕ) : ℝ) 32 * (Contract.spherePolyCoeff (n + 1) j : ℝ) =
      (Nat.choose 32 j : ℝ) * radialMoment 1 j * radialMoment n (32 - j) := by
  have hhalf : (((n + 1 : ℕ) : ℚ) - 1) / 2 = (n : ℚ) / 2 := by push_cast; ring
  have hone := risingQ_half_cast 1 j
  norm_num only [Nat.cast_one] at hone
  have hn := risingQ_half_cast n (32 - j)
  have hd := risingQ_half_cast (n + 1) 32
  have hp : (2 : ℝ) ^ j * 2 ^ (32 - j) = 2 ^ 32 := by
    rw [← pow_add, Nat.add_sub_of_le hj]
  have hden : (Contract.risingQ (((n + 1 : ℕ) : ℚ) / 2) 32 : ℝ) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hd
    exact (ne_of_gt (radialMoment_pos (by positivity : (0 : ℝ) < (n + 1 : ℕ)) 32)) hd.symm
  unfold Contract.spherePolyCoeff
  rw [hhalf]
  rw [← hd]
  push_cast at hden ⊢
  field_simp
  rw [← hone, ← hn, ← hp]
  ring

/-- Gaussian representation of the sphere polynomial in dimension `n+1`. -/
theorem signedSplitMoment_eq_spherePoly (n : ℕ) (lam : ℝ) :
    signedSplitMoment n lam = radialMoment ((n + 1 : ℕ) : ℝ) 32 * spherePolyReal (n + 1) lam := by
  rw [signedSplitMoment_eq_sum]
  unfold spherePolyReal
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  have hj' : j ≤ 32 := by have := mem_range.mp hj; omega
  calc
    _ = ((Nat.choose 32 j : ℝ) * radialMoment 1 j * radialMoment n (32 - j)) * lam ^ (32 - j) := by ring
    _ = (radialMoment ((n + 1 : ℕ) : ℝ) 32 * (Contract.spherePolyCoeff (n + 1) j : ℝ)) *
        lam ^ (32 - j) := by rw [spherePolyCoeff_gaussian n j hj']
    _ = _ := by ring

/-- The representation with the radial expectation written explicitly, as in A4. -/
theorem signedSplitMoment_eq_gaussian_norm_moment (n : ℕ) (lam : ℝ) :
    signedSplitMoment n lam =
      (∫ g : EuclideanSpace ℝ (Fin (n + 1)), ‖g‖ ^ 64
        ∂stdGaussian (EuclideanSpace ℝ (Fin (n + 1)))) * spherePolyReal (n + 1) lam := by
  rw [integral_norm_pow_stdGaussian_even (n + 1) 32]
  exact signedSplitMoment_eq_spherePoly n lam

end GMCExplicitDelta.Averaging
