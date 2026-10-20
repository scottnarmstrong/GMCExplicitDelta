module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! # Scalar Gaussian even moments for C13 -/

@[expose] public section

open MeasureTheory Set
open scoped Nat NNReal

namespace GMCExplicitDelta.Insertion

/-- The half-line Gaussian moment, before normalization by the density constant. -/
theorem integral_gaussian_even_Ioi (p : ℕ) :
    (∫ x : ℝ in Ioi 0, x ^ (2 * p) * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) =
      ((2 * p - 1)‼ : ℝ) * ((1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) / 2 * Real.sqrt Real.pi) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow
    (p := (2 : ℝ)) (q := (2 * p : ℕ)) (b := (1 / 2 : ℝ))
    (by norm_num) (by exact lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg _)) (by norm_num)
  simp only [Real.rpow_natCast, Real.rpow_two] at h
  rw [h]
  have ha : (((2 * p : ℕ) : ℝ) + 1) / 2 = (p : ℝ) + 1 / 2 := by push_cast; ring
  rw [ha, Real.Gamma_nat_add_half]
  have hb : -(((2 * p : ℕ) : ℝ) + 1) / 2 = -(1 / 2 : ℝ) - (p : ℝ) := by
    push_cast; ring
  rw [hb, Real.rpow_sub (by norm_num : (0 : ℝ) < 1 / 2), Real.rpow_natCast]
  have hc : (1 / 2 : ℝ) ^ p * 2 ^ p = 1 := by
    rw [← mul_pow]; norm_num
  have hd : (2 : ℝ) ^ p ≠ 0 := by positivity
  have he : (1 / 2 : ℝ) ^ p ≠ 0 := by positivity
  field_simp
  nlinarith only [hc]

/-- The corresponding full-line, unnormalized even moment. -/
theorem integral_gaussian_even (p : ℕ) :
    (∫ x : ℝ, x ^ (2 * p) * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) =
      ((2 * p - 1)‼ : ℝ) * ((1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) * Real.sqrt Real.pi) := by
  let f : ℝ → ℝ := fun x => x ^ (2 * p) * Real.exp (-(1 / 2 : ℝ) * x ^ 2)
  have hi : Integrable f := by
    simpa only [Real.rpow_natCast] using
      (integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
        (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg (2 * p))))
  have hs : (∫ x in Iic (0 : ℝ), f x) = ∫ x in Ioi (0 : ℝ), f x := by
    calc
      _ = ∫ x in Ioi (0 : ℝ), f (-x) := by
        simpa only [neg_zero] using (integral_comp_neg_Ioi 0 f).symm
      _ = _ := by simp only [f, Even.neg_pow (even_two_mul p), neg_sq]
  rw [← integral_add_compl measurableSet_Ioi hi, compl_Ioi, hs]
  dsimp only [f]
  rw [integral_gaussian_even_Ioi]
  ring

/-- A standard Gaussian real has even moment `(2p-1)!!`, including `p = 0`. -/
theorem integral_pow_gaussianReal_even (p : ℕ) :
    (∫ x : ℝ, x ^ (2 * p) ∂ProbabilityTheory.gaussianReal 0 1) =
      ((2 * p - 1)‼ : ℝ) := by
  have hn (n : ℕ) :
      (∫ x : ℝ, x ^ (2 * n) ∂ProbabilityTheory.gaussianReal 0 1) =
      (Real.sqrt (2 * Real.pi))⁻¹ *
        (∫ x : ℝ, x ^ (2 * n) * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) := by
    rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul (by norm_num)]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [ProbabilityTheory.gaussianPDFReal, sub_zero, NNReal.coe_one,
      mul_one, smul_eq_mul]
    rw [show -x ^ 2 / (2 : ℝ) = -(1 / 2 : ℝ) * x ^ 2 by ring]
    ring
  have hz := hn 0
  rw [integral_gaussian_even] at hz
  simp only [Nat.mul_zero, Nat.zero_sub, Nat.doubleFactorial, Nat.cast_one,
    pow_zero, integral_const, probReal_univ, smul_eq_mul, mul_one, one_mul] at hz
  rw [hn p, integral_gaussian_even]
  calc
    _ = ((2 * p - 1)‼ : ℝ) *
        ((Real.sqrt (2 * Real.pi))⁻¹ *
          ((1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) * Real.sqrt Real.pi)) := by ring
    _ = _ := by rw [← hz, mul_one]

/-- Scaling a standard Gaussian gives the even moments at variance `c²`. -/
theorem integral_pow_gaussianReal_sq_even (c : ℝ) (p : ℕ) :
    (∫ x : ℝ, x ^ (2 * p)
      ∂ProbabilityTheory.gaussianReal 0 (NNReal.mk (c ^ 2) (sq_nonneg c))) =
      ((2 * p - 1)‼ : ℝ) * c ^ (2 * p) := by
  have hm : (ProbabilityTheory.gaussianReal 0 1).map (fun x => c * x) =
      ProbabilityTheory.gaussianReal 0 (NNReal.mk (c ^ 2) (sq_nonneg c)) := by
    simpa only [mul_zero, mul_one] using
      (ProbabilityTheory.gaussianReal_map_const_mul (μ := 0) (v := 1) c)
  rw [← hm, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [mul_pow]
  rw [integral_const_mul, integral_pow_gaussianReal_even, mul_comm]

end GMCExplicitDelta.Insertion
