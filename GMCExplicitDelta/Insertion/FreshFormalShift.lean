module

public import GMCExplicitDelta.Insertion.FreshFormalGenerator
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # The shifted formal hyperbolic series at an old response -/

@[expose] public section

open Polynomial

namespace GMCExplicitDelta.Insertion

/-- `cosh(theta+t)` in formal series, where `cosh theta = 1+j`. -/
noncomputable def shiftedFormalCosh (j : ℝ) : PowerSeries ℝ :=
  PowerSeries.C (j + 1) * formalCosh +
    PowerSeries.C (Real.sqrt (j * (j + 2))) * formalSinh

/-- The corresponding formal hyperbolic sine. -/
noncomputable def shiftedFormalSinh (j : ℝ) : PowerSeries ℝ :=
  PowerSeries.C (Real.sqrt (j * (j + 2))) * formalCosh +
    PowerSeries.C (j + 1) * formalSinh

theorem derivative_shiftedFormalCosh (j : ℝ) :
    PowerSeries.derivative (shiftedFormalCosh j) = shiftedFormalSinh j := by
  simp only [shiftedFormalCosh, shiftedFormalSinh, map_add, Derivation.leibniz,
    PowerSeries.derivative_C, derivative_formalCosh, derivative_formalSinh,
    smul_eq_mul, mul_zero, add_zero]
  ring

theorem derivative_shiftedFormalSinh (j : ℝ) :
    PowerSeries.derivative (shiftedFormalSinh j) = shiftedFormalCosh j := by
  simp only [shiftedFormalCosh, shiftedFormalSinh, map_add, Derivation.leibniz,
    PowerSeries.derivative_C, derivative_formalCosh, derivative_formalSinh,
    smul_eq_mul, mul_zero, add_zero]
  ring

@[simp] theorem constantCoeff_shiftedFormalCosh (j : ℝ) :
    PowerSeries.constantCoeff (shiftedFormalCosh j) = j + 1 := by
  simp only [shiftedFormalCosh, map_add, map_mul, PowerSeries.constantCoeff_C,
    constantCoeff_formalCosh, constantCoeff_formalSinh, mul_one, mul_zero, add_zero]

theorem shiftedFormalCosh_sq_sub_shiftedFormalSinh_sq {j : ℝ} (hj : 0 ≤ j) :
    shiftedFormalCosh j ^ 2 - shiftedFormalSinh j ^ 2 = 1 := by
  calc
    _ = (PowerSeries.C (j + 1) ^ 2 - PowerSeries.C (Real.sqrt (j * (j + 2))) ^ 2) *
        (formalCosh ^ 2 - formalSinh ^ 2) := by
      unfold shiftedFormalCosh shiftedFormalSinh
      ring
    _ = PowerSeries.C ((j + 1) ^ 2 - Real.sqrt (j * (j + 2)) ^ 2) := by
      rw [formalCosh_sq_sub_formalSinh_sq, mul_one, map_sub, map_pow, map_pow]
    _ = 1 := by
      rw [Real.sq_sqrt (mul_nonneg hj (add_nonneg hj (by norm_num)))]
      have he : (j + 1) ^ 2 - j * (j + 2) = 1 := by ring
      rw [he, map_one]

theorem shiftedFormalSinh_sq {j : ℝ} (hj : 0 ≤ j) :
    shiftedFormalSinh j ^ 2 = (shiftedFormalCosh j - 1) ^ 2 + 2 * (shiftedFormalCosh j - 1) := by
  have hh := shiftedFormalCosh_sq_sub_shiftedFormalSinh_sq hj
  linear_combination -hh

/-- The exact generator coefficient of the scalar reference in I3. -/
theorem shiftedFormalCosh_even_coeff {j : ℝ} (hj : 0 ≤ j) (p n : ℕ) :
    ((2 * n).factorial : ℝ) * PowerSeries.coeff (2 * n) ((shiftedFormalCosh j - 1) ^ p) =
      2 ^ n * (((coshL ^ n) (X ^ p : ℝ[X])).eval j) := by
  have hh := formal_hyperbolic_even_coeff (derivative_shiftedFormalCosh j)
    (derivative_shiftedFormalSinh j) (shiftedFormalSinh_sq hj) p n
  simpa only [constantCoeff_shiftedFormalCosh, add_sub_cancel_right] using hh

/-- The decomposition used when the even and odd spatial weights are summed. -/
theorem shiftedFormalCosh_sub_one_eq (j : ℝ) :
    shiftedFormalCosh j - 1 = PowerSeries.C j + PowerSeries.C (j + 1) * (formalCosh - 1) +
      PowerSeries.C (Real.sqrt (j * (j + 2))) * formalSinh := by
  unfold shiftedFormalCosh
  rw [map_add, map_one]
  ring

end GMCExplicitDelta.Insertion
