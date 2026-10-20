module

public import GMCExplicitDelta.Insertion.CoshGeneratorPoly
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.Algebra.Group.Nat.Even

/-! # Formal hyperbolic series for coefficient-level moment transfer -/

@[expose] public section

namespace GMCExplicitDelta.Insertion

/-- The formal even exponential series, including its constant term. -/
noncomputable def formalCosh : PowerSeries ℝ :=
  PowerSeries.mk fun n => if Even n then (n.factorial : ℝ)⁻¹ else 0

/-- The formal odd exponential series. -/
noncomputable def formalSinh : PowerSeries ℝ :=
  PowerSeries.mk fun n => if Even n then 0 else (n.factorial : ℝ)⁻¹

theorem factorial_inv_succ_mul (n : ℕ) :
    (((n + 1).factorial : ℝ)⁻¹) * ((n + 1 : ℕ) : ℝ) = (n.factorial : ℝ)⁻¹ := by
  rw [Nat.factorial_succ, Nat.cast_mul, mul_inv_rev, mul_assoc,
    inv_mul_cancel₀ (by positivity : ((n + 1 : ℕ) : ℝ) ≠ 0), mul_one]

theorem derivative_formalCosh : PowerSeries.derivative formalCosh = formalSinh := by
  ext n
  simp only [PowerSeries.coeff_derivative, formalCosh, formalSinh,
    PowerSeries.coeff_mk, Nat.even_add_one]
  by_cases hn : Even n
  · simp only [hn, not_true_eq_false, ↓reduceIte, zero_mul]
  · simp only [hn, not_false_eq_true, ↓reduceIte]
    simpa only [Nat.cast_add, Nat.cast_one] using factorial_inv_succ_mul n

theorem derivative_formalSinh : PowerSeries.derivative formalSinh = formalCosh := by
  ext n
  simp only [PowerSeries.coeff_derivative, formalCosh, formalSinh,
    PowerSeries.coeff_mk, Nat.even_add_one]
  by_cases hn : Even n
  · simp only [hn, not_true_eq_false, ↓reduceIte]
    simpa only [Nat.cast_add, Nat.cast_one] using factorial_inv_succ_mul n
  · simp only [hn, not_false_eq_true, ↓reduceIte, zero_mul]

@[simp] theorem constantCoeff_formalCosh : PowerSeries.constantCoeff formalCosh = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp [formalCosh, PowerSeries.coeff_mk]

@[simp] theorem constantCoeff_formalSinh : PowerSeries.constantCoeff formalSinh = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp [formalSinh, PowerSeries.coeff_mk]

/-- The hyperbolic identity follows coefficientwise from its differential equation. -/
theorem formalCosh_sq_sub_formalSinh_sq : formalCosh ^ 2 - formalSinh ^ 2 = 1 := by
  apply PowerSeries.derivative.ext
  · simp only [map_sub, Derivation.leibniz_pow, derivative_formalCosh,
      derivative_formalSinh, PowerSeries.derivative_one]
    simp only [smul_eq_mul]
    ring
  · simp only [map_sub, map_pow, constantCoeff_formalCosh, constantCoeff_formalSinh,
      one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero, map_one]

end GMCExplicitDelta.Insertion
