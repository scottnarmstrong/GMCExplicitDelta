module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Module.Basic
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Algebra.Order.Ring.Defs

/-!
# The cosh generator on polynomials in `a = cosh t - 1`

Design choice: the generator is realised on `R[X]` (polynomials in `a`), not on `Fin (p+1) → ℝ`.
We use the unscaled operator `M q = (X² + 2X) q'' + (X + 1) q'`, so that
`d²/dt² (q (a t)) = (M q) (a t)` (statement `G2`), and `L = (1/2) M` is the generator of
the brief: `L X^k = (k²/2) X^k + (k(2k-1)/2) X^(k-1)` (statement `G1`, coefficientwise as
`coeff_coshM`).  Coefficients of `X^p` are read off by `Polynomial.coeff`.
-/

@[expose] public section

open Polynomial

namespace GMCExplicitDelta.Insertion

section Poly

variable {R : Type*} [CommSemiring R]

/-- `M q = (X² + 2X) q'' + (X + 1) q'`; twice the generator. -/
noncomputable def coshMFun (q : R[X]) : R[X] :=
  (X ^ 2 + 2 * X) * derivative (derivative q) + (X + 1) * derivative q

/-- `M` as a linear map on `R[X]`. -/
noncomputable def coshM : R[X] →ₗ[R] R[X] where
  toFun := coshMFun
  map_add' q r := by simp only [coshMFun, derivative_add]; ring
  map_smul' c q := by
    simp only [coshMFun, RingHom.id_apply, Polynomial.smul_eq_C_mul, derivative_mul,
      derivative_C, zero_mul, zero_add]
    ring

theorem coshM_apply (q : R[X]) :
    coshM q = (X ^ 2 + 2 * X) * derivative (derivative q) + (X + 1) * derivative q := rfl

/-- (G1), coefficientwise: `M X^k = k² X^k + k(2k-1) X^(k-1)`, i.e. the coefficient of `X^k`
in `M q` is `k² q_k + (k+1)(2k+1) q_{k+1}`. -/
theorem coeff_coshM (q : R[X]) (k : ℕ) :
    (coshM q).coeff k =
      (k : R) ^ 2 * q.coeff k + ((k : R) + 1) * (2 * k + 1) * q.coeff (k + 1) := by
  have h : coshM q = X * (X * derivative (derivative q) + 2 * derivative (derivative q)
      + derivative q) + derivative q := by
    rw [coshM_apply]; ring
  rw [h]
  rcases k with _ | _ | k
  · simp [coeff_derivative]
  · simp [coeff_derivative, coeff_X_mul, coeff_add]
    ring
  · simp [coeff_derivative, coeff_X_mul, coeff_add]
    ring

/-- (G1), monomial form with the stated constants. -/
theorem coshM_X_pow_succ (k : ℕ) :
    coshM (X ^ (k + 1) : R[X]) =
      C ((k + 1 : R) ^ 2) * X ^ (k + 1) + C (((k : R) + 1) * (2 * k + 1)) * X ^ k := by
  ext j
  rw [coeff_coshM]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow]
  by_cases h1 : j = k + 1
  · subst h1; simp
  · by_cases h2 : j = k
    · subst h2; simp
    · simp [h1, h2]

theorem coshM_X_pow_zero : coshM (X ^ 0 : R[X]) = 0 := by
  simp [coshM_apply]

theorem coshM_map {S : Type*} [CommSemiring S] (φ : R →+* S) (q : R[X]) :
    (coshM q).map φ = coshM (q.map φ) := by
  simp [coshM_apply, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_pow,
    derivative_map]

theorem coshM_pow_map {S : Type*} [CommSemiring S] (φ : R →+* S) (n : ℕ) (q : R[X]) :
    ((coshM ^ n) q).map φ = (coshM ^ n) (q.map φ) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Module.End.mul_apply, coshM_map, ih, pow_succ',
      Module.End.mul_apply]

end Poly

section Real

/-- The generator `L = (1/2) M` on `ℝ[X]`. -/
noncomputable def coshL : ℝ[X] →ₗ[ℝ] ℝ[X] := (1 / 2 : ℝ) • coshM

theorem coshM_pow_eq (n : ℕ) : (coshM : ℝ[X] →ₗ[ℝ] ℝ[X]) ^ n = (2 : ℝ) ^ n • coshL ^ n := by
  rw [coshL, smul_pow, smul_smul, ← mul_pow]
  norm_num

/-- Coefficientwise `L`: `(L q)_k = (k²/2) q_k + ((k+1)(2k+1)/2) q_{k+1}`. -/
theorem coeff_coshL (q : ℝ[X]) (k : ℕ) :
    (coshL q).coeff k =
      (k : ℝ) ^ 2 / 2 * q.coeff k + ((k : ℝ) + 1) * (2 * k + 1) / 2 * q.coeff (k + 1) := by
  simp only [coshL, LinearMap.smul_apply, coeff_smul, coeff_coshM, smul_eq_mul]
  ring

theorem coshL_nonneg {q : ℝ[X]} (h : ∀ k, 0 ≤ q.coeff k) (k : ℕ) : 0 ≤ (coshL q).coeff k := by
  rw [coeff_coshL]
  have := h k; have := h (k + 1)
  positivity

theorem coshL_pow_nonneg (n p : ℕ) (k : ℕ) : 0 ≤ ((coshL ^ n) (X ^ p : ℝ[X])).coeff k := by
  induction n generalizing k with
  | zero => simp [coeff_X_pow]; split_ifs <;> norm_num
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact coshL_nonneg ih k

/-- (G2, degree part): the coefficient of `a^k` in `L^n e_p` vanishes unless `k + n ≥ p`. -/
theorem coshL_pow_coeff_eq_zero (n p : ℕ) :
    ∀ k, k + n < p → ((coshL ^ n) (X ^ p : ℝ[X])).coeff k = 0 := by
  induction n with
  | zero => intro k hk; simp [coeff_X_pow]; omega
  | succ n ih =>
    intro k hk
    rw [pow_succ', Module.End.mul_apply, coeff_coshL, ih k (by omega), ih (k + 1) (by omega)]
    simp

end Real

end GMCExplicitDelta.Insertion
