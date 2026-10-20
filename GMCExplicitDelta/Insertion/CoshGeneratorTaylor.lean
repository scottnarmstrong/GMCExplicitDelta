module

public import GMCExplicitDelta.Insertion.CoshGeneratorDeriv
public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Real statements (G1), (G2) and the Taylor expansion of `(cosh t - 1)^p`
-/

@[expose] public section

open Polynomial
open scoped Nat

namespace GMCExplicitDelta.Insertion

/-- The function `t ↦ (cosh t - 1)^p`. -/
noncomputable def coshPow (p : ℕ) (t : ℝ) : ℝ := (Real.cosh t - 1) ^ p

theorem hcs_real (x : ℝ) : Real.sinh x ^ 2 = (Real.cosh x - 1) ^ 2 + 2 * (Real.cosh x - 1) := by
  have := Real.cosh_sq x
  linear_combination -this

theorem hcs_complex (x : ℂ) :
    Complex.sinh x ^ 2 = (Complex.cosh x - 1) ^ 2 + 2 * (Complex.cosh x - 1) := by
  have := Complex.cosh_sq x
  linear_combination -this

/-- (G1): `(1/2) d²/dt² a(t)^(k+1) = ((k+1)²/2) a^(k+1) + ((k+1)(2k+1)/2) a^k`. -/
theorem G1_deriv_deriv (k : ℕ) (t : ℝ) :
    (1 / 2 : ℝ) * deriv (deriv (coshPow (k + 1))) t =
      ((k + 1 : ℝ) ^ 2 / 2) * (Real.cosh t - 1) ^ (k + 1) +
        ((k + 1 : ℝ) * (2 * k + 1) / 2) * (Real.cosh t - 1) ^ k := by
  have h := congrFun (deriv_deriv_eval_comp (c := Real.cosh) (s := Real.sinh)
    Real.hasDerivAt_cosh Real.hasDerivAt_sinh hcs_real (X ^ (k + 1) : ℝ[X])) t
  have e : coshPow (k + 1) = fun y => (X ^ (k + 1) : ℝ[X]).eval (Real.cosh y - 1) := by
    funext y; simp [coshPow]
  rw [e, h, coshM_X_pow_succ]
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
  ring

/-- (G1), `k = 0`: the constant `a^0 = 1` has zero second derivative. -/
theorem G1_deriv_deriv_zero (t : ℝ) : deriv (deriv (coshPow 0)) t = 0 := by
  have : coshPow 0 = fun _ => (1 : ℝ) := by funext y; simp [coshPow]
  simp [this]

/-- (G2): `(d/dt)^(2n) a(t)^p = 2^n · ((L^n e_p)(a(t)))`. -/
theorem G2_iteratedDeriv_even (p n : ℕ) :
    iteratedDeriv (2 * n) (coshPow p) =
      fun t => (2 : ℝ) ^ n * ((coshL ^ n) (X ^ p : ℝ[X])).eval (Real.cosh t - 1) := by
  have h := iterate_deriv_even (c := Real.cosh) (s := Real.sinh)
    Real.hasDerivAt_cosh Real.hasDerivAt_sinh hcs_real (X ^ p : ℝ[X]) n
  have e : coshPow p = fun y => (X ^ p : ℝ[X]).eval (Real.cosh y - 1) := by
    funext y; simp [coshPow]
  rw [iteratedDeriv_eq_iterate, e, h]
  funext t
  rw [coshM_pow_eq]
  simp [LinearMap.smul_apply, Polynomial.eval_smul]

theorem iteratedDeriv_even_eq (p n : ℕ) :
    iteratedDeriv (2 * n) (coshPow p) =
      fun t => ((coshM ^ n) (X ^ p : ℝ[X])).eval (Real.cosh t - 1) := by
  have h := iterate_deriv_even (c := Real.cosh) (s := Real.sinh)
    Real.hasDerivAt_cosh Real.hasDerivAt_sinh hcs_real (X ^ p : ℝ[X]) n
  have e : coshPow p = fun y => (X ^ p : ℝ[X]).eval (Real.cosh y - 1) := by
    funext y; simp [coshPow]
  rw [iteratedDeriv_eq_iterate, e, h]

theorem iteratedDeriv_odd_eq (p n : ℕ) :
    iteratedDeriv (2 * n + 1) (coshPow p) =
      fun t => (derivative ((coshM ^ n) (X ^ p : ℝ[X]))).eval (Real.cosh t - 1) * Real.sinh t := by
  have h := iterate_deriv_odd (c := Real.cosh) (s := Real.sinh)
    Real.hasDerivAt_cosh Real.hasDerivAt_sinh hcs_real (X ^ p : ℝ[X]) n
  have e : coshPow p = fun y => (X ^ p : ℝ[X]).eval (Real.cosh y - 1) := by
    funext y; simp [coshPow]
  rw [iteratedDeriv_eq_iterate, e, h]

/-! ### Complex extension and Taylor series -/

/-- Complex extension. -/
noncomputable def coshPowC (p : ℕ) (z : ℂ) : ℂ := (Complex.cosh z - 1) ^ p

theorem differentiable_coshPowC (p : ℕ) : Differentiable ℂ (coshPowC p) := by
  have : Differentiable ℂ (fun z : ℂ => Complex.cosh z - 1) :=
    Complex.differentiable_cosh.sub_const 1
  exact this.pow p

theorem eval_map_ofReal (q : ℝ[X]) (a : ℝ) :
    (q.map Complex.ofRealHom).eval (a : ℂ) = ((q.eval a : ℝ) : ℂ) := by
  rw [eval_map]
  exact eval₂_at_apply Complex.ofRealHom a

theorem iteratedDeriv_coshPowC_ofReal (p j : ℕ) (θ : ℝ) :
    iteratedDeriv j (coshPowC p) (θ : ℂ) = ((iteratedDeriv j (coshPow p) θ : ℝ) : ℂ) := by
  have e : coshPowC p = fun y => (X ^ p : ℂ[X]).eval (Complex.cosh y - 1) := by
    funext y; simp [coshPowC]
  have key : ∀ n : ℕ, (coshM ^ n) (X ^ p : ℂ[X]) =
      ((coshM ^ n) (X ^ p : ℝ[X])).map Complex.ofRealHom := by
    intro n; rw [coshM_pow_map]; simp
  have hc : Complex.cosh (θ : ℂ) - 1 = ((Real.cosh θ - 1 : ℝ) : ℂ) := by
    simp
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' j
  · rw [iteratedDeriv_even_eq, iteratedDeriv_eq_iterate, e,
      iterate_deriv_even (c := Complex.cosh) (s := Complex.sinh)
        Complex.hasDerivAt_cosh Complex.hasDerivAt_sinh hcs_complex]
    beta_reduce
    rw [key n, hc, eval_map_ofReal]
  · rw [iteratedDeriv_odd_eq, iteratedDeriv_eq_iterate, e,
      iterate_deriv_odd (c := Complex.cosh) (s := Complex.sinh)
        Complex.hasDerivAt_cosh Complex.hasDerivAt_sinh hcs_complex]
    beta_reduce
    rw [key n, hc, derivative_map, eval_map_ofReal]
    push_cast
    rfl

/-- Real Taylor expansion of the entire function `(cosh t - 1)^p`. -/
theorem hasSum_taylor_coshPow (p : ℕ) (θ x : ℝ) :
    HasSum (fun j : ℕ => ((j ! : ℝ)⁻¹ * iteratedDeriv j (coshPow p) θ) * x ^ j)
      (coshPow p (θ + x)) := by
  have h := Complex.hasSum_taylorSeries_of_entire (differentiable_coshPowC p) (θ : ℂ)
    ((θ + x : ℝ) : ℂ)
  have h' : HasSum (fun j : ℕ => ((((j ! : ℝ)⁻¹ * iteratedDeriv j (coshPow p) θ) * x ^ j : ℝ) : ℂ))
      ((coshPow p (θ + x) : ℝ) : ℂ) := by
    convert h using 1
    · funext j
      rw [iteratedDeriv_coshPowC_ofReal]
      simp only [smul_eq_mul]
      push_cast
      ring
    · simp [coshPowC, coshPow, Complex.ofReal_cosh]
  exact Complex.hasSum_ofReal.mp h'

theorem eval_nonneg_of_coeff_nonneg {q : ℝ[X]} (h : ∀ k, 0 ≤ q.coeff k) {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ q.eval a := by
  rw [eval_eq_sum_range]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (h i) (pow_nonneg ha i)

theorem coshM_pow_coeff_nonneg (n p k : ℕ) : 0 ≤ ((coshM ^ n) (X ^ p : ℝ[X])).coeff k := by
  rw [coshM_pow_eq]
  simp only [LinearMap.smul_apply, coeff_smul, smul_eq_mul]
  exact mul_nonneg (by positivity) (coshL_pow_nonneg n p k)

theorem derivative_coeff_nonneg {q : ℝ[X]} (h : ∀ k, 0 ≤ q.coeff k) (k : ℕ) :
    0 ≤ (derivative q).coeff k := by
  rw [coeff_derivative]
  exact mul_nonneg (h _) (by positivity)

/-- For `θ ≥ 0` all derivatives of `(cosh t - 1)^p` at `θ` are nonnegative. -/
theorem iteratedDeriv_coshPow_nonneg (p j : ℕ) {θ : ℝ} (hθ : 0 ≤ θ) :
    0 ≤ iteratedDeriv j (coshPow p) θ := by
  have ha : 0 ≤ Real.cosh θ - 1 := by linarith [Real.one_le_cosh θ]
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' j
  · rw [iteratedDeriv_even_eq]
    exact eval_nonneg_of_coeff_nonneg (coshM_pow_coeff_nonneg n p) ha
  · rw [iteratedDeriv_odd_eq]
    exact mul_nonneg (eval_nonneg_of_coeff_nonneg
      (derivative_coeff_nonneg (coshM_pow_coeff_nonneg n p)) ha) (Real.sinh_nonneg_iff.mpr hθ)

end GMCExplicitDelta.Insertion
