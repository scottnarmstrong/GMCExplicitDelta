module

public import GMCExplicitDelta.Insertion.CoshGeneratorPoly
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Iterated derivatives of `q (cosh t - 1)`

A generic statement over a nontrivially normed field `𝕜` (used for `ℝ` and `ℂ`) for any pair
`c, s` with `c' = s`, `s' = c`, `s² = (c-1)² + 2(c-1)` (i.e. `c² - s² = 1`).
-/

@[expose] public section

open Polynomial

namespace GMCExplicitDelta.Insertion

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {c s : 𝕜 → 𝕜}

theorem hasDerivAt_eval_comp (hc : ∀ x, HasDerivAt c (s x) x) (q : 𝕜[X]) (x : 𝕜) :
    HasDerivAt (fun y => q.eval (c y - 1)) ((derivative q).eval (c x - 1) * s x) x :=
  by
  have h := HasDerivAt.scomp x (q.hasDerivAt (c x - 1)) ((hc x).sub_const 1)
  rw [smul_eq_mul, mul_comm] at h
  exact h

theorem deriv_eval_comp (hc : ∀ x, HasDerivAt c (s x) x) (q : 𝕜[X]) :
    deriv (fun y => q.eval (c y - 1)) = fun x => (derivative q).eval (c x - 1) * s x :=
  funext fun x => (hasDerivAt_eval_comp hc q x).deriv

theorem deriv_deriv_eval_comp (hc : ∀ x, HasDerivAt c (s x) x) (hs : ∀ x, HasDerivAt s (c x) x)
    (hcs : ∀ x, s x ^ 2 = (c x - 1) ^ 2 + 2 * (c x - 1)) (q : 𝕜[X]) :
    deriv (deriv fun y => q.eval (c y - 1)) = fun x => (coshM q).eval (c x - 1) := by
  rw [deriv_eval_comp hc]
  funext x
  have h := (hasDerivAt_eval_comp hc (derivative q) x).fun_mul (hs x)
  rw [h.deriv]
  simp only [coshM_apply, eval_add, eval_mul, eval_pow, eval_X, eval_ofNat, eval_one]
  have := hcs x
  linear_combination (eval (c x - 1) (derivative (derivative q))) * this

/-- (G2), generic form: `(d/dx)^(2n) (q ∘ (c - 1)) = (M^n q) ∘ (c - 1)`. -/
theorem iterate_deriv_even (hc : ∀ x, HasDerivAt c (s x) x) (hs : ∀ x, HasDerivAt s (c x) x)
    (hcs : ∀ x, s x ^ 2 = (c x - 1) ^ 2 + 2 * (c x - 1)) (q : 𝕜[X]) (n : ℕ) :
    deriv^[2 * n] (fun y => q.eval (c y - 1)) = fun x => ((coshM ^ n) q).eval (c x - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 + 2 * n by ring, Function.iterate_add_apply, ih]
    rw [show deriv^[2] = fun f => deriv (deriv f) from rfl]
    simp only
    rw [deriv_deriv_eval_comp hc hs hcs, pow_succ', Module.End.mul_apply]

theorem iterate_deriv_odd (hc : ∀ x, HasDerivAt c (s x) x) (hs : ∀ x, HasDerivAt s (c x) x)
    (hcs : ∀ x, s x ^ 2 = (c x - 1) ^ 2 + 2 * (c x - 1)) (q : 𝕜[X]) (n : ℕ) :
    deriv^[2 * n + 1] (fun y => q.eval (c y - 1)) =
      fun x => (derivative ((coshM ^ n) q)).eval (c x - 1) * s x := by
  rw [Function.iterate_succ_apply', iterate_deriv_even hc hs hcs, deriv_eval_comp hc]

end GMCExplicitDelta.Insertion
