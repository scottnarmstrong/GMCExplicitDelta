module

public import GMCExplicitDelta.Insertion.FreshFormalCosh
public import Mathlib.Algebra.Polynomial.Eval.SMul

/-! # The hyperbolic generator acting on formal Taylor coefficients -/

@[expose] public section

open Polynomial

namespace GMCExplicitDelta.Insertion

/-- Constant-term evaluation commutes with polynomial substitution. -/
theorem constantCoeff_aeval (f : PowerSeries ℝ) (q : ℝ[X]) :
    PowerSeries.constantCoeff (aeval f q) = q.eval (PowerSeries.constantCoeff f) := by
  let cc : PowerSeries ℝ →ₐ[ℝ] ℝ :=
    { PowerSeries.constantCoeff with
      commutes' := fun r => by simp }
  change cc (aeval f q) = q.eval (cc f)
  simpa only [coe_aeval_eq_eval] using (aeval_algHom_apply cc f q).symm

/-- The first derivative chain rule, with all coefficient derivatives zero. -/
theorem formal_derivative_aeval {c s : PowerSeries ℝ}
    (hc : PowerSeries.derivative c = s) (q : ℝ[X]) :
    PowerSeries.derivative (aeval (c - 1) q) = aeval (c - 1) q.derivative * s := by
  have hh := PowerSeries.derivative.map_aeval q (c - 1)
  simpa only [map_sub, PowerSeries.derivative_one, hc, sub_zero, smul_eq_mul] using hh

/-- The formal second derivative is twice the generator, exactly as in I2. -/
theorem formal_derivative_twice_aeval {c s : PowerSeries ℝ}
    (hc : PowerSeries.derivative c = s) (hs : PowerSeries.derivative s = c)
    (hcs : s ^ 2 = (c - 1) ^ 2 + 2 * (c - 1)) (q : ℝ[X]) :
    PowerSeries.derivative (PowerSeries.derivative (aeval (c - 1) q)) =
      aeval (c - 1) (coshM q) := by
  rw [formal_derivative_aeval hc, Derivation.leibniz, formal_derivative_aeval hc, hs]
  simp only [smul_eq_mul, coshM_apply, map_add, map_mul, map_pow, map_ofNat, aeval_X, map_one]
  linear_combination (aeval (c - 1) q.derivative.derivative) * hcs

/-- Iteration of the formal generator identity. -/
theorem formal_iterate_derivative_even {c s : PowerSeries ℝ}
    (hc : PowerSeries.derivative c = s) (hs : PowerSeries.derivative s = c)
    (hcs : s ^ 2 = (c - 1) ^ 2 + 2 * (c - 1)) (q : ℝ[X]) (n : ℕ) :
    (PowerSeries.derivative : PowerSeries ℝ → PowerSeries ℝ)^[2 * n] (aeval (c - 1) q) =
      aeval (c - 1) ((coshM ^ n) q) := by
  induction n with
  | zero => simp only [Nat.mul_zero, Function.iterate_zero, id_eq, pow_zero, Module.End.one_apply]
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 + 2 * n by omega, Function.iterate_add_apply, ih]
    change PowerSeries.derivative (PowerSeries.derivative
      (aeval (c - 1) ((coshM ^ n) q))) = _
    rw [formal_derivative_twice_aeval hc hs hcs, pow_succ', Module.End.mul_apply]

/-- The even coefficient of a shifted formal hyperbolic power is the I2 generator coefficient. -/
theorem formal_hyperbolic_even_coeff {c s : PowerSeries ℝ}
    (hc : PowerSeries.derivative c = s) (hs : PowerSeries.derivative s = c)
    (hcs : s ^ 2 = (c - 1) ^ 2 + 2 * (c - 1)) (p n : ℕ) :
    (((2 * n).factorial : ℝ) * PowerSeries.coeff (2 * n) ((c - 1) ^ p)) =
      2 ^ n * (((coshL ^ n) (X ^ p : ℝ[X])).eval (PowerSeries.constantCoeff c - 1)) := by
  have hh := congrArg PowerSeries.constantCoeff
    (formal_iterate_derivative_even hc hs hcs (X ^ p : ℝ[X]) n)
  simp only [map_pow, aeval_X] at hh
  rw [PowerSeries.constantCoeff_iterate_derivative, constantCoeff_aeval, coshM_pow_eq] at hh
  simpa only [LinearMap.smul_apply, eval_smul, smul_eq_mul, map_sub, map_one] using hh

end GMCExplicitDelta.Insertion
