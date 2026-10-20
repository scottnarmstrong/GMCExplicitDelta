module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # Nonnegative hyperbolic series for the conditional moment comparison -/

@[expose] public section

open scoped ENNReal

namespace GMCExplicitDelta.Insertion

/-- The even hyperbolic increment has no constant Taylor term. -/
theorem hasSum_cosh_sub_one (t : ℝ) :
    HasSum (fun n : ℕ => t ^ (2 * (n + 1)) / ((2 * (n + 1)).factorial : ℝ))
      (Real.cosh t - 1) := by
  have hs := Real.hasSum_cosh t
  have ht := hs.summable.comp_injective Nat.succ_injective
  have he := hs.summable.sum_add_tsum_nat_add 1
  rw [hs.tsum_eq] at he
  simp only [Finset.sum_range_one, Nat.mul_zero, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one] at he
  have he' : (∑' n : ℕ, t ^ (2 * (n + 1)) / ((2 * (n + 1)).factorial : ℝ)) =
      Real.cosh t - 1 := by linarith only [he]
  exact he' ▸ ht.hasSum

/-- A nonnegative series suitable for Tonelli's theorem. -/
theorem ofReal_cosh_sub_one_eq_tsum (t : ℝ) :
    ENNReal.ofReal (Real.cosh t - 1) = ∑' n : ℕ,
      ENNReal.ofReal (((2 * (n + 1)).factorial : ℝ)⁻¹) *
        ENNReal.ofReal |t| ^ (2 * (n + 1)) := by
  have hs := hasSum_cosh_sub_one |t|
  rw [← Real.cosh_abs t, ← hs.tsum_eq,
    ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hs.summable]
  apply tsum_congr
  intro n
  rw [div_eq_mul_inv, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow (abs_nonneg _), mul_comm]

/-- The absolute odd hyperbolic function has a nonnegative odd series. -/
theorem ofReal_abs_sinh_eq_tsum (t : ℝ) :
    ENNReal.ofReal |Real.sinh t| = ∑' n : ℕ,
      ENNReal.ofReal (((2 * n + 1).factorial : ℝ)⁻¹) *
        ENNReal.ofReal |t| ^ (2 * n + 1) := by
  have hs := Real.hasSum_sinh |t|
  rw [Real.abs_sinh, ← hs.tsum_eq,
    ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hs.summable]
  apply tsum_congr
  intro n
  rw [div_eq_mul_inv, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow (abs_nonneg _), mul_comm]

end GMCExplicitDelta.Insertion
