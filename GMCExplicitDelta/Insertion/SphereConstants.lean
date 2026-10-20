module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum

/-!
# Exact constants for the PSD sphere inequality

The coefficient is the ratio of the radial and one-dimensional Gaussian even
moments. This file evaluates that finite product; it does not assert the
Gaussian moment identities or the random matrix inequality.
-/

@[expose] public section

open scoped BigOperators

namespace GMCExplicitDelta.Insertion

/-- The coefficient `β_{d,p}^p` in C13, in finite-product form. -/
noncomputable def sphereMomentRatio (d p : ℕ) : ℝ :=
  ∏ j ∈ Finset.range p, ((d : ℝ) + 2 * j) / (2 * j + 1)

/-- Exact two-dimensional coefficient at moment order 32. -/
theorem sphereMomentRatio_two_32 :
    sphereMomentRatio 2 32 = (4 : ℝ) ^ 32 / Nat.choose 64 32 := by
  norm_num [sphereMomentRatio, Finset.prod_range_succ, Nat.choose_eq_factorial_div_factorial, Nat.factorial]

/-- Exact three-dimensional coefficient at moment order 32. -/
theorem sphereMomentRatio_three_32 : sphereMomentRatio 3 32 = 65 := by
  norm_num [sphereMomentRatio, Finset.prod_range_succ]

/-- Exact four-dimensional coefficient at moment order 32. -/
theorem sphereMomentRatio_four_32 :
    sphereMomentRatio 4 32 = 33 * (4 : ℝ) ^ 32 / Nat.choose 64 32 := by
  norm_num [sphereMomentRatio, Finset.prod_range_succ, Nat.choose_eq_factorial_div_factorial, Nat.factorial]

end GMCExplicitDelta.Insertion
