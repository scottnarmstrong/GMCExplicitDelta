module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-! # Symmetrized powers with only nonnegative even binomial terms -/

@[expose] public section

namespace GMCExplicitDelta.Insertion

/-- The binomial projection onto even powers of the second variable. -/
theorem add_pow_add_sub_pow {R : Type*} [CommRing R] (A B : R) (p : ℕ) :
    (A + B) ^ p + (A - B) ^ p = 2 * ∑ i ∈ Finset.range (p + 1),
      if Even i then (p.choose i : R) * A ^ (p - i) * B ^ i else 0 := by
  rw [add_comm A B, add_pow, sub_eq_add_neg, add_comm A (-B), add_pow,
    ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : Even i
  · rw [ite_eq_left hi, Even.neg_pow hi]
    ring
  · have ho := Nat.not_even_iff_odd.mp hi
    rw [ite_eq_right hi, Odd.neg_pow ho]
    ring

/-- For real variables the surviving even terms can use the absolute odd variable. -/
theorem symmetrized_power_eq_even_sum (A B : ℝ) (p : ℕ) :
    ((A + B) ^ p + (A - B) ^ p) / 2 = ∑ i ∈ Finset.range (p + 1),
      if Even i then (p.choose i : ℝ) * A ^ (p - i) * |B| ^ i else 0 := by
  have hh := add_pow_add_sub_pow A B p
  have he : (∑ i ∈ Finset.range (p + 1),
      if Even i then (p.choose i : ℝ) * A ^ (p - i) * |B| ^ i else 0) =
      ∑ i ∈ Finset.range (p + 1),
      if Even i then (p.choose i : ℝ) * A ^ (p - i) * B ^ i else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    split_ifs with hi
    · rw [Even.pow_abs hi]
    · rfl
  rw [he]
  linarith only [hh]

end GMCExplicitDelta.Insertion
