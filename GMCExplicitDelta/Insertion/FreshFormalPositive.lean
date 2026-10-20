module

public import GMCExplicitDelta.Insertion.FreshFormalCosh
public import GMCExplicitDelta.Insertion.FreshCoefficientFunctional

/-! # Positive coefficients and sparse hyperbolic series under a moment functional -/

@[expose] public section

open scoped ENNReal

namespace GMCExplicitDelta.Insertion

theorem formalCosh_coeff_nonneg (n : ℕ) : 0 ≤ PowerSeries.coeff n formalCosh := by
  simp only [formalCosh, PowerSeries.coeff_mk]
  split_ifs <;> positivity

theorem formalSinh_coeff_nonneg (n : ℕ) : 0 ≤ PowerSeries.coeff n formalSinh := by
  simp only [formalSinh, PowerSeries.coeff_mk]
  split_ifs <;> positivity

theorem formalCosh_sub_one_coeff_nonneg (n : ℕ) :
    0 ≤ PowerSeries.coeff n (formalCosh - 1) := by
  by_cases hn : n = 0
  · subst n
    simp [formalCosh]
  · simp only [map_sub, formalCosh, PowerSeries.coeff_mk,
      PowerSeries.coeff_one, ite_eq_right hn, sub_zero]
    split_ifs <;> positivity

@[simp] theorem formalSinh_even_coeff (n : ℕ) : PowerSeries.coeff (2 * n) formalSinh = 0 := by
  simp [formalSinh, PowerSeries.coeff_mk]

@[simp] theorem formalSinh_odd_coeff (n : ℕ) :
    PowerSeries.coeff (2 * n + 1) formalSinh = ((2 * n + 1).factorial : ℝ)⁻¹ := by
  simp [formalSinh, PowerSeries.coeff_mk]

@[simp] theorem formalCosh_sub_one_odd_coeff (n : ℕ) :
    PowerSeries.coeff (2 * n + 1) (formalCosh - 1) = 0 := by
  simp [formalCosh, PowerSeries.coeff_mk]

@[simp] theorem formalCosh_sub_one_zero_coeff : PowerSeries.coeff 0 (formalCosh - 1) = 0 := by
  simp [formalCosh]

@[simp] theorem formalCosh_sub_one_even_coeff (n : ℕ) :
    PowerSeries.coeff (2 * (n + 1)) (formalCosh - 1) = ((2 * (n + 1)).factorial : ℝ)⁻¹ := by
  simp [formalCosh, PowerSeries.coeff_mk,
    show 2 * (n + 1) ≠ 0 by omega]

/-- A positive functional of the formal sine is its odd Taylor series. -/
theorem coefficientFunctional_formalSinh (B : ℕ → ℝ≥0∞) :
    coefficientFunctional B formalSinh = ∑' n : ℕ,
      ENNReal.ofReal (((2 * n + 1).factorial : ℝ)⁻¹) * B (2 * n + 1) := by
  unfold coefficientFunctional
  rw [← tsum_even_add_odd ENNReal.summable ENNReal.summable]
  simp only [formalSinh_even_coeff, formalSinh_odd_coeff, ENNReal.ofReal_zero,
    zero_mul, tsum_zero, zero_add]

/-- Remove a vanishing constant term from a nonnegative series. -/
theorem tsum_eq_succ_of_zero {f : ℕ → ℝ≥0∞} (h0 : f 0 = 0) :
    (∑' n : ℕ, f n) = ∑' n : ℕ, f (n + 1) := by
  have hs : Summable (fun n : ℕ => f (n + 1)) := ENNReal.summable
  have ht := tsum_eq_zero_add' hs
  simpa only [h0, zero_add] using ht

/-- A positive functional of the formal cosh increment starts at degree two. -/
theorem coefficientFunctional_formalCosh_sub_one (B : ℕ → ℝ≥0∞) :
    coefficientFunctional B (formalCosh - 1) = ∑' n : ℕ,
      ENNReal.ofReal (((2 * (n + 1)).factorial : ℝ)⁻¹) * B (2 * (n + 1)) := by
  unfold coefficientFunctional
  rw [← tsum_even_add_odd ENNReal.summable ENNReal.summable]
  simp only [formalCosh_sub_one_odd_coeff, ENNReal.ofReal_zero, zero_mul, tsum_zero, add_zero]
  let f : ℕ → ℝ≥0∞ := fun n =>
    ENNReal.ofReal (PowerSeries.coeff (2 * n) (formalCosh - 1)) * B (2 * n)
  have h0 : f 0 = 0 := by simp only [f, Nat.mul_zero, formalCosh_sub_one_zero_coeff,
    ENNReal.ofReal_zero, zero_mul]
  change (∑' n : ℕ, f n) = _
  have ht := tsum_eq_succ_of_zero h0
  exact ht.trans (tsum_congr fun n => by
    dsimp only [f]
    rw [formalCosh_sub_one_even_coeff])

end GMCExplicitDelta.Insertion
