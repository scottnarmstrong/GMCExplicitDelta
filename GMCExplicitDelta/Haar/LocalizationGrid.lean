module

public import GMCExplicitDelta.Haar.LocalizationQuadrature
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! H13: uniform-grid trapezoids and endpoint minima. -/
@[expose] public section

namespace GMCExplicitDelta.Haar

open Real Set intervalIntegral
open MeasureTheory (volume)
open scoped BigOperators

noncomputable def gridPoint (N i : ℕ) : ℝ := -(1 / 2) + (i : ℝ) / (N : ℝ)

noncomputable def gridTrap (N : ℕ) (f : ℝ → ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, (f (gridPoint N i) + f (gridPoint N (i + 1))) / 2

noncomputable def gridMin (N : ℕ) (f : ℝ → ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, min (f (gridPoint N i)) (f (gridPoint N (i + 1)))

theorem gridPoint_step (N i : ℕ) : gridPoint N (i + 1) - gridPoint N i = (N : ℝ)⁻¹ := by
  unfold gridPoint
  push_cast
  ring

theorem gridPoint_mem {N i : ℕ} (hN : 0 < N) (hi : i ≤ N) :
    gridPoint N i ∈ Icc (-(1 / 2)) (1 / 2) := by
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast hN
  have hi0 : 0 ≤ (i : ℝ) / (N : ℝ) := div_nonneg (Nat.cast_nonneg _) hN0.le
  have hi1 : (i : ℝ) / (N : ℝ) ≤ 1 := (div_le_one hN0).2 (by exact_mod_cast hi)
  unfold gridPoint
  constructor <;> linarith only [hi0, hi1]

theorem grid_integral_sum {N : ℕ} (hN : 0 < N) {f : ℝ → ℝ} (hf : Continuous f) :
    (∑ i ∈ Finset.range N, ∫ x in gridPoint N i..gridPoint N (i + 1), f x) =
      ∫ x in -(1 / 2 : ℝ)..1 / 2, f x := by
  have h := sum_integral_adjacent_intervals (a := gridPoint N) (n := N) (f := f) (μ := volume)
    (fun _ _ => hf.intervalIntegrable _ _)
  simpa only [gridPoint, Nat.cast_zero, zero_div, add_zero,
    div_self (by exact_mod_cast hN.ne' : (N : ℝ) ≠ 0),
    show (-(1 / 2 : ℝ)) + 1 = 1 / 2 by norm_num] using h

theorem sum_range_drop (a : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ Finset.range N, (a i - a (i + 1))) = a 0 - a N := by
  induction N with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, sub_self]
  | succ N ih => rw [Finset.sum_range_succ, ih]; ring

/-- Summing the sharp C¹ cell error gives a telescoping endpoint derivative drop. -/
theorem integral_sub_gridTrap_le {N : ℕ} (hN : 0 < N) {f f' : ℝ → ℝ}
    (hdf : ∀ x, HasDerivAt f (f' x) x) (hcont : Continuous f')
    (hanti : AntitoneOn f' (Icc (-(1 / 2)) (1 / 2))) :
    (∫ x in -(1 / 2 : ℝ)..1 / 2, f x) - gridTrap N f ≤
      (N : ℝ)⁻¹ ^ 2 / 8 * (f' (-(1 / 2)) - f' (1 / 2)) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hf : Continuous f := continuous_iff_continuousAt.2 (fun x => (hdf x).continuousAt)
  have hcell (i : ℕ) (hi : i ∈ Finset.range N) :
      (∫ x in gridPoint N i..gridPoint N (i + 1), f x) -
        (N : ℝ)⁻¹ * ((f (gridPoint N i) + f (gridPoint N (i + 1))) / 2) ≤
      (N : ℝ)⁻¹ ^ 2 / 8 * (f' (gridPoint N i) - f' (gridPoint N (i + 1))) := by
    have hia := gridPoint_mem hN (Nat.le_of_lt (Finset.mem_range.mp hi))
    have hib := gridPoint_mem (i := i + 1) hN (Nat.succ_le_of_lt (Finset.mem_range.mp hi))
    have hab : gridPoint N i ≤ gridPoint N (i + 1) := by
      apply sub_nonneg.mp
      rw [gridPoint_step]
      positivity
    have h := trapezoid_error_le_derivative_drop hab hdf hcont
      (hanti.mono (fun x hx => ⟨le_trans hia.1 hx.1, le_trans hx.2 hib.2⟩))
    rw [gridPoint_step] at h
    convert h using 1; ring
  have hsum := Finset.sum_le_sum hcell
  rw [Finset.sum_sub_distrib, grid_integral_sum hN hf, ← Finset.mul_sum,
    ← Finset.mul_sum, sum_range_drop (fun i => f' (gridPoint N i)) N] at hsum
  simpa only [gridTrap, gridPoint, Nat.cast_zero, zero_div, add_zero, div_self hN0, show (-(1 / 2 : ℝ)) + 1 = 1 / 2 by norm_num] using hsum

/-- Discrete variation is bounded by the integral of the absolute derivative. -/
theorem grid_variation_le {N : ℕ} (hN : 0 < N) {f f' : ℝ → ℝ}
    (hdf : ∀ x, HasDerivAt f (f' x) x) (hcont : Continuous f') :
    (∑ i ∈ Finset.range N, |f (gridPoint N (i + 1)) - f (gridPoint N i)|) ≤
      ∫ x in -(1 / 2 : ℝ)..1 / 2, |f' x| := by
  rw [← grid_integral_sum (f := fun x => |f' x|) hN hcont.abs]
  apply Finset.sum_le_sum
  intro i _
  have hab : gridPoint N i ≤ gridPoint N (i + 1) := by
    apply sub_nonneg.mp
    rw [gridPoint_step]
    positivity
  rw [← integral_eq_sub_of_hasDerivAt (fun x _ => hdf x) (hcont.intervalIntegrable _ _)]
  exact abs_integral_le_integral_abs hab

/-- Endpoint minima differ from trapezoids by half the discrete variation. -/
theorem gridMin_eq_gridTrap_sub_variation (N : ℕ) (f : ℝ → ℝ) :
    gridMin N f = gridTrap N f - (N : ℝ)⁻¹ / 2 *
      ∑ i ∈ Finset.range N, |f (gridPoint N (i + 1)) - f (gridPoint N i)| := by
  have hmin (a b : ℝ) : min a b = (a + b) / 2 - |b - a| / 2 := by
    rcases le_total a b with h | h
    · rw [min_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]; ring
    · rw [min_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
  unfold gridMin gridTrap
  simp_rw [hmin, Finset.sum_sub_distrib, ← Finset.sum_div]
  ring

end GMCExplicitDelta.Haar
