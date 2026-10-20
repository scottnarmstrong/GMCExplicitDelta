module

public import GMCExplicitDelta.Haar.CutoffProfile
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Exact primitive energies of mean-zero step functions on three equal cells. -/
@[expose] public section

open MeasureTheory Set
open scoped Topology

namespace GMCExplicitDelta.Localization.ProjPoincare

/-- A basic polynomial integral used for the three affine pieces. -/
theorem integral_affine_sq (a b c e : ℝ) :
    (∫ t in a..b, (c * t + e) ^ 2) =
      c ^ 2 / 3 * (b ^ 3 - a ^ 3) + c * e * (b ^ 2 - a ^ 2) + e ^ 2 * (b - a) := by
  have hd (t : ℝ) : HasDerivAt
      (fun t : ℝ => c ^ 2 / 3 * t ^ 3 + c * e * t ^ 2 + e ^ 2 * t) ((c * t + e) ^ 2) t := by
    convert ((((hasDerivAt_id t).pow 3).const_mul (c ^ 2 / 3)).add
      (((hasDerivAt_id t).pow 2).const_mul (c * e))).add
      ((hasDerivAt_id t).const_mul (e ^ 2)) using 1
    · funext y
      dsimp
    · dsimp
      ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (by exact Continuous.intervalIntegrable (by fun_prop) _ _)]
  ring

/-- The primitive of a step function on thirds, with its right-hand formula
written using the zero-mean relation. -/
noncomputable def thirdsPrimitive (b₀ b₁ b₂ x : ℝ) : ℝ :=
  Haar.joinAt (1 / 3) (fun t => b₀ * t)
    (Haar.joinAt (2 / 3) (fun t => b₀ / 3 + b₁ * (t - 1 / 3)) (fun t => -b₂ * (1 - t))) x

theorem thirdsPrimitive_continuous {b₀ b₁ b₂ : ℝ} (hb : b₀ + b₁ + b₂ = 0) :
    Continuous (thirdsPrimitive b₀ b₁ b₂) := by
  apply Haar.continuous_joinAt _ (by fun_prop)
    (Haar.continuous_joinAt _ (by fun_prop) (by fun_prop) (by linarith only [hb]))
  norm_num [Haar.joinAt]
  ring

theorem thirdsPrimitive_energy {b₀ b₁ b₂ : ℝ} (hb : b₀ + b₁ + b₂ = 0) :
    (∫ t in (0 : ℝ)..1, thirdsPrimitive b₀ b₁ b₂ t ^ 2) =
      (4 * b₀ ^ 2 + 3 * b₀ * b₁ + b₁ ^ 2 + b₂ ^ 2) / 81 := by
  have hc : Continuous (fun t => thirdsPrimitive b₀ b₁ b₂ t ^ 2) :=
    (thirdsPrimitive_continuous hb).pow 2
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 (1 / 3)) (hc.intervalIntegrable (1 / 3) 1)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (1 / 3) (2 / 3)) (hc.intervalIntegrable (2 / 3) 1)]
  have h0 : (∫ t in (0 : ℝ)..(1 / 3), thirdsPrimitive b₀ b₁ b₂ t ^ 2) =
      ∫ t in (0 : ℝ)..(1 / 3), (b₀ * t + 0) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    simp only [thirdsPrimitive, Haar.joinAt, ite_eq_left ht.2, add_zero]
  have h1 : (∫ t in (1 / 3 : ℝ)..(2 / 3), thirdsPrimitive b₀ b₁ b₂ t ^ 2) =
      ∫ t in (1 / 3 : ℝ)..(2 / 3), (b₁ * t + (b₀ - b₁) / 3) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    unfold thirdsPrimitive Haar.joinAt
    dsimp only
    rw [ite_eq_left ht.2]
    split_ifs with h
    · have he : t = 1 / 3 := le_antisymm h ht.1
      rw [he]
      ring
    · ring
  have h2 : (∫ t in (2 / 3 : ℝ)..1, thirdsPrimitive b₀ b₁ b₂ t ^ 2) =
      ∫ t in (2 / 3 : ℝ)..1, (b₂ * t - b₂) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    unfold thirdsPrimitive Haar.joinAt
    dsimp only
    rw [ite_eq_right (by linarith only [ht.1] : ¬ t ≤ (1 : ℝ) / 3)]
    split_ifs with h
    · have he : t = 2 / 3 := le_antisymm h ht.1
      rw [he]
      have hb' : b₀ = -b₁ - b₂ := by linarith only [hb]
      rw [hb']
      ring
    · ring
  rw [h0, h1, h2]
  simp_rw [sub_eq_add_neg, integral_affine_sq]
  ring

/-- H4's one-dimensional primitive estimate; the middle coefficient gives the
exact nonnegative remainder. -/
theorem thirdsPrimitive_energy_le {b₀ b₁ b₂ : ℝ} (hb : b₀ + b₁ + b₂ = 0) :
    (∫ t in (0 : ℝ)..1, thirdsPrimitive b₀ b₁ b₂ t ^ 2) ≤
      (5 / 54 : ℝ) * ((b₀ ^ 2 + b₁ ^ 2 + b₂ ^ 2) / 3) := by
  rw [thirdsPrimitive_energy hb]
  have hb' : b₂ = -b₀ - b₁ := by linarith only [hb]
  rw [hb']
  nlinarith only [sq_nonneg b₁]

end GMCExplicitDelta.Localization.ProjPoincare
