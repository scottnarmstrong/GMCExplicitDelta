module

public import GMCExplicitDelta.Proofs.ProjPoincare.Scalar

/-! The projected Poincaré inequality for the three thirds of a unit interval. -/
@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace GMCExplicitDelta.Localization.ProjPoincare

theorem interval_integral_mul_sq_le {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, f t * g t) ^ 2 ≤
      (∫ t in a..b, f t ^ 2) * ∫ t in a..b, g t ^ 2 := by
  have hf2 : MemLp f 2 (volume.restrict (Ioc a b)) :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr ((hf.pow 2).intervalIntegrable a b).1
  have hg2 : MemLp g 2 (volume.restrict (Ioc a b)) :=
    (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).mpr ((hg.pow 2).intervalIntegrable a b).1
  simpa only [intervalIntegral.integral_of_le hab] using integral_mul_sq_le hf2 hg2

/-- Duality estimate for any mean-zero three-cell step field. -/
theorem thirds_pairing_sq_le {v g : ℝ → ℝ} (hv : Continuous v) (hg : Continuous g)
    (hd : ∀ t, HasDerivAt v (g t) t) {b₀ b₁ b₂ : ℝ} (hb : b₀ + b₁ + b₂ = 0) :
    (b₀ * (∫ t in (0 : ℝ)..(1 / 3), v t) +
      b₁ * (∫ t in (1 / 3 : ℝ)..(2 / 3), v t) + b₂ * (∫ t in (2 / 3 : ℝ)..1, v t)) ^ 2 ≤
      ((5 / 54 : ℝ) * ((b₀ ^ 2 + b₁ ^ 2 + b₂ ^ 2) / 3)) * ∫ t in (0 : ℝ)..1, g t ^ 2 := by
  have hcs := interval_integral_mul_sq_le (thirdsPrimitive_continuous hb) hg (by norm_num : (0 : ℝ) ≤ 1)
  rw [thirdsPrimitive_pairing hv hg hd hb, neg_sq] at hcs
  exact hcs.trans (mul_le_mul_of_nonneg_right (thirdsPrimitive_energy_le hb)
    (intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => sq_nonneg _)))

/-- The elementary three-cell variance bound, in terms of the three integrals. -/
theorem thirds_projected_poincare {v g : ℝ → ℝ} (hv : Continuous v) (hg : Continuous g)
    (hd : ∀ t, HasDerivAt v (g t) t) :
    let m := ∫ t in (0 : ℝ)..1, v t
    ((3 * (∫ t in (0 : ℝ)..(1 / 3), v t) - m) ^ 2 +
      (3 * (∫ t in (1 / 3 : ℝ)..(2 / 3), v t) - m) ^ 2 +
      (3 * (∫ t in (2 / 3 : ℝ)..1, v t) - m) ^ 2) / 3 ≤
      (5 / 54 : ℝ) * ∫ t in (0 : ℝ)..1, g t ^ 2 := by
  let A := ∫ t in (0 : ℝ)..(1 / 3), v t
  let B := ∫ t in (1 / 3 : ℝ)..(2 / 3), v t
  let C := ∫ t in (2 / 3 : ℝ)..1, v t
  let m := ∫ t in (0 : ℝ)..1, v t
  have hm : m = A + B + C := by
    dsimp only [m, A, B, C]
    rw [intervalIntegral.integral_add_adjacent_intervals (hv.intervalIntegrable _ _) (hv.intervalIntegrable _ _),
      intervalIntegral.integral_add_adjacent_intervals (hv.intervalIntegrable _ _) (hv.intervalIntegrable _ _)]
  let E := ((3 * A - m) ^ 2 + (3 * B - m) ^ 2 + (3 * C - m) ^ 2) / 3
  have hb : (3 * A - m) + (3 * B - m) + (3 * C - m) = 0 := by rw [hm]; ring
  have hp : (3 * A - m) * A + (3 * B - m) * B + (3 * C - m) * C = E := by
    dsimp only [E]
    rw [hm]
    ring
  have h := thirds_pairing_sq_le hv hg hd hb
  change ((3 * A - m) * A + (3 * B - m) * B + (3 * C - m) * C) ^ 2 ≤
    ((5 / 54 : ℝ) * E) * (∫ t in (0 : ℝ)..1, g t ^ 2) at h
  rw [hp] at h
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hg0 : 0 ≤ ∫ t in (0 : ℝ)..1, g t ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => sq_nonneg _)
  change E ≤ _
  nlinarith only [h, hE, hg0]

end GMCExplicitDelta.Localization.ProjPoincare
