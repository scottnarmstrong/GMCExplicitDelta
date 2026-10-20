module

public import GMCExplicitDelta.Proofs.ProjPoincare.Primitive
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Function.L2Space

/-! Duality on thirds: the one-dimensional projected Poincaré estimate. -/
@[expose] public section

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

namespace GMCExplicitDelta.Localization.ProjPoincare

/-- The real L² Cauchy--Schwarz inequality in an integral-only form. -/
theorem integral_mul_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * ∫ x, g x ^ 2 ∂μ := by
  have he {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
      inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
    rw [hx, hy]
    simp only [RCLike.inner_apply', starRingEnd_apply, star_trivial]
  have h := real_inner_mul_inner_self_le (hf.toLp f) (hg.toLp g)
  rw [he hf hg, he hf hf, he hg hg] at h
  simpa only [pow_two] using h

/-- Integrating an affine factor against the derivative. -/
theorem affine_integration_by_parts {v g : ℝ → ℝ} (hv : Continuous v) (hg : Continuous g)
    (hd : ∀ t, HasDerivAt v (g t) t) (a b c e : ℝ) :
    (∫ t in a..b, (c * t + e) * g t) =
      (c * b + e) * v b - (c * a + e) * v a - c * ∫ t in a..b, v t := by
  have h' := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt (a := a) (b := b)
    (u := fun t => c * t + e) (u' := fun _ => c) (v := v) (v' := g)
    (by fun_prop) hv.continuousOn
    (fun t _ => by simpa only [id_eq, mul_one] using
      ((hasDerivAt_id t).const_mul c).add_const e) (fun t _ => hd t)
    (continuous_const.intervalIntegrable _ _) (hg.intervalIntegrable _ _)
  simpa only [intervalIntegral.integral_const_mul] using h'

/-- The primitive pairing identity on the unit interval. -/
theorem thirdsPrimitive_pairing {v g : ℝ → ℝ} (hv : Continuous v) (hg : Continuous g)
    (hd : ∀ t, HasDerivAt v (g t) t) {b₀ b₁ b₂ : ℝ} (hb : b₀ + b₁ + b₂ = 0) :
    (∫ t in (0 : ℝ)..1, thirdsPrimitive b₀ b₁ b₂ t * g t) =
      -(b₀ * (∫ t in (0 : ℝ)..(1 / 3), v t) +
        b₁ * (∫ t in (1 / 3 : ℝ)..(2 / 3), v t) + b₂ * (∫ t in (2 / 3 : ℝ)..1, v t)) := by
  have hc : Continuous (fun t => thirdsPrimitive b₀ b₁ b₂ t * g t) :=
    (thirdsPrimitive_continuous hb).mul hg
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 (1 / 3)) (hc.intervalIntegrable (1 / 3) 1)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (1 / 3) (2 / 3)) (hc.intervalIntegrable (2 / 3) 1)]
  have h0 : (∫ t in (0 : ℝ)..(1 / 3), thirdsPrimitive b₀ b₁ b₂ t * g t) =
      ∫ t in (0 : ℝ)..(1 / 3), (b₀ * t + 0) * g t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    simp only [thirdsPrimitive, Haar.joinAt, ite_eq_left ht.2, add_zero]
  have h1 : (∫ t in (1 / 3 : ℝ)..(2 / 3), thirdsPrimitive b₀ b₁ b₂ t * g t) =
      ∫ t in (1 / 3 : ℝ)..(2 / 3), (b₁ * t + (b₀ - b₁) / 3) * g t := by
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
  have h2 : (∫ t in (2 / 3 : ℝ)..1, thirdsPrimitive b₀ b₁ b₂ t * g t) =
      ∫ t in (2 / 3 : ℝ)..1, (b₂ * t - b₂) * g t := by
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
  simp_rw [sub_eq_add_neg, affine_integration_by_parts hv hg hd]
  have hb' : b₂ = -b₀ - b₁ := by linarith only [hb]
  rw [hb']
  ring

end GMCExplicitDelta.Localization.ProjPoincare
