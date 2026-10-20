module

public import GMCExplicitDelta.Proofs.HaarMode.Slope
public import GMCExplicitDelta.Proofs.HaarMode.Moments
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # Additional one-dimensional moments for the affine cutoff field -/

@[expose] public section

open MeasureTheory Homogenization Set Filter Real intervalIntegral
open scoped ENNReal

namespace GMCExplicitDelta.Localization

/-- Odd integrands have zero integral on the centered unit interval. -/
theorem haarMode_integral_odd {f : ℝ → ℝ} (hf : ∀ t, f (-t) = -f t) :
    (∫ t in -(1 / 2 : ℝ)..1 / 2, f t) = 0 := by
  have heq := integral_comp_neg (f := f) (a := -(1 / 2 : ℝ)) (b := 1 / 2)
  simp only [neg_neg] at heq
  simp_rw [hf] at heq
  rw [intervalIntegral.integral_neg] at heq
  linarith only [heq]

/-- The cutoff slope is odd. -/
theorem haarMode_slope_odd {ω : ℝ} (hω : ω ≤ 1 / 2) (t : ℝ) :
    Haar.cutoffSlope ω (-t) = -Haar.cutoffSlope ω t := by
  have hs : haarMode_soft ω (-t) = -haarMode_soft ω t := by
    unfold haarMode_soft
    simp only [neg_neg]
    ring
  rw [(haarMode_soft_trig hω (-t)).2, hs, mul_neg, sin_neg, (haarMode_soft_trig hω t).2]
  ring

/-- An even marginal weight has zero first moment. -/
theorem haarMode_first_moment_even {f : ℝ → ℝ} (hf : Function.Even f) :
    (∫ t in -(1 / 2 : ℝ)..1 / 2, t * f t) = 0 :=
  haarMode_integral_odd (fun t => by rw [hf]; ring)

/-- The squared profile has zero first moment. -/
theorem haarMode_profile_sq_first {ω : ℝ} (hω : ω ≤ 1 / 2) :
    (∫ t in -(1 / 2 : ℝ)..1 / 2, t * Haar.cutoffProfile ω t ^ 2) = 0 :=
  haarMode_first_moment_even (fun t => by rw [Haar.cutoffProfile_even hω])

/-- The squared slope has zero first moment. -/
theorem haarMode_slope_sq_first {ω : ℝ} (hω : ω ≤ 1 / 2) :
    (∫ t in -(1 / 2 : ℝ)..1 / 2, t * Haar.cutoffSlope ω t ^ 2) = 0 :=
  haarMode_first_moment_even (fun t => by rw [haarMode_slope_odd hω, neg_sq])

/-- The slope has zero average by parity. -/
theorem haarMode_slope_integral {ω : ℝ} (hω : ω ≤ 1 / 2) :
    (∫ t in -(1 / 2 : ℝ)..1 / 2, Haar.cutoffSlope ω t) = 0 :=
  haarMode_integral_odd (haarMode_slope_odd hω)

/-- Integration by parts identifies the affine first moment of the slope. -/
theorem haarMode_moment_slope {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1 / 2) :
    (∫ t in -(1 / 2 : ℝ)..1 / 2, t * Haar.cutoffSlope ω t) = -(1 - 2 * ω + 4 * ω / π) := by
  have h := integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := id) (v := Haar.cutoffProfile ω) (u' := fun _ => 1) (v' := Haar.cutoffSlope ω)
    (a := -(1 / 2 : ℝ)) (b := 1 / 2)
    continuous_id.continuousOn (Haar.cutoffProfile_contDiff hω1).continuous.continuousOn
    (fun t _ => hasDerivAt_id t) (fun t _ => Haar.cutoffProfile_hasDerivAt hω1 t)
    (continuous_const.intervalIntegrable _ _) ((Haar.cutoffSlope_continuous hω1).intervalIntegrable _ _)
  simpa only [id_eq, (Haar.cutoffProfile_endpoint hω0 hω1).1,
    (Haar.cutoffProfile_endpoint hω0 hω1).2, mul_zero, sub_self, one_mul, zero_sub,
    Haar.integral_cutoffProfile hω0 hω1] using h

/-- Integration by parts for the square of the profile. -/
theorem haarMode_profile_slope_moment {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1 / 2) :
    (∫ t in -(1 / 2 : ℝ)..1 / 2, t * Haar.cutoffProfile ω t * Haar.cutoffSlope ω t) =
      -(1 - ω) / 2 := by
  have h := integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := id) (v := fun t => Haar.cutoffProfile ω t ^ 2)
    (u' := fun _ => 1) (v' := fun t => 2 * Haar.cutoffProfile ω t * Haar.cutoffSlope ω t)
    (a := -(1 / 2 : ℝ)) (b := 1 / 2)
    continuous_id.continuousOn ((Haar.cutoffProfile_contDiff hω1).continuous.pow 2).continuousOn
    (fun t _ => hasDerivAt_id t)
    (fun t _ => by convert! (Haar.cutoffProfile_hasDerivAt hω1 t).pow 2 using 1; ring)
    (continuous_const.intervalIntegrable _ _)
    (((continuous_const.mul (Haar.cutoffProfile_contDiff hω1).continuous).mul
      (Haar.cutoffSlope_continuous hω1)).intervalIntegrable _ _)
  have heq : (fun t => t * (2 * Haar.cutoffProfile ω t * Haar.cutoffSlope ω t)) =
      fun t => 2 * (t * Haar.cutoffProfile ω t * Haar.cutoffSlope ω t) := by funext t; ring
  simp only [id_eq, (Haar.cutoffProfile_endpoint hω0 hω1).1,
    (Haar.cutoffProfile_endpoint hω0 hω1).2, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    mul_zero, sub_self, one_mul, zero_sub, Haar.integral_cutoffProfile_sq hω0 hω1] at h
  rw [heq, intervalIntegral.integral_const_mul] at h
  linarith only [h]

end GMCExplicitDelta.Localization
