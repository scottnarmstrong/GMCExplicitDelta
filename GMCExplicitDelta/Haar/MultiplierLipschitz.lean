module

public import GMCExplicitDelta.Haar.CutoffProfile
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-! Lipschitz gluing and absolute continuity of the plateau slope. -/
@[expose] public section

open Real Set
open scoped NNReal

namespace GMCExplicitDelta.Haar

/-- Gluing Lipschitz real functions at a common value preserves their constant. -/
theorem lipschitzWith_joinAt {K : ℝ≥0} {f g : ℝ → ℝ} (c : ℝ)
    (hf : LipschitzWith K f) (hg : LipschitzWith K g) (hfg : f c = g c) :
    LipschitzWith K (joinAt c f g) := by
  have hle (x y : ℝ) (hxy : x ≤ y) :
      dist (joinAt c f g x) (joinAt c f g y) ≤ K * dist x y := by
    by_cases hx : x ≤ c
    · by_cases hy : y ≤ c
      · simpa only [joinAt, ite_eq_left hx, ite_eq_left hy] using hf.dist_le_mul x y
      · have hcy : c ≤ y := (lt_of_not_ge hy).le
        rw [joinAt, ite_eq_left hx, joinAt, ite_eq_right hy]
        calc
          dist (f x) (g y) ≤ dist (f x) (f c) + dist (f c) (g y) := dist_triangle _ _ _
          _ ≤ K * dist x c + K * dist c y := by
            rw [hfg]
            exact add_le_add (by simpa only [← hfg] using hf.dist_le_mul x c) (hg.dist_le_mul c y)
          _ = K * dist x y := by
            rw [Real.dist_eq, Real.dist_eq, Real.dist_eq,
              abs_of_nonpos (sub_nonpos.mpr hx), abs_of_nonpos (sub_nonpos.mpr hcy),
              abs_of_nonpos (sub_nonpos.mpr hxy)]
            ring
    · have hy : ¬ y ≤ c := fun hy => hx (hxy.trans hy)
      simpa only [joinAt, ite_eq_right hx, ite_eq_right hy] using hg.dist_le_mul x y
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rcases le_total x y with h | h
  · exact hle x y h
  · simpa only [dist_comm] using hle y x h

theorem neg_mul_sin_affine_hasDerivAt (κ a x : ℝ) :
    HasDerivAt (fun y => -κ * sin (κ * (y - a)))
      (-κ ^ 2 * cos (κ * (x - a))) x := by
  simpa only [id_eq, mul_one, mul_neg, neg_mul, pow_two, mul_assoc, mul_comm, mul_left_comm] using
    ((((hasDerivAt_id x).sub_const a).const_mul κ).sin.const_mul (-κ))

theorem lipschitzWith_neg_mul_sin_affine (κ a : ℝ) :
    LipschitzWith ⟨κ ^ 2, sq_nonneg κ⟩ (fun y => -κ * sin (κ * (y - a))) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun x => (neg_mul_sin_affine_hasDerivAt κ a x).differentiableAt)
  intro x
  rw [(neg_mul_sin_affine_hasDerivAt κ a x).deriv]
  change ‖-κ ^ 2 * cos (κ * (x - a))‖ ≤ κ ^ 2
  rw [Real.norm_eq_abs]
  rw [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg _)]
  exact (mul_le_mul_of_nonneg_left (abs_cos_le_one _) (sq_nonneg _)).trans_eq (mul_one _)

/-- The first derivative of the plateau profile is globally Lipschitz, including
across both interfaces where its own derivative may jump. -/
theorem cutoffSlope_lipschitzWith {ω : ℝ} (hω : ω ≤ 1 / 2) :
    LipschitzWith ⟨(π / (2 * ω)) ^ 2, sq_nonneg _⟩ (cutoffSlope ω) := by
  have ha : -(1 / 2 - ω) ≤ 1 / 2 - ω := by linarith only [hω]
  have hc : LipschitzWith ⟨(π / (2 * ω)) ^ 2, sq_nonneg _⟩ (fun _ : ℝ => (0 : ℝ)) :=
    (LipschitzWith.const 0).weaken (by exact zero_le)
  have hin := lipschitzWith_joinAt (1 / 2 - ω) hc
    (lipschitzWith_neg_mul_sin_affine (π / (2 * ω)) (1 / 2 - ω)) (by simp)
  unfold cutoffSlope
  apply lipschitzWith_joinAt _
    (by simpa only [sub_neg_eq_add] using
      lipschitzWith_neg_mul_sin_affine (π / (2 * ω)) (-(1 / 2 - ω))) hin
  simp only [neg_add_cancel, mul_zero, sin_zero, mul_zero, joinAt, ite_eq_left ha]

end GMCExplicitDelta.Haar
