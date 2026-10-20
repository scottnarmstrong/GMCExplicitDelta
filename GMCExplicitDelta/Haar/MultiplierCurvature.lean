module

public import GMCExplicitDelta.Haar.MultiplierApprox
public import GMCExplicitDelta.Haar.MultiplierLipschitz
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The a.e. second derivative of the plateau profile and its smooth approximation. -/
@[expose] public section

open Real Set Filter MeasureTheory
open scoped Topology

namespace GMCExplicitDelta.Haar

noncomputable def cutoffCurvature (ω x : ℝ) : ℝ :=
  joinAt (-(1 / 2 - ω)) (fun y => -(π / (2 * ω)) ^ 2 * cos (π / (2 * ω) * (y + (1 / 2 - ω))))
    (joinAt (1 / 2 - ω) (fun _ => 0)
      (fun y => -(π / (2 * ω)) ^ 2 * cos (π / (2 * ω) * (y - (1 / 2 - ω))))) x

theorem deriv_joinAt_of_lt {c x : ℝ} {f g : ℝ → ℝ} (hx : x < c) :
    deriv (joinAt c f g) x = deriv f x := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
  exact ite_eq_left hy.le

theorem deriv_joinAt_of_gt {c x : ℝ} {f g : ℝ → ℝ} (hx : c < x) :
    deriv (joinAt c f g) x = deriv g x := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
  exact ite_eq_right (not_le.mpr hy)

/-- The only exceptional points are the two interfaces. -/
theorem deriv_cutoffSlope_of_ne {ω x : ℝ}
    (hl : x ≠ -(1 / 2 - ω)) (hr : x ≠ 1 / 2 - ω) :
    deriv (cutoffSlope ω) x = cutoffCurvature ω x := by
  unfold cutoffSlope cutoffCurvature
  by_cases hx : x ≤ -(1 / 2 - ω)
  · rw [deriv_joinAt_of_lt (lt_of_le_of_ne hx hl), joinAt, ite_eq_left hx]
    simpa only [sub_neg_eq_add] using
      (neg_mul_sin_affine_hasDerivAt (π / (2 * ω)) (-(1 / 2 - ω)) x).deriv
  · rw [deriv_joinAt_of_gt (lt_of_not_ge hx), joinAt, ite_eq_right hx]
    by_cases hy : x ≤ 1 / 2 - ω
    · rw [deriv_joinAt_of_lt (lt_of_le_of_ne hy hr), joinAt, ite_eq_left hy, deriv_const]
    · rw [deriv_joinAt_of_gt (lt_of_not_ge hy), joinAt, ite_eq_right hy]
      exact (neg_mul_sin_affine_hasDerivAt _ _ x).deriv

theorem cutoffCurvature_ae_eq_deriv (ω : ℝ) :
    cutoffCurvature ω =ᵐ[volume] deriv (cutoffSlope ω) := by
  filter_upwards [volume.ae_ne (-(1 / 2 - ω)), volume.ae_ne (1 / 2 - ω)] with x hl hr
  exact (deriv_cutoffSlope_of_ne hl hr).symm

theorem layerSwitch_eventuallyEq_zero {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n)
    {c x : ℝ} (hx : x ≤ c) :
    (fun n => layerSwitch c (ε n) x) =ᶠ[atTop] fun _ => 0 := by
  filter_upwards with n
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) (hε n).le

theorem layerSwitch_eventuallyEq_one {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n)
    (hεlim : Tendsto ε atTop (𝓝 0)) {c x : ℝ} (hx : c < x) :
    (fun n => layerSwitch c (ε n) x) =ᶠ[atTop] fun _ => 1 := by
  filter_upwards [(tendsto_order.1 hεlim).2 (x - c) (sub_pos.mpr hx)] with n hn
  apply Real.smoothTransition.one_of_one_le
  exact (le_div_iff₀ (hε n)).mpr (by simpa only [one_mul] using hn.le)

/-- At every point the approximated curvature eventually equals its chosen
one-sided representative. -/
theorem curvatureApprox_eventuallyEq {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n)
    (hεlim : Tendsto ε atTop (𝓝 0)) {ω x : ℝ} (hω : ω ≤ 1 / 2) :
    (fun n => curvatureApprox ω (ε n) x) =ᶠ[atTop] fun _ => cutoffCurvature ω x := by
  have ha : -(1 / 2 - ω) ≤ 1 / 2 - ω := by linarith only [hω]
  by_cases hx : x ≤ -(1 / 2 - ω)
  · filter_upwards [layerSwitch_eventuallyEq_zero hε hx,
      layerSwitch_eventuallyEq_zero hε (hx.trans ha)] with n hn hm
    simp only [curvatureApprox, hn, hm, cutoffCurvature, joinAt, ite_eq_left hx,
      sub_zero, one_mul, zero_mul, add_zero]
  · have hx' : -(1 / 2 - ω) < x := lt_of_not_ge hx
    by_cases hy : x ≤ 1 / 2 - ω
    · filter_upwards [layerSwitch_eventuallyEq_one hε hεlim hx',
        layerSwitch_eventuallyEq_zero hε hy] with n hn hm
      simp only [curvatureApprox, hn, hm, cutoffCurvature, joinAt, ite_eq_right hx,
        ite_eq_left hy, sub_self, zero_mul, add_zero, mul_zero]
    · filter_upwards [layerSwitch_eventuallyEq_one hε hεlim hx',
        layerSwitch_eventuallyEq_one hε hεlim (lt_of_not_ge hy)] with n hn hm
      simp only [curvatureApprox, hn, hm, cutoffCurvature, joinAt, ite_eq_right hx,
        ite_eq_right hy, sub_self, zero_mul, zero_add, one_mul]

theorem primitive_cutoffCurvature {ω : ℝ} (hω : ω ≤ 1 / 2) (x : ℝ) :
    primitive (cutoffCurvature ω) x = cutoffSlope ω x := by
  unfold primitive
  calc
    (∫ t in (0 : ℝ)..x, cutoffCurvature ω t) = ∫ t in (0 : ℝ)..x, deriv (cutoffSlope ω) t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [cutoffCurvature_ae_eq_deriv ω] with t ht
      exact fun _ => ht
    _ = cutoffSlope ω x - cutoffSlope ω 0 :=
      (cutoffSlope_lipschitzWith hω).lipschitzOnWith.absolutelyContinuousOnInterval.integral_deriv_eq_sub
    _ = cutoffSlope ω x := by rw [cutoffSlope_zero hω, sub_zero]

/-- Dominated convergence for primitives on a fixed finite interval. -/
theorem primitive_tendsto_of_dominated {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {C : ℝ}
    (hF : ∀ n, Continuous (F n)) (hb : ∀ n t, ‖F n t‖ ≤ C)
    (hlim : ∀ᵐ t ∂volume, Tendsto (fun n => F n t) atTop (𝓝 (f t))) (x : ℝ) :
    Tendsto (fun n => primitive (F n) x) atTop (𝓝 (primitive f x)) := by
  have : IsFiniteMeasure (volume.restrict (uIoc 0 x)) := Real.isFiniteMeasure_restrict_Ioc _ _
  have hi := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (uIoc 0 x)) (fun _ => C)
    (fun n => (hF n).aestronglyMeasurable)
    (integrable_const C)
    (fun n => Filter.Eventually.of_forall (hb n)) (ae_restrict_of_ae hlim)
  simpa only [primitive, intervalIntegral.intervalIntegral_eq_integral_uIoc] using
    hi.const_smul (if (0 : ℝ) ≤ x then (1 : ℝ) else -1)

theorem slopeApprox_tendsto {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n)
    (hεlim : Tendsto ε atTop (𝓝 0)) {ω : ℝ} (hω : ω ≤ 1 / 2) (x : ℝ) :
    Tendsto (fun n => slopeApprox ω (ε n) x) atTop (𝓝 (cutoffSlope ω x)) := by
  rw [← primitive_cutoffCurvature hω x]
  apply primitive_tendsto_of_dominated
    (fun n => (curvatureApprox_contDiff ω (ε n)).continuous)
    (fun n t => by simpa only [Real.norm_eq_abs] using abs_curvatureApprox_le ω (ε n) t)
  filter_upwards with t
  exact tendsto_const_nhds.congr' (curvatureApprox_eventuallyEq hε hεlim hω).symm

theorem cutoffCurvature_sq_le (ω x : ℝ) :
    cutoffCurvature ω x ^ 2 ≤ (π / (2 * ω)) ^ 4 * cutoffProfile ω x ^ 2 := by
  unfold cutoffCurvature cutoffProfile joinAt
  split_ifs
  · exact le_of_eq (by ring)
  · nlinarith only [sq_nonneg ((π / (2 * ω)) ^ 2)]
  · exact le_of_eq (by ring)

theorem cutoffSlope_mul_curvature_add (ω x : ℝ) :
    cutoffSlope ω x * (cutoffCurvature ω x + (π / (2 * ω)) ^ 2 * cutoffProfile ω x) = 0 := by
  unfold cutoffSlope cutoffCurvature cutoffProfile joinAt
  split_ifs <;> ring

theorem cutoffCurvature_measurable (ω : ℝ) : Measurable (cutoffCurvature ω) := by
  unfold cutoffCurvature joinAt
  apply Measurable.ite (measurableSet_le measurable_id measurable_const)
  · fun_prop
  · apply Measurable.ite (measurableSet_le measurable_id measurable_const)
    · fun_prop
    · fun_prop

/-- The normalized profile, slope, and curvature satisfy the two-column
oscillator contraction relations, even at an interface. -/
theorem cutoff_oscillator_relations {ω : ℝ} (hω0 : 0 < ω) (x : ℝ) :
    let κ := π / (2 * ω)
    cutoffProfile ω x ^ 2 + (cutoffSlope ω x / κ) ^ 2 = 1 ∧
      (cutoffCurvature ω x / κ ^ 2) ^ 2 + (cutoffSlope ω x / κ) ^ 2 ≤ 1 ∧
      (cutoffSlope ω x / κ) * (cutoffCurvature ω x / κ ^ 2 + cutoffProfile ω x) = 0 := by
  dsimp only
  let κ := π / (2 * ω)
  have hk : κ ≠ 0 := ne_of_gt (div_pos pi_pos (mul_pos (by norm_num) hω0))
  have hs : (cutoffSlope ω x / κ) ^ 2 = 1 - cutoffProfile ω x ^ 2 := by
    rw [div_pow, cutoffSlope_sq]
    exact mul_div_cancel_left₀ _ (pow_ne_zero 2 hk)
  have hc : (cutoffCurvature ω x / κ ^ 2) ^ 2 ≤ cutoffProfile ω x ^ 2 := by
    calc
      (cutoffCurvature ω x / κ ^ 2) ^ 2 = cutoffCurvature ω x ^ 2 / κ ^ 4 := by
        rw [div_pow, ← pow_mul]
      _ ≤ (κ ^ 4 * cutoffProfile ω x ^ 2) / κ ^ 4 :=
        div_le_div_of_nonneg_right (cutoffCurvature_sq_le ω x) (pow_nonneg (by positivity) _)
      _ = cutoffProfile ω x ^ 2 := mul_div_cancel_left₀ _ (pow_ne_zero 4 hk)
  refine ⟨?_, ?_, ?_⟩
  · change cutoffProfile ω x ^ 2 + (cutoffSlope ω x / κ) ^ 2 = 1
    rw [hs]
    ring
  · change (cutoffCurvature ω x / κ ^ 2) ^ 2 + (cutoffSlope ω x / κ) ^ 2 ≤ 1
    rw [hs]
    linarith only [hc]
  · change (cutoffSlope ω x / κ) * (cutoffCurvature ω x / κ ^ 2 + cutoffProfile ω x) = 0
    calc
      _ = cutoffSlope ω x * (cutoffCurvature ω x + κ ^ 2 * cutoffProfile ω x) / κ ^ 3 := by
        field_simp [hk]
      _ = 0 := by rw [cutoffSlope_mul_curvature_add, zero_div]

end GMCExplicitDelta.Haar
