module

public import GMCExplicitDelta.Haar.MultiplierCurvature

/-! Convergence of smooth profile approximations, including their first derivatives. -/
@[expose] public section

open Real Set Filter MeasureTheory
open scoped Topology

namespace GMCExplicitDelta.Haar

theorem primitive_cutoffSlope {ω : ℝ} (hω : ω ≤ 1 / 2) (x : ℝ) :
    primitive (cutoffSlope ω) x = cutoffProfile ω x - 1 := by
  unfold primitive
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => cutoffProfile_hasDerivAt hω t)
    ((cutoffSlope_continuous hω).intervalIntegrable _ _)]
  have h0 : cutoffProfile ω 0 = 1 := cutoffProfile_plateau hω
    (by simpa only [abs_zero] using sub_nonneg.mpr hω)
  rw [h0]

theorem profileApprox_tendsto {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n)
    (hεlim : Tendsto ε atTop (𝓝 0)) {ω : ℝ} (hω : ω ≤ 1 / 2) (x : ℝ) :
    Tendsto (fun n => profileApprox ω (ε n) x) atTop (𝓝 (cutoffProfile ω x)) := by
  have : IsFiniteMeasure (volume.restrict (uIoc 0 x)) := Real.isFiniteMeasure_restrict_Ioc _ _
  have hi := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (uIoc 0 x)) (fun _ => 2 * (π / (2 * ω)) ^ 2 * |x|)
    (fun n => (slopeApprox_contDiff ω (ε n)).continuous.aestronglyMeasurable)
    (integrable_const _)
    (fun n => by
      filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
      exact (norm_slopeApprox_le ω (ε n) t).trans
        (mul_le_mul_of_nonneg_left (abs_le_abs_of_mem_zero_uIoc ht) (by positivity)))
    (Filter.Eventually.of_forall (slopeApprox_tendsto hε hεlim hω))
  have hprim : Tendsto (fun n => primitive (slopeApprox ω (ε n)) x) atTop
      (𝓝 (primitive (cutoffSlope ω) x)) := by
    simpa only [primitive, intervalIntegral.intervalIntegral_eq_integral_uIoc] using
      hi.const_smul (if (0 : ℝ) ≤ x then (1 : ℝ) else -1)
  have he : 1 + primitive (cutoffSlope ω) x = cutoffProfile ω x := by
    rw [primitive_cutoffSlope hω]
    ring
  simpa only [profileApprox, he] using hprim.const_add 1

end GMCExplicitDelta.Haar
