module

public import GMCExplicitDelta.Proofs.HaarMode.Cutoff1D

/-! # Layer curvature and its exact one-dimensional moments -/

@[expose] public section

open MeasureTheory Homogenization Set Filter Real
open scoped ENNReal

namespace GMCExplicitDelta.Localization

/-- The a.e. second derivative of the plateau-cosine profile. -/
noncomputable def haarMode_curvature (ω t : ℝ) : ℝ :=
  -(π / (2 * ω)) ^ 2 * (if 1 / 2 - ω < |t| then Haar.cutoffProfile ω t else 0)

/-- Integrating a layer-restricted continuous function gives the two layer integrals. -/
theorem haarMode_integral_layer {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1 / 2)
    {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ t in -(1 / 2 : ℝ)..1 / 2, if 1 / 2 - ω < |t| then f t else 0) =
      Haar.layerIntegral ω f := by
  let a : ℝ := 1 / 2 - ω
  have ha : 0 ≤ a := sub_nonneg.2 hω1
  have ha1 : a ≤ 1 / 2 := by dsimp [a]; linarith
  have hpoint (t : ℝ) (ht : t ≠ -a) :
      (if a < |t| then f t else 0) = f t - (Ioc (-a) a).indicator f t := by
    by_cases hab : a < |t|
    · have hnot : t ∉ Ioc (-a) a := by
        intro hmem
        exact not_le_of_gt hab (abs_le.2 ⟨hmem.1.le, hmem.2⟩)
      simp only [hab, ite_true, indicator_of_notMem hnot, sub_zero]
    · have hle : |t| ≤ a := le_of_not_gt hab
      have hmem : t ∈ Ioc (-a) a := ⟨lt_of_le_of_ne (abs_le.1 hle).1 (Ne.symm ht), (abs_le.1 hle).2⟩
      simp only [hab, ite_false, indicator_of_mem hmem, sub_self]
  have heq : (∫ t in -(1 / 2 : ℝ)..1 / 2, if a < |t| then f t else 0) =
      ∫ t in -(1 / 2 : ℝ)..1 / 2, f t - (Ioc (-a) a).indicator f t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne (-a)] with t ht
    intro _
    exact hpoint t ht
  have hfi := hf.intervalIntegrable (μ := volume) (a := -(1 / 2 : ℝ)) (b := 1 / 2)
  have hii : IntervalIntegrable ((Ioc (-a) a).indicator f) volume (-(1 / 2 : ℝ)) (1 / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).2
      (((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1 hfi).indicator measurableSet_Ioc)
  have hsub : Ioc (-a) a ⊆ Ioc (-(1 / 2 : ℝ)) (1 / 2) := by
    intro t ht
    exact ⟨lt_of_le_of_lt (by linarith) ht.1, ht.2.trans ha1⟩
  have hi : (∫ t in -(1 / 2 : ℝ)..1 / 2, (Ioc (-a) a).indicator f t) = ∫ t in -a..a, f t := by
    rw [intervalIntegral.integral_of_le (by norm_num), MeasureTheory.integral_indicator measurableSet_Ioc,
      Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.2 hsub,
      ← intervalIntegral.integral_of_le (by linarith : -a ≤ a)]
  rw [heq, intervalIntegral.integral_sub hfi hii, hi]
  have h := Haar.integral_eq_layerIntegral_add_middle (ω := ω) hf
  change (∫ t in -(1 / 2 : ℝ)..1 / 2, f t) - (∫ t in -a..a, f t) = _
  linarith only [h]

/-- The curvature is even. -/
theorem haarMode_curvature_even {ω : ℝ} (hω : ω ≤ 1 / 2) : Function.Even (haarMode_curvature ω) := by
  intro t
  unfold haarMode_curvature
  rw [abs_neg, Haar.cutoffProfile_even hω]

/-- Curvature-square integrands are the corresponding layer moments. -/
theorem haarMode_curvature_sq (ω t : ℝ) :
    haarMode_curvature ω t ^ 2 = (π / (2 * ω)) ^ 4 *
      (if 1 / 2 - ω < |t| then Haar.cutoffProfile ω t ^ 2 else 0) := by
  unfold haarMode_curvature
  split_ifs <;> ring

/-- The total curvature-square mass. -/
theorem haarMode_curvature_sq_integral {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1 / 2) :
    (∫ t in -(1 / 2 : ℝ)..1 / 2, haarMode_curvature ω t ^ 2) = (π / (2 * ω)) ^ 4 * ω := by
  simp_rw [haarMode_curvature_sq]
  rw [intervalIntegral.integral_const_mul, haarMode_integral_layer (f := fun t => Haar.cutoffProfile ω t ^ 2) hω0 hω1
    ((Haar.cutoffProfile_contDiff hω1).continuous.pow 2), Haar.layerIntegral_profile_sq hω0 hω1]

/-- The second moment of curvature-square mass. -/
theorem haarMode_curvature_sq_moment {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1 / 2) :
    (∫ t in -(1 / 2 : ℝ)..1 / 2, t ^ 2 * haarMode_curvature ω t ^ 2) =
      (π / (2 * ω)) ^ 4 * (ω / 4 - ω ^ 2 / 2 + ω ^ 3 / 3 - 2 * ω ^ 2 * (1 - ω) / π ^ 2) := by
  have heq (t : ℝ) : t ^ 2 * haarMode_curvature ω t ^ 2 = (π / (2 * ω)) ^ 4 *
      (if 1 / 2 - ω < |t| then t ^ 2 * Haar.cutoffProfile ω t ^ 2 else 0) := by
    rw [haarMode_curvature_sq]
    split_ifs <;> ring
  simp_rw [heq]
  rw [intervalIntegral.integral_const_mul, haarMode_integral_layer (f := fun t => t ^ 2 * Haar.cutoffProfile ω t ^ 2) hω0 hω1
    ((continuous_id.pow 2).mul ((Haar.cutoffProfile_contDiff hω1).continuous.pow 2)),
    Haar.layerIntegral_moment_profile_sq hω0 hω1]

/-- The slope vanishes throughout the plateau. -/
theorem haarMode_slope_plateau {ω t : ℝ} (hω1 : ω ≤ 1 / 2) (ht : |t| ≤ 1 / 2 - ω) :
    Haar.cutoffSlope ω t = 0 := by
  have h : Haar.cutoffSlope ω t ^ 2 = 0 := by
    rw [Haar.cutoffSlope_sq, Haar.cutoffProfile_plateau hω1 ht]
    ring
  exact (sq_eq_zero_iff).1 h

/-- The mixed slope-curvature moment, including the boundary contribution. -/
theorem haarMode_slope_curvature_moment {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1 / 2) :
    (∫ t in -(1 / 2 : ℝ)..1 / 2, t * Haar.cutoffSlope ω t * haarMode_curvature ω t) =
      (π / (2 * ω)) ^ 2 * (1 - ω) / 2 := by
  have heq (t : ℝ) : t * Haar.cutoffSlope ω t * haarMode_curvature ω t =
      -(π / (2 * ω)) ^ 2 * (t * Haar.cutoffProfile ω t * Haar.cutoffSlope ω t) := by
    unfold haarMode_curvature
    split_ifs with ht
    · ring
    · rw [haarMode_slope_plateau hω1 (le_of_not_gt ht)]
      ring
  simp_rw [heq]
  rw [intervalIntegral.integral_const_mul, haarMode_profile_slope_moment hω0 hω1]
  ring

/-- The profile-curvature mass is the negative layer mass times the frequency squared. -/
theorem haarMode_profile_curvature_integral {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1 / 2) :
    (∫ t in -(1 / 2 : ℝ)..1 / 2, Haar.cutoffProfile ω t * haarMode_curvature ω t) =
      -(π / (2 * ω)) ^ 2 * ω := by
  have heq (t : ℝ) : Haar.cutoffProfile ω t * haarMode_curvature ω t =
      -(π / (2 * ω)) ^ 2 * (if 1 / 2 - ω < |t| then Haar.cutoffProfile ω t ^ 2 else 0) := by
    unfold haarMode_curvature
    split_ifs <;> ring
  simp_rw [heq]
  rw [intervalIntegral.integral_const_mul,
    haarMode_integral_layer (f := fun t => Haar.cutoffProfile ω t ^ 2) hω0 hω1
      ((Haar.cutoffProfile_contDiff hω1).continuous.pow 2), Haar.layerIntegral_profile_sq hω0 hω1]

end GMCExplicitDelta.Localization
