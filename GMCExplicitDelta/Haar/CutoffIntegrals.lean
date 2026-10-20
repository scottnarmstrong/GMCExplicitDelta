module

public import GMCExplicitDelta.Haar.CutoffProfile
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! H10: one-dimensional cutoff integrals and the contract constants. -/
@[expose] public section

namespace GMCExplicitDelta.Haar

open Real intervalIntegral
open MeasureTheory (volume)

/-- Reflection reduces the full interval integral of an even continuous function. -/
theorem integral_even_unit {f : ℝ → ℝ} (hf : Continuous f) (he : Function.Even f) :
    (∫ x in -(1 / 2 : ℝ)..1 / 2, f x) = 2 * ∫ x in (0 : ℝ)..1 / 2, f x := by
  have hneg : (∫ x in -(1 / 2 : ℝ)..0, f x) = ∫ x in (0 : ℝ)..1 / 2, f x := by
    calc
      (∫ x in -(1 / 2 : ℝ)..0, f x) = ∫ x in -(1 / 2 : ℝ)..0, f (-x) := by
        apply integral_congr
        intro x _
        dsimp only
        exact (he x).symm
      _ = ∫ x in (0 : ℝ)..1 / 2, f x := by rw [integral_comp_neg]; simp only [neg_zero, neg_neg]
  have hadd := integral_add_adjacent_intervals
    (hf.intervalIntegrable (μ := volume) (a := -(1 / 2 : ℝ)) (b := 0))
    (hf.intervalIntegrable (μ := volume) (a := 0) (b := 1 / 2))
  rw [hneg] at hadd
  linarith only [hadd]

/-- Every power has a constant plateau and a rescaled cosine layer. -/
theorem integral_cutoffProfile_pow {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1 / 2) (n : ℕ) :
    (∫ x in -(1 / 2 : ℝ)..1 / 2, cutoffProfile ω x ^ n) =
      1 - 2 * ω + 2 * ∫ t in (0 : ℝ)..ω, cos (π / (2 * ω) * t) ^ n := by
  have hf := (cutoffProfile_contDiff hω1).continuous
  have ha : 0 ≤ 1 / 2 - ω := sub_nonneg.mpr hω1
  rw [integral_even_unit (f := fun x => cutoffProfile ω x ^ n) (hf.pow n) (fun x => by dsimp only; rw [cutoffProfile_even hω1 x])]
  have hp : (∫ x in (0 : ℝ)..(1 / 2 - ω), cutoffProfile ω x ^ n) = 1 / 2 - ω := by
    calc
      (∫ x in (0 : ℝ)..(1 / 2 - ω), cutoffProfile ω x ^ n) = ∫ x in (0 : ℝ)..(1 / 2 - ω), (1 : ℝ) := by
        apply integral_congr
        intro x hx
        dsimp only
        rw [Set.uIcc_of_le ha] at hx
        rw [cutoffProfile_plateau hω1 (by rw [abs_of_nonneg hx.1]; exact hx.2), one_pow]
      _ = 1 / 2 - ω := by simp only [integral_const, smul_eq_mul, sub_zero, mul_one]
  have hl : (∫ x in (1 / 2 - ω)..(1 / 2 : ℝ), cutoffProfile ω x ^ n) =
      ∫ t in (0 : ℝ)..ω, cos (π / (2 * ω) * t) ^ n := by
    calc
      (∫ x in (1 / 2 - ω)..(1 / 2 : ℝ), cutoffProfile ω x ^ n) =
          ∫ t in (0 : ℝ)..ω, cutoffProfile ω (t + (1 / 2 - ω)) ^ n := by
        rw [integral_comp_add_right (fun x => cutoffProfile ω x ^ n)]
        congr 1 <;> ring
      _ = ∫ t in (0 : ℝ)..ω, cos (π / (2 * ω) * t) ^ n := by
        apply integral_congr
        intro t ht
        dsimp only
        rw [Set.uIcc_of_le hω0.le] at ht
        rw [cutoffProfile_right hω1 (by linarith only [ht.1])]
        simp only [add_sub_cancel_right]
  have hadd := integral_add_adjacent_intervals (f := fun x => cutoffProfile ω x ^ n)
    ((hf.pow n).intervalIntegrable (μ := volume) (a := 0) (b := 1 / 2 - ω))
    ((hf.pow n).intervalIntegrable (μ := volume) (a := 1 / 2 - ω) (b := 1 / 2))
  rw [hp, hl] at hadd
  linarith only [hadd]

theorem integral_cutoffProfile {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1 / 2) :
    (∫ x in -(1 / 2 : ℝ)..1 / 2, cutoffProfile ω x) = 1 - 2 * ω + 4 * ω / π := by
  have hk : π / (2 * ω) ≠ 0 := div_ne_zero pi_ne_zero (by positivity)
  have hκω : π / (2 * ω) * ω = π / 2 := by field_simp [hω0.ne']
  have h := integral_cutoffProfile_pow hω0 hω1 1
  simp only [pow_one] at h
  rw [h, integral_comp_mul_left _ hk, mul_zero, hκω, integral_cos,
    sin_pi_div_two, sin_zero, sub_zero, smul_eq_mul]
  field_simp
  ring

theorem integral_cutoffProfile_sq {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1 / 2) :
    (∫ x in -(1 / 2 : ℝ)..1 / 2, cutoffProfile ω x ^ 2) = 1 - ω := by
  have hk : π / (2 * ω) ≠ 0 := div_ne_zero pi_ne_zero (by positivity)
  have hκω : π / (2 * ω) * ω = π / 2 := by field_simp [hω0.ne']
  rw [integral_cutoffProfile_pow hω0 hω1 2,
    integral_comp_mul_left (fun t => cos t ^ 2) hk,
    mul_zero, hκω, integral_cos_sq, cos_pi_div_two, sin_zero, cos_zero,
    zero_mul, mul_zero]
  simp only [sub_zero, zero_add, smul_eq_mul]
  field_simp
  ring

/-- The single weighted trigonometric integral needed for C_* and E. -/
theorem integral_shift_sq_cos {c ω : ℝ} (hc : c ≠ 0) (hcω : c * ω = π) (a : ℝ) :
    (∫ t in (0 : ℝ)..ω, (t + a) ^ 2 * cos (c * t)) = -2 * (2 * a + ω) / c ^ 2 := by
  let F : ℝ → ℝ := fun t => (t + a) ^ 2 * sin (c * t) / c +
    2 * (t + a) * cos (c * t) / c ^ 2 - 2 * sin (c * t) / c ^ 3
  have hF (t : ℝ) : HasDerivAt F ((t + a) ^ 2 * cos (c * t)) t := by
    have hs := ((hasDerivAt_id t).const_mul c).sin
    have hcos := ((hasDerivAt_id t).const_mul c).cos
    dsimp only [F]
    convert ((((((hasDerivAt_id t).add_const a).fun_pow 2).fun_mul hs).div_const c).fun_add
      (((((hasDerivAt_id t).add_const a).const_mul 2).fun_mul hcos).div_const (c ^ 2))).fun_sub
      ((hs.const_mul 2).div_const (c ^ 3)) using 1
    · rfl
    · simp only [id_eq, mul_one, Nat.cast_ofNat, Nat.reduceSub, pow_one]
      field_simp [hc]
      ring
  have hint : IntervalIntegrable (fun t => (t + a) ^ 2 * cos (c * t)) volume 0 ω :=
    (by fun_prop : Continuous (fun t : ℝ => (t + a) ^ 2 * cos (c * t))).intervalIntegrable 0 ω
  rw [integral_eq_sub_of_hasDerivAt (fun t _ => hF t) hint]
  dsimp only [F]
  simp only [hcω, sin_pi, cos_pi, mul_zero, sin_zero, cos_zero]
  field_simp [hc]
  ring

/-- The sum of the integrals over the two boundary layers. -/
noncomputable def layerIntegral (ω : ℝ) (f : ℝ → ℝ) : ℝ :=
  (∫ x in -(1 / 2 : ℝ)..-(1 / 2 - ω), f x) +
    ∫ x in (1 / 2 - ω)..(1 / 2 : ℝ), f x

theorem layerIntegral_even (ω : ℝ) {f : ℝ → ℝ} (he : Function.Even f) :
    layerIntegral ω f = 2 * ∫ x in (1 / 2 - ω)..(1 / 2 : ℝ), f x := by
  have hneg : (∫ x in -(1 / 2 : ℝ)..-(1 / 2 - ω), f x) =
      ∫ x in (1 / 2 - ω)..(1 / 2 : ℝ), f x := by
    calc
      (∫ x in -(1 / 2 : ℝ)..-(1 / 2 - ω), f x) =
          ∫ x in (1 / 2 - ω)..(1 / 2 : ℝ), f (-x) := by rw [integral_comp_neg]
      _ = ∫ x in (1 / 2 - ω)..(1 / 2 : ℝ), f x := integral_congr (fun x _ => he x)
  unfold layerIntegral
  rw [hneg]
  ring

theorem layerIntegral_profile_pow {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1 / 2) (n : ℕ) :
    layerIntegral ω (fun x => cutoffProfile ω x ^ n) =
      2 * ∫ t in (0 : ℝ)..ω, cos (π / (2 * ω) * t) ^ n := by
  rw [layerIntegral_even ω (fun x => by rw [cutoffProfile_even hω1 x])]
  congr 1
  calc
    (∫ x in (1 / 2 - ω)..(1 / 2 : ℝ), cutoffProfile ω x ^ n) =
        ∫ t in (0 : ℝ)..ω, cutoffProfile ω (t + (1 / 2 - ω)) ^ n := by
      rw [integral_comp_add_right (fun x => cutoffProfile ω x ^ n)]
      congr 1 <;> ring
    _ = ∫ t in (0 : ℝ)..ω, cos (π / (2 * ω) * t) ^ n := by
      apply integral_congr
      intro t ht
      dsimp only
      rw [Set.uIcc_of_le hω0.le] at ht
      rw [cutoffProfile_right hω1 (by linarith only [ht.1])]
      simp only [add_sub_cancel_right]

theorem layerIntegral_profile_sq {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1 / 2) :
    layerIntegral ω (fun x => cutoffProfile ω x ^ 2) = ω := by
  have hk : π / (2 * ω) ≠ 0 := div_ne_zero pi_ne_zero (by positivity)
  have hκω : π / (2 * ω) * ω = π / 2 := by field_simp [hω0.ne']
  rw [layerIntegral_profile_pow hω0 hω1 2,
    integral_comp_mul_left (fun t => cos t ^ 2) hk,
    mul_zero, hκω, integral_cos_sq, cos_pi_div_two, sin_zero, cos_zero,
    zero_mul, mul_zero]
  simp only [sub_zero, zero_add, smul_eq_mul]
  field_simp [pi_ne_zero]

/-- Layer moment before translating back to the cube coordinates. -/
theorem integral_layer_moment_cos {ω : ℝ} (hω0 : 0 < ω) (a : ℝ) :
    2 * (∫ t in (0 : ℝ)..ω, (t + a) ^ 2 * cos (π / (2 * ω) * t) ^ 2) =
      ((ω + a) ^ 3 - a ^ 3) / 3 - 2 * (2 * a + ω) * ω ^ 2 / π ^ 2 := by
  have hc : π / ω ≠ 0 := div_ne_zero pi_ne_zero hω0.ne'
  have hcω : π / ω * ω = π := div_mul_cancel₀ _ hω0.ne'
  have htrig (t : ℝ) : (t + a) ^ 2 * cos (π / (2 * ω) * t) ^ 2 =
      ((t + a) ^ 2 + (t + a) ^ 2 * cos (π / ω * t)) / 2 := by
    have heq : 2 * (π / (2 * ω) * t) = π / ω * t := by ring
    have h := cos_two_mul (π / (2 * ω) * t)
    rw [heq] at h
    have hcos : cos (π / (2 * ω) * t) ^ 2 = (1 + cos (π / ω * t)) / 2 := by
      linarith only [h]
    rw [hcos]
    ring
  have hp : (∫ t in (0 : ℝ)..ω, (t + a) ^ 2) = ((ω + a) ^ 3 - a ^ 3) / 3 := by
    rw [integral_comp_add_right (fun t : ℝ => t ^ 2), integral_pow]
    norm_num
  have hcontinuous : Continuous (fun t : ℝ => (t + a) ^ 2 * cos (π / ω * t)) := by fun_prop
  simp_rw [htrig]
  rw [integral_div, integral_add ((by fun_prop : Continuous (fun t : ℝ => (t + a) ^ 2)).intervalIntegrable _ _)
    (hcontinuous.intervalIntegrable _ _), hp, integral_shift_sq_cos hc hcω a]
  field_simp [pi_ne_zero, hω0.ne']
  ring

theorem layerIntegral_moment_profile_sq {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1 / 2) :
    layerIntegral ω (fun x => x ^ 2 * cutoffProfile ω x ^ 2) =
      (ω / 4 - ω ^ 2 / 2 + ω ^ 3 / 3) - 2 * ω ^ 2 * (1 - ω) / π ^ 2 := by
  have he : Function.Even (fun x => x ^ 2 * cutoffProfile ω x ^ 2) := by
    intro x
    dsimp only
    rw [neg_sq, cutoffProfile_even hω1 x]
  rw [layerIntegral_even ω he]
  have hl : (∫ x in (1 / 2 - ω)..(1 / 2 : ℝ), x ^ 2 * cutoffProfile ω x ^ 2) =
      ∫ t in (0 : ℝ)..ω, (t + (1 / 2 - ω)) ^ 2 * cos (π / (2 * ω) * t) ^ 2 := by
    calc
      (∫ x in (1 / 2 - ω)..(1 / 2 : ℝ), x ^ 2 * cutoffProfile ω x ^ 2) =
          ∫ t in (0 : ℝ)..ω, (t + (1 / 2 - ω)) ^ 2 * cutoffProfile ω (t + (1 / 2 - ω)) ^ 2 := by
        rw [integral_comp_add_right (fun x => x ^ 2 * cutoffProfile ω x ^ 2)]
        congr 1 <;> ring
      _ = _ := by
        apply integral_congr
        intro t ht
        dsimp only
        rw [Set.uIcc_of_le hω0.le] at ht
        rw [cutoffProfile_right hω1 (by linarith only [ht.1])]
        simp only [add_sub_cancel_right]
  rw [hl, integral_layer_moment_cos hω0 (1 / 2 - ω)]
  ring

/-- A continuous integrand splits exactly into the two layers and the plateau. -/
theorem integral_eq_layerIntegral_add_middle {ω : ℝ} {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ x in -(1 / 2 : ℝ)..1 / 2, f x) = layerIntegral ω f +
      ∫ x in -(1 / 2 - ω)..(1 / 2 - ω), f x := by
  have h1 := integral_add_adjacent_intervals
    (hf.intervalIntegrable (μ := volume) (a := -(1 / 2 : ℝ)) (b := -(1 / 2 - ω)))
    (hf.intervalIntegrable (μ := volume) (a := -(1 / 2 - ω)) (b := 1 / 2 - ω))
  have h2 := integral_add_adjacent_intervals
    (hf.intervalIntegrable (μ := volume) (a := -(1 / 2 : ℝ)) (b := 1 / 2 - ω))
    (hf.intervalIntegrable (μ := volume) (a := 1 / 2 - ω) (b := 1 / 2))
  unfold layerIntegral
  linarith only [h1, h2]

theorem integral_moment_profile_sq {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1 / 2) :
    (∫ x in -(1 / 2 : ℝ)..1 / 2, x ^ 2 * cutoffProfile ω x ^ 2) =
      (ω / 4 - ω ^ 2 / 2 + ω ^ 3 / 3) - 2 * ω ^ 2 * (1 - ω) / π ^ 2 +
      2 / 3 * (1 / 2 - ω) ^ 3 := by
  have hf : Continuous (fun x => x ^ 2 * cutoffProfile ω x ^ 2) := by
    exact (continuous_id.pow 2).mul ((cutoffProfile_contDiff hω1).continuous.pow 2)
  rw [integral_eq_layerIntegral_add_middle hf, layerIntegral_moment_profile_sq hω0 hω1]
  congr 1
  have ha : -(1 / 2 - ω) ≤ 1 / 2 - ω := by linarith
  calc
    (∫ x in -(1 / 2 - ω)..(1 / 2 - ω), x ^ 2 * cutoffProfile ω x ^ 2) =
        ∫ x in -(1 / 2 - ω)..(1 / 2 - ω), x ^ 2 := by
      apply integral_congr
      intro x hx
      dsimp only
      rw [Set.uIcc_of_le ha] at hx
      rw [cutoffProfile_plateau hω1 (abs_le.mpr hx), one_pow, mul_one]
    _ = 2 / 3 * (1 / 2 - ω) ^ 3 := by rw [integral_pow]; norm_num; ring

theorem integral_cutoffSlope_sq {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1 / 2) :
    (∫ x in -(1 / 2 : ℝ)..1 / 2, cutoffSlope ω x ^ 2) = π ^ 2 / (4 * ω) := by
  simp_rw [cutoffSlope_sq]
  rw [integral_const_mul, integral_sub (f := fun _ : ℝ => (1 : ℝ)) (g := fun x => cutoffProfile ω x ^ 2) (continuous_const.intervalIntegrable _ _)
    (((cutoffProfile_contDiff hω1).continuous.pow 2).intervalIntegrable _ _),
    integral_const, integral_cutoffProfile_sq hω0 hω1]
  simp only [smul_eq_mul, mul_one]
  field_simp [hω0.ne']
  ring

theorem integral_moment_cutoffSlope_sq {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1 / 2) :
    (∫ x in -(1 / 2 : ℝ)..1 / 2, x ^ 2 * cutoffSlope ω x ^ 2) =
      (π / (2 * ω)) ^ 2 * (ω / 4 - ω ^ 2 / 2 + ω ^ 3 / 3) + (1 - ω) / 2 := by
  have heq : (fun x => x ^ 2 * cutoffSlope ω x ^ 2) =
      (fun x => (π / (2 * ω)) ^ 2 * (x ^ 2 - x ^ 2 * cutoffProfile ω x ^ 2)) := by
    funext x
    rw [cutoffSlope_sq]
    ring
  rw [heq, integral_const_mul, integral_sub (f := fun x : ℝ => x ^ 2) (g := fun x => x ^ 2 * cutoffProfile ω x ^ 2) ((continuous_id.pow 2).intervalIntegrable _ _)
    (((continuous_id.pow 2).mul ((cutoffProfile_contDiff hω1).continuous.pow 2)).intervalIntegrable _ _),
    integral_moment_profile_sq hω0 hω1, integral_pow]
  norm_num
  field_simp [hω0.ne', pi_ne_zero]
  ring

/-- All seven one-dimensional H10 identities, using the exact row constants. -/
theorem cutoff_integrals_row {d : ℕ} (row : Contract.Row d)
    (hω0 : 0 < row.omegaEff) (hω1 : row.omegaEff ≤ 1 / 2) :
    (∫ x in -(1 / 2 : ℝ)..1 / 2, cutoffProfile row.omegaEff x ^ 2) = row.cosA ∧
    (∫ x in -(1 / 2 : ℝ)..1 / 2, cutoffSlope row.omegaEff x ^ 2) = row.cosB ∧
    (∫ x in -(1 / 2 : ℝ)..1 / 2, cutoffProfile row.omegaEff x) = row.cosMean ∧
    layerIntegral row.omegaEff (fun x => x ^ 2 * cutoffProfile row.omegaEff x ^ 2) = row.cosCstar ∧
    (∫ x in -(1 / 2 : ℝ)..1 / 2, x ^ 2 * cutoffProfile row.omegaEff x ^ 2) = row.cosC ∧
    (∫ x in -(1 / 2 : ℝ)..1 / 2, x ^ 2 * cutoffSlope row.omegaEff x ^ 2) = row.cosE ∧
    layerIntegral row.omegaEff (fun x => cutoffProfile row.omegaEff x ^ 2) = row.omegaEff := by
  refine ⟨integral_cutoffProfile_sq hω0 hω1, integral_cutoffSlope_sq hω0 hω1,
    integral_cutoffProfile hω0 hω1, ?_, ?_, ?_, layerIntegral_profile_sq hω0 hω1⟩
  · exact layerIntegral_moment_profile_sq hω0 hω1
  · exact integral_moment_profile_sq hω0 hω1
  · exact integral_moment_cutoffSlope_sq hω0 hω1

end GMCExplicitDelta.Haar
