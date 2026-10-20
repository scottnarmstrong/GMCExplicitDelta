module

public import GMCExplicitDelta.Haar.LocalizationGrid
public import GMCExplicitDelta.Haar.CutoffIntegrals

/-! H13: certified localization weights for the exact plateau-cosine profile. -/
@[expose] public section

namespace GMCExplicitDelta.Haar

open Real Set intervalIntegral
open MeasureTheory (volume)

/-- A unit-height concave profile vanishing at both endpoints has total variation two. -/
theorem integral_abs_derivative_eq_two {f f' : ℝ → ℝ}
    (hdf : ∀ x, HasDerivAt f (f' x) x) (hcont : Continuous f')
    (hanti : AntitoneOn f' (Icc (-(1 / 2)) (1 / 2)))
    (hzero : f' 0 = 0) (hfzero : f 0 = 1)
    (hfleft : f (-(1 / 2)) = 0) (hfright : f (1 / 2) = 0) :
    (∫ x in -(1 / 2 : ℝ)..1 / 2, |f' x|) = 2 := by
  have hleft : (∫ x in -(1 / 2 : ℝ)..0, |f' x|) = ∫ x in -(1 / 2 : ℝ)..0, f' x := by
    apply integral_congr
    intro x hx
    dsimp only
    rw [Set.uIcc_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 0)] at hx
    apply abs_of_nonneg
    have h := hanti ⟨hx.1, by linarith only [hx.2]⟩ ⟨by norm_num, by norm_num⟩ hx.2
    rwa [hzero] at h
  have hright : (∫ x in (0 : ℝ)..1 / 2, |f' x|) = -(∫ x in (0 : ℝ)..1 / 2, f' x) := by
    calc
      (∫ x in (0 : ℝ)..1 / 2, |f' x|) = ∫ x in (0 : ℝ)..1 / 2, -f' x := by
        apply integral_congr
        intro x hx
        dsimp only
        rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hx
        apply abs_of_nonpos
        have h := hanti ⟨by norm_num, by norm_num⟩ ⟨by linarith only [hx.1], hx.2⟩ hx.1
        rwa [hzero] at h
      _ = _ := integral_neg
  have hadd := integral_add_adjacent_intervals (f := fun x => |f' x|)
    (hcont.abs.intervalIntegrable (μ := volume) (a := -(1 / 2 : ℝ)) (b := 0))
    (hcont.abs.intervalIntegrable (μ := volume) (a := 0) (b := 1 / 2))
  rw [hleft, hright,
    integral_eq_sub_of_hasDerivAt (fun x _ => hdf x) (hcont.intervalIntegrable _ _),
    integral_eq_sub_of_hasDerivAt (fun x _ => hdf x) (hcont.intervalIntegrable _ _),
    hfzero, hfleft, hfright] at hadd
  linarith only [hadd]

theorem integral_abs_cutoffSlope {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1 / 2) :
    (∫ x in -(1 / 2 : ℝ)..1 / 2, |cutoffSlope ω x|) = 2 := by
  apply integral_abs_derivative_eq_two (cutoffProfile_hasDerivAt hω1)
    (cutoffSlope_continuous hω1) (cutoffSlope_antitoneOn hω0 hω1) (cutoffSlope_zero hω1)
  · exact cutoffProfile_plateau hω1 (by simpa only [abs_zero] using sub_nonneg.mpr hω1)
  · exact (cutoffProfile_endpoint hω0 hω1).2
  · exact (cutoffProfile_endpoint hω0 hω1).1

/-- The one-dimensional lower bound, before taking a tensor-product power. -/
theorem gridMin_cutoffProfile_ge {N : ℕ} (hN : 0 < N) {ω : ℝ}
    (hω0 : 0 < ω) (hω1 : ω ≤ 1 / 2) :
    1 - 2 * ω + 4 * ω / π - 1 / (N : ℝ) - π / (8 * ω * (N : ℝ) ^ 2) ≤
      gridMin N (cutoffProfile ω) := by
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast hN
  have hq := integral_sub_gridTrap_le hN (cutoffProfile_hasDerivAt hω1)
    (cutoffSlope_continuous hω1) (cutoffSlope_antitoneOn hω0 hω1)
  rw [integral_cutoffProfile hω0 hω1, cutoffSlope_endpoint_left hω0,
    cutoffSlope_endpoint_right hω0 hω1] at hq
  have hv := grid_variation_le hN (cutoffProfile_hasDerivAt hω1) (cutoffSlope_continuous hω1)
  rw [integral_abs_cutoffSlope hω0 hω1] at hv
  have hmin := gridMin_eq_gridTrap_sub_variation N (cutoffProfile ω)
  have hmul := mul_le_mul_of_nonneg_left hv (show 0 ≤ (N : ℝ)⁻¹ / 2 by positivity)
  have heq : (N : ℝ)⁻¹ ^ 2 / 8 * (π / (2 * ω) - -(π / (2 * ω))) =
      π / (8 * ω * (N : ℝ) ^ 2) := by ring
  rw [heq] at hq
  have hn : (N : ℝ)⁻¹ / 2 * 2 = 1 / (N : ℝ) := by ring
  rw [hn] at hmul
  linarith only [hq, hmin, hmul]

/-- The exact endpoint-minimum weight in the statement of H13. -/
noncomputable def exactLocalizationWeight {d : ℕ} (row : Contract.Row d) : ℝ :=
  gridMin (3 ^ row.nu) (cutoffProfile row.omegaEff) ^ d

/-- H13, about the exact cNu defined in the contract. -/
theorem cNu_le_exactLocalizationWeight {d : ℕ} (row : Contract.Row d)
    (hω0 : 0 < row.omegaEff) (hω1 : row.omegaEff ≤ 1 / 2) (hbr : 0 < row.locBracket) :
    row.cNu ≤ exactLocalizationWeight row := by
  have hN : 0 < (3 : ℕ) ^ row.nu := pow_pos (by norm_num) _
  have h := gridMin_cutoffProfile_ge hN hω0 hω1
  have hb : row.locBracket ≤ gridMin (3 ^ row.nu) (cutoffProfile row.omegaEff) := by
    simpa only [Contract.Row.locBracket, Contract.Row.cosMean, Nat.cast_pow, Nat.cast_ofNat] using h
  exact pow_le_pow_left₀ hbr.le hb d

end GMCExplicitDelta.Haar
