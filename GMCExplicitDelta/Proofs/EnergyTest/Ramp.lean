module

public import GMCExplicitDelta.Haar.CutoffProfile

/-! A C¹ boundary truncation with uniformly bounded derivative. -/

@[expose] public section

open Filter
open scoped Topology

namespace GMCExplicitDelta.Localization.EnergyTest

noncomputable def boundaryRamp (τ z : ℝ) : ℝ :=
  Haar.joinAt τ (fun _ => 0)
    (Haar.joinAt (2 * τ) (fun y => (y - τ) ^ 2 / (2 * τ)) (fun y => y - 3 * τ / 2)) z

noncomputable def boundaryRampDeriv (τ z : ℝ) : ℝ :=
  Haar.joinAt τ (fun _ => 0)
    (Haar.joinAt (2 * τ) (fun y => (y - τ) / τ) (fun _ => 1)) z

theorem boundaryRamp_hasDerivAt {τ : ℝ} (hτ : 0 < τ) (z : ℝ) :
    HasDerivAt (boundaryRamp τ) (boundaryRampDeriv τ z) z := by
  have hquad (y : ℝ) : HasDerivAt (fun t => (t - τ) ^ 2 / (2 * τ)) ((y - τ) / τ) y := by
    have hh := (((hasDerivAt_id y).sub_const τ).pow 2).div_const (2 * τ)
    change HasDerivAt (fun t : ℝ => (t - τ) ^ 2 / (2 * τ)) _ y at hh
    convert hh using 1
    dsimp only [id_eq]
    field_simp [hτ.ne']
    ring
  have hinner (y : ℝ) : HasDerivAt
      (Haar.joinAt (2 * τ) (fun t => (t - τ) ^ 2 / (2 * τ)) (fun t => t - 3 * τ / 2))
      (Haar.joinAt (2 * τ) (fun t => (t - τ) / τ) (fun _ => 1) y) y :=
    Haar.hasDerivAt_joinAt _ hquad (fun y => (hasDerivAt_id y).sub_const _)
      (by change (2 * τ - τ) ^ 2 / (2 * τ) = 2 * τ - 3 * τ / 2; field_simp [hτ.ne']; ring)
      (by change (2 * τ - τ) / τ = 1; field_simp [hτ.ne']; ring) y
  apply Haar.hasDerivAt_joinAt _ (fun y => hasDerivAt_const y (0 : ℝ)) hinner
  · simp only [Haar.joinAt, ite_eq_left (show τ ≤ 2 * τ by linarith), sub_self, zero_pow (by decide : 2 ≠ 0), zero_div]
  · simp only [Haar.joinAt, ite_eq_left (show τ ≤ 2 * τ by linarith), sub_self, zero_div]

theorem boundaryRamp_contDiff {τ : ℝ} (hτ : 0 < τ) : ContDiff ℝ 1 (boundaryRamp τ) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun z => (boundaryRamp_hasDerivAt hτ z).differentiableAt, ?_⟩
  have he : deriv (boundaryRamp τ) = boundaryRampDeriv τ :=
    funext fun z => (boundaryRamp_hasDerivAt hτ z).deriv
  rw [he]
  apply Haar.continuous_joinAt _ continuous_const
    (Haar.continuous_joinAt _ (by fun_prop) continuous_const (by change (2 * τ - τ) / τ = 1; field_simp [hτ.ne']; ring))
  simp only [Haar.joinAt, ite_eq_left (show τ ≤ 2 * τ by linarith), sub_self, zero_div]

theorem boundaryRamp_eq_zero {τ z : ℝ} (hz : z ≤ τ) : boundaryRamp τ z = 0 :=
  ite_eq_left hz

theorem boundaryRampDeriv_bounds {τ : ℝ} (hτ : 0 < τ) (z : ℝ) :
    0 ≤ boundaryRampDeriv τ z ∧ boundaryRampDeriv τ z ≤ 1 := by
  unfold boundaryRampDeriv Haar.joinAt
  split
  · exact ⟨le_rfl, zero_le_one⟩
  · rename_i hz
    split
    · rename_i hz2
      exact ⟨div_nonneg (by linarith) hτ.le, (div_le_one hτ).mpr (by linarith)⟩
    · exact ⟨zero_le_one, le_rfl⟩

theorem abs_boundaryRamp_le {τ : ℝ} (hτ : 0 < τ) (z : ℝ) : |boundaryRamp τ z| ≤ |z| := by
  unfold boundaryRamp Haar.joinAt
  split
  · simp only [abs_zero, abs_nonneg]
  · rename_i hz
    have hz0 : 0 < z := hτ.trans (lt_of_not_ge hz)
    rw [abs_of_pos hz0]
    split
    · rename_i hz2
      rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (by positivity))]
      apply (div_le_iff₀ (show 0 < 2 * τ by positivity)).mpr
      have hs : (z - τ) ^ 2 ≤ τ ^ 2 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 2
      have hp := mul_nonneg hτ.le (show 0 ≤ z - τ by linarith)
      nlinarith only [hs, hp, sq_nonneg τ]
    · rename_i hz2
      rw [abs_of_nonneg (by linarith : 0 ≤ z - 3 * τ / 2)]
      linarith

theorem boundaryRamp_limits {τ : ℕ → ℝ}
    (hlim : Tendsto τ atTop (𝓝 0)) {z : ℝ} (hz : 0 < z) :
    Tendsto (fun n => boundaryRamp (τ n) z) atTop (𝓝 z) ∧
      Tendsto (fun n => boundaryRampDeriv (τ n) z) atTop (𝓝 1) := by
  have hsmall : ∀ᶠ n in atTop, 2 * τ n < z :=
    (show Tendsto (fun n => 2 * τ n) atTop (𝓝 0) by simpa using hlim.const_mul 2).eventually_lt_const hz
  constructor
  · have ht : Tendsto (fun n => z - 3 * τ n / 2) atTop (𝓝 z) := by
      simpa using ((hlim.const_mul 3).div_const 2).const_sub z
    apply ht.congr'
    filter_upwards [hsmall] with n hn
    simp only [boundaryRamp, Haar.joinAt, ite_eq_right (by linarith : ¬z ≤ τ n), ite_eq_right (not_le.mpr hn)]
  · apply tendsto_const_nhds.congr'
    filter_upwards [hsmall] with n hn
    simp only [boundaryRampDeriv, Haar.joinAt, ite_eq_right (by linarith : ¬z ≤ τ n), ite_eq_right (not_le.mpr hn)]

end GMCExplicitDelta.Localization.EnergyTest
