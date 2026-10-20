module

public import GMCExplicitDelta.Contract.DerivedGeometry
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Convex.Deriv

/-! H7: the one-dimensional plateau-cosine profile. -/
@[expose] public section

namespace GMCExplicitDelta.Haar

open Real Set Filter

/-- Join two formulas at a real threshold, retaining the left value there. -/
noncomputable def joinAt (c : ℝ) (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x ≤ c then f x else g x

/-- A differentiable gluing lemma with matching values and first derivatives. -/
theorem hasDerivAt_joinAt (c : ℝ) {f g f' g' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hg : ∀ x, HasDerivAt g (g' x) x)
    (hfg : f c = g c) (hfg' : f' c = g' c) (x : ℝ) :
    HasDerivAt (joinAt c f g) (joinAt c f' g' x) x := by
  rcases lt_trichotomy x c with hx | hxc | hx
  · rw [joinAt, ite_eq_left hx.le]
    apply (hf x).congr_of_eventuallyEq
    filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
    simp only [joinAt, ite_eq_left hy.le]
  · subst x
    rw [joinAt, ite_eq_left le_rfl]
    have hl : HasDerivWithinAt (joinAt c f g) (f' c) (Iic c) c := by
      apply (hf c).hasDerivWithinAt.congr
      · intro y hy
        exact ite_eq_left hy
      · exact ite_eq_left le_rfl
    have hr : HasDerivWithinAt (joinAt c f g) (f' c) (Ici c) c := by
      rw [hfg']
      apply (hg c).hasDerivWithinAt.congr
      · intro y hy
        by_cases h : y ≤ c
        · have heq : y = c := le_antisymm h hy
          subst y
          simpa only [joinAt, ite_eq_left le_rfl] using hfg
        · exact ite_eq_right h
      · simpa only [joinAt, ite_eq_left le_rfl] using hfg
    have hu := hl.union hr
    rw [Iic_union_Ici] at hu
    exact hu.hasDerivAt (by simp)
  · rw [joinAt, ite_eq_right (not_le.mpr hx)]
    apply (hg x).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    simp only [joinAt, ite_eq_right (not_le.mpr hy)]

theorem continuous_joinAt (c : ℝ) {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hfg : f c = g c) :
    Continuous (joinAt c f g) := by
  apply hf.if_le hg continuous_id continuous_const
  intro x hx
  change x = c at hx
  subst x
  exact hfg

/-- The plateau-cosine cutoff, extended by its cosine branches outside the cube. -/
noncomputable def cutoffProfile (ω x : ℝ) : ℝ :=
  joinAt (-(1 / 2 - ω)) (fun y => cos (π / (2 * ω) * (y + (1 / 2 - ω))))
    (joinAt (1 / 2 - ω) (fun _ => 1) (fun y => cos (π / (2 * ω) * (y - (1 / 2 - ω))))) x

/-- The explicit first derivative of the plateau-cosine profile. -/
noncomputable def cutoffSlope (ω x : ℝ) : ℝ :=
  joinAt (-(1 / 2 - ω)) (fun y => -(π / (2 * ω)) * sin (π / (2 * ω) * (y + (1 / 2 - ω))))
    (joinAt (1 / 2 - ω) (fun _ => 0)
      (fun y => -(π / (2 * ω)) * sin (π / (2 * ω) * (y - (1 / 2 - ω))))) x

theorem hasDerivAt_cos_affine (κ a x : ℝ) :
    HasDerivAt (fun y => cos (κ * (y - a))) (-κ * sin (κ * (x - a))) x := by
  simpa only [id_eq, mul_one, mul_neg, neg_mul, mul_comm] using
    (((hasDerivAt_id x).sub_const a).const_mul κ).cos

theorem cutoffProfile_hasDerivAt {ω : ℝ} (hω : ω ≤ 1 / 2) (x : ℝ) :
    HasDerivAt (cutoffProfile ω) (cutoffSlope ω x) x := by
  have ha : -(1 / 2 - ω) ≤ 1 / 2 - ω := by linarith
  have hin := hasDerivAt_joinAt (1 / 2 - ω)
    (fun y => hasDerivAt_const y (1 : ℝ))
    (fun y => hasDerivAt_cos_affine (π / (2 * ω)) (1 / 2 - ω) y)
    (by simp) (by simp)
  unfold cutoffProfile cutoffSlope
  apply hasDerivAt_joinAt
    (-(1 / 2 - ω))
    (fun y => by simpa only [sub_neg_eq_add] using
      hasDerivAt_cos_affine (π / (2 * ω)) (-(1 / 2 - ω)) y)
    hin
  · simp only [neg_add_cancel, mul_zero, cos_zero, joinAt, ite_eq_left ha]
  · simp only [neg_add_cancel, mul_zero, sin_zero, joinAt, ite_eq_left ha]

theorem cutoffSlope_continuous {ω : ℝ} (hω : ω ≤ 1 / 2) :
    Continuous (cutoffSlope ω) := by
  have ha : -(1 / 2 - ω) ≤ 1 / 2 - ω := by linarith
  have hleft : Continuous (fun y : ℝ => -(π / (2 * ω)) *
      sin (π / (2 * ω) * (y + (1 / 2 - ω)))) := by fun_prop
  have hright : Continuous (fun y : ℝ => -(π / (2 * ω)) *
      sin (π / (2 * ω) * (y - (1 / 2 - ω)))) := by fun_prop
  have hin : Continuous (joinAt (1 / 2 - ω) (fun _ => (0 : ℝ))
      (fun y => -(π / (2 * ω)) * sin (π / (2 * ω) * (y - (1 / 2 - ω))))) :=
    continuous_joinAt (1 / 2 - ω) continuous_const hright (by simp)
  unfold cutoffSlope
  apply continuous_joinAt (-(1 / 2 - ω)) hleft hin
  simp only [neg_add_cancel, mul_zero, sin_zero, joinAt, ite_eq_left ha]

theorem cutoffProfile_contDiff {ω : ℝ} (hω : ω ≤ 1 / 2) :
    ContDiff ℝ 1 (cutoffProfile ω) := by
  apply contDiff_one_iff_deriv.2
  constructor
  · intro x
    exact (cutoffProfile_hasDerivAt hω x).differentiableAt
  · have heq : deriv (cutoffProfile ω) = cutoffSlope ω := by
      funext x
      exact (cutoffProfile_hasDerivAt hω x).deriv
    rw [heq]
    exact cutoffSlope_continuous hω

/-- The original absolute-value formula from H7. -/
theorem cutoffProfile_eq_abs {ω : ℝ} (hω : ω ≤ 1 / 2) (x : ℝ) :
    cutoffProfile ω x = if |x| ≤ 1 / 2 - ω then 1 else
      cos (π / (2 * ω) * (|x| - (1 / 2 - ω))) := by
  have ha : 0 ≤ 1 / 2 - ω := sub_nonneg.mpr hω
  unfold cutoffProfile joinAt
  by_cases hl : x ≤ -(1 / 2 - ω)
  · rw [ite_eq_left hl, abs_of_nonpos (le_trans hl (neg_nonpos.mpr ha))]
    by_cases hp : -x ≤ 1 / 2 - ω
    · have hx : x = -(1 / 2 - ω) := by linarith
      rw [ite_eq_left hp, hx]
      simp only [neg_add_cancel, mul_zero, cos_zero]
    · rw [ite_eq_right hp]
      dsimp only
      rw [show π / (2 * ω) * (x + (1 / 2 - ω)) =
        -(π / (2 * ω) * (-x - (1 / 2 - ω))) by ring, cos_neg]
  · rw [ite_eq_right hl]
    by_cases hr : x ≤ 1 / 2 - ω
    · rw [ite_eq_left hr, ite_eq_left (abs_le.mpr ⟨(not_le.mp hl).le, hr⟩)]
    · have hx0 : 0 ≤ x := le_trans ha (not_le.mp hr).le
      rw [ite_eq_right hr, abs_of_nonneg hx0, ite_eq_right hr]

/-- Nonnegativity and the upper bound on the closed unit interval. -/
theorem cutoffProfile_bounds {ω x : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1 / 2)
    (hx : |x| ≤ 1 / 2) : 0 ≤ cutoffProfile ω x ∧ cutoffProfile ω x ≤ 1 := by
  rw [cutoffProfile_eq_abs hω1]
  split
  · exact ⟨zero_le_one, le_rfl⟩
  · rename_i hl
    have hκ : 0 < π / (2 * ω) := div_pos pi_pos (by positivity)
    have harg0 : 0 ≤ π / (2 * ω) * (|x| - (1 / 2 - ω)) :=
      mul_nonneg hκ.le (sub_nonneg.mpr (not_le.mp hl).le)
    have harg1 : π / (2 * ω) * (|x| - (1 / 2 - ω)) ≤ π / 2 := by
      calc
        π / (2 * ω) * (|x| - (1 / 2 - ω)) ≤ π / (2 * ω) * ω := by
          apply mul_le_mul_of_nonneg_left _ hκ.le
          linarith only [hx]
        _ = π / 2 := by field_simp [hω0.ne']
    exact ⟨cos_nonneg_of_neg_pi_div_two_le_of_le
      (le_trans (by linarith only [pi_pos] : -(π / 2) ≤ 0) harg0) harg1, cos_le_one _⟩

theorem cutoffProfile_endpoint {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1 / 2) :
    cutoffProfile ω (1 / 2) = 0 ∧ cutoffProfile ω (-(1 / 2)) = 0 := by
  have h : (1 / 2 : ℝ) > 1 / 2 - ω := by linarith
  have hk : π / (2 * ω) * ((1 / 2 : ℝ) - (1 / 2 - ω)) = π / 2 := by
    field_simp [hω0.ne']
    ring
  rw [cutoffProfile_eq_abs hω1, cutoffProfile_eq_abs hω1]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_neg]
  rw [ite_eq_right (not_le.mpr h), hk, cos_pi_div_two]
  exact ⟨rfl, rfl⟩

/-- The derivative vanishes at both plateau interfaces. -/
theorem cutoffSlope_interface {ω : ℝ} (hω : ω ≤ 1 / 2) :
    cutoffSlope ω (1 / 2 - ω) = 0 ∧ cutoffSlope ω (-(1 / 2 - ω)) = 0 := by
  have ha : -(1 / 2 - ω) ≤ 1 / 2 - ω := by linarith
  constructor
  · by_cases hz : 1 / 2 - ω ≤ -(1 / 2 - ω)
    · have heq : 1 / 2 - ω = 0 := by linarith
      simp only [cutoffSlope, joinAt, heq, neg_zero, le_refl, ite_eq_left, zero_add, mul_zero, sin_zero]
    · simp only [cutoffSlope, joinAt, ite_eq_right hz, le_refl, ite_eq_left]
  · simp only [cutoffSlope, joinAt, le_refl, ite_eq_left, neg_add_cancel, mul_zero, sin_zero]

/-- The oscillator identity holds on the layers; it also holds on the plateau,
where both sides are zero. -/
theorem cutoffSlope_sq (ω x : ℝ) :
    cutoffSlope ω x ^ 2 = (π / (2 * ω)) ^ 2 * (1 - cutoffProfile ω x ^ 2) := by
  unfold cutoffSlope cutoffProfile joinAt
  have htrig (t κ : ℝ) : (-κ * sin t) ^ 2 = κ ^ 2 * (1 - cos t ^ 2) := by
    have h : sin t ^ 2 = 1 - cos t ^ 2 := by linarith only [sin_sq_add_cos_sq t]
    rw [mul_pow, neg_sq, h]
  split_ifs <;> first | exact htrig _ _ | norm_num

/-- An antitone gluing lemma on a closed interval. -/
theorem antitoneOn_joinAt {a c b : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    {f g : ℝ → ℝ} (hf : AntitoneOn f (Icc a c)) (hg : AntitoneOn g (Icc c b))
    (hfg : f c = g c) : AntitoneOn (joinAt c f g) (Icc a b) := by
  intro x hx y hy hxy
  simp only [joinAt]
  by_cases hxc : x ≤ c
  · rw [ite_eq_left hxc]
    by_cases hyc : y ≤ c
    · rw [ite_eq_left hyc]
      exact hf ⟨hx.1, hxc⟩ ⟨hy.1, hyc⟩ hxy
    · rw [ite_eq_right hyc]
      exact le_trans (hg ⟨le_rfl, hcb⟩ ⟨(not_le.mp hyc).le, hy.2⟩ (not_le.mp hyc).le)
        (hfg ▸ hf ⟨hx.1, hxc⟩ ⟨hac, le_rfl⟩ hxc)
  · have hyc : ¬y ≤ c := not_le.mpr (lt_of_lt_of_le (not_le.mp hxc) hxy)
    rw [ite_eq_right hxc, ite_eq_right hyc]
    exact hg ⟨(not_le.mp hxc).le, hx.2⟩ ⟨(not_le.mp hyc).le, hy.2⟩ hxy

/-- The explicit slope is decreasing throughout the unit interval. -/
theorem cutoffSlope_antitoneOn {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1 / 2) :
    AntitoneOn (cutoffSlope ω) (Icc (-(1 / 2)) (1 / 2)) := by
  have hκ : 0 ≤ π / (2 * ω) := (div_pos pi_pos (by positivity : 0 < 2 * ω)).le
  have hk : π / (2 * ω) * ω = π / 2 := by field_simp [hω0.ne']
  have ha : -(1 / 2 - ω) ≤ 1 / 2 - ω := by linarith
  have hleft : AntitoneOn
      (fun y => -(π / (2 * ω)) * sin (π / (2 * ω) * (y + (1 / 2 - ω))))
      (Icc (-(1 / 2)) (-(1 / 2 - ω))) := by
    intro x hx y hy hxy
    apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr hκ)
    apply sin_le_sin_of_le_of_le_pi_div_two
    · have h := mul_le_mul_of_nonneg_left hx.1 hκ
      nlinarith only [h, hk]
    · have h := mul_le_mul_of_nonneg_left hy.2 hκ
      nlinarith only [h, pi_pos]
    · exact mul_le_mul_of_nonneg_left (by linarith only [hxy]) hκ
  have hright : AntitoneOn
      (fun y => -(π / (2 * ω)) * sin (π / (2 * ω) * (y - (1 / 2 - ω))))
      (Icc (1 / 2 - ω) (1 / 2)) := by
    intro x hx y hy hxy
    apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr hκ)
    apply sin_le_sin_of_le_of_le_pi_div_two
    · have h := mul_le_mul_of_nonneg_left hx.1 hκ
      nlinarith only [h, pi_pos]
    · have h := mul_le_mul_of_nonneg_left hy.2 hκ
      nlinarith only [h, hk]
    · exact mul_le_mul_of_nonneg_left (sub_le_sub_right hxy _) hκ
  have hin := antitoneOn_joinAt ha (by linarith : 1 / 2 - ω ≤ 1 / 2)
    (f := fun _ => (0 : ℝ)) (g := fun y => -(π / (2 * ω)) * sin (π / (2 * ω) * (y - (1 / 2 - ω))))
    (fun _ _ _ _ _ => le_rfl) hright (by simp)
  apply antitoneOn_joinAt (by linarith : -(1 / 2 : ℝ) ≤ -(1 / 2 - ω))
    (by linarith : -(1 / 2 - ω) ≤ 1 / 2) hleft hin
  simp only [neg_add_cancel, mul_zero, sin_zero, joinAt, ite_eq_left ha]

theorem cutoffProfile_concaveOn {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1 / 2) :
    ConcaveOn ℝ (Icc (-(1 / 2)) (1 / 2)) (cutoffProfile ω) := by
  apply AntitoneOn.concaveOn_of_deriv (convex_Icc _ _)
    (cutoffProfile_contDiff hω1).continuous.continuousOn
    (cutoffProfile_contDiff hω1).differentiable_one.differentiableOn
  have heq : deriv (cutoffProfile ω) = cutoffSlope ω := by
    funext x
    exact (cutoffProfile_hasDerivAt hω1 x).deriv
  rw [heq]
  exact (cutoffSlope_antitoneOn hω0 hω1).mono interior_subset

theorem cutoffProfile_even {ω : ℝ} (hω : ω ≤ 1 / 2) :
    Function.Even (cutoffProfile ω) := by
  intro x
  rw [cutoffProfile_eq_abs hω, cutoffProfile_eq_abs hω, abs_neg]

theorem cutoffProfile_plateau {ω x : ℝ} (hω : ω ≤ 1 / 2) (hx : |x| ≤ 1 / 2 - ω) :
    cutoffProfile ω x = 1 := by
  rw [cutoffProfile_eq_abs hω, ite_eq_left hx]

theorem cutoffProfile_right {ω x : ℝ} (hω : ω ≤ 1 / 2) (hx : 1 / 2 - ω ≤ x) :
    cutoffProfile ω x = cos (π / (2 * ω) * (x - (1 / 2 - ω))) := by
  have hx0 : 0 ≤ x := le_trans (sub_nonneg.mpr hω) hx
  rw [cutoffProfile_eq_abs hω, abs_of_nonneg hx0]
  by_cases h : x ≤ 1 / 2 - ω
  · have heq := le_antisymm h hx
    rw [ite_eq_left h, heq, sub_self, mul_zero, cos_zero]
  · rw [ite_eq_right h]

theorem cutoffSlope_endpoint_right {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1 / 2) :
    cutoffSlope ω (1 / 2) = -(π / (2 * ω)) := by
  have hl : ¬(1 / 2 : ℝ) ≤ -(1 / 2 - ω) := by linarith
  have hr : ¬(1 / 2 : ℝ) ≤ 1 / 2 - ω := by linarith
  have hk : π / (2 * ω) * ((1 / 2 : ℝ) - (1 / 2 - ω)) = π / 2 := by
    field_simp [hω0.ne']
    ring
  simp only [cutoffSlope, joinAt, ite_eq_right hl, ite_eq_right hr]
  rw [hk, sin_pi_div_two, mul_one]

theorem cutoffSlope_endpoint_left {ω : ℝ} (hω0 : 0 < ω) :
    cutoffSlope ω (-(1 / 2)) = π / (2 * ω) := by
  have hl : -(1 / 2 : ℝ) ≤ -(1 / 2 - ω) := by linarith
  have hk : π / (2 * ω) * (-(1 / 2 : ℝ) + (1 / 2 - ω)) = -(π / 2) := by
    field_simp [hω0.ne']
    ring
  simp only [cutoffSlope, joinAt, ite_eq_left hl]
  rw [hk, sin_neg, sin_pi_div_two]
  ring

theorem cutoffSlope_zero {ω : ℝ} (hω : ω ≤ 1 / 2) : cutoffSlope ω 0 = 0 := by
  have ha : 0 ≤ 1 / 2 - ω := sub_nonneg.mpr hω
  unfold cutoffSlope joinAt
  by_cases hz : (0 : ℝ) ≤ -(1 / 2 - ω)
  · have heq : 1 / 2 - ω = 0 := by linarith
    rw [ite_eq_left hz]
    rw [heq]
    norm_num
  · simp only [ite_eq_right hz, ite_eq_left ha]

end GMCExplicitDelta.Haar
