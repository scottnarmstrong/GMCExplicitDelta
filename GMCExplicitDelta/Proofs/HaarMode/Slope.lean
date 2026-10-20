module

public import GMCExplicitDelta.Proofs.HaarMode.Sobolev

/-! # Weak derivatives of the plateau-cosine slope -/

@[expose] public section

open MeasureTheory Homogenization Set Filter Real
open scoped ENNReal

namespace GMCExplicitDelta.Localization

variable {d : ℕ} {U : Set (Homogenization.Vec d)}

/-- Signed distance from the plateau, before the cosine is applied. -/
noncomputable def haarMode_soft (ω t : ℝ) : ℝ :=
  max (t - (1 / 2 - ω)) 0 - max (-t - (1 / 2 - ω)) 0

/-- The cutoff and slope are trigonometric functions of the signed plateau distance. -/
theorem haarMode_soft_trig {ω : ℝ} (hω : ω ≤ 1 / 2) (t : ℝ) :
    Haar.cutoffProfile ω t = cos (π / (2 * ω) * haarMode_soft ω t) ∧
      Haar.cutoffSlope ω t = -(π / (2 * ω)) * sin (π / (2 * ω) * haarMode_soft ω t) := by
  have ha : 0 ≤ 1 / 2 - ω := sub_nonneg.2 hω
  unfold Haar.cutoffProfile Haar.cutoffSlope Haar.joinAt haarMode_soft
  by_cases hl : t ≤ -(1 / 2 - ω)
  · have h1 : t - (1 / 2 - ω) ≤ 0 := by linarith
    have h2 : 0 ≤ -t - (1 / 2 - ω) := by linarith
    simp only [ite_eq_left hl, max_eq_right h1, max_eq_left h2]
    have heq : 0 - (-t - (1 / 2 - ω)) = t + (1 / 2 - ω) := by ring
    rw [heq]
    exact ⟨rfl, rfl⟩
  · rw [ite_eq_right hl, ite_eq_right hl]
    by_cases hr : t ≤ 1 / 2 - ω
    · have h1 : t - (1 / 2 - ω) ≤ 0 := sub_nonpos.2 hr
      have h2 : -t - (1 / 2 - ω) ≤ 0 := by linarith
      simp only [ite_eq_left hr, max_eq_right h1, max_eq_right h2, sub_self,
        mul_zero, cos_zero, sin_zero, and_true]
    · have h1 : 0 ≤ t - (1 / 2 - ω) := by linarith
      have h2 : -t - (1 / 2 - ω) ≤ 0 := by linarith
      simp only [ite_eq_right hr, max_eq_left h1, max_eq_right h2, sub_zero, and_true]

/-- The profile is bounded in absolute value on the whole real line. -/
theorem haarMode_profile_abs_le_one (ω t : ℝ) : |Haar.cutoffProfile ω t| ≤ 1 := by
  unfold Haar.cutoffProfile Haar.joinAt
  split_ifs <;> first | exact abs_cos_le_one _ | norm_num

/-- The slope is bounded by its frequency on the whole real line. -/
theorem haarMode_slope_abs_le (ω t : ℝ) : |Haar.cutoffSlope ω t| ≤ |π / (2 * ω)| := by
  unfold Haar.cutoffSlope Haar.joinAt
  split_ifs <;> first
  | simpa only [abs_mul, abs_neg, mul_one] using
      mul_le_mul_of_nonneg_left (abs_sin_le_one _) (abs_nonneg (π / (2 * ω)))
  | simpa only [abs_zero] using abs_nonneg (π / (2 * ω))

/-- Positive-part truncation gives the weak gradient of the signed plateau distance. -/
theorem haarMode_h1_soft (hU : IsOpenBoundedConvexDomain U) (u : H1Function U)
    {ω : ℝ} (hω : ω ≤ 1 / 2) :
    ∃ v : H1Function U, v.toFun = (fun x => haarMode_soft ω (u x)) ∧
      ∀ᵐ x ∂volume.restrict U,
        v.grad x = if 1 / 2 - ω < |u x| then u.grad x else 0 := by
  have ha : 0 ≤ 1 / 2 - ω := sub_nonneg.2 hω
  obtain ⟨vp, hpf, hpg⟩ := exists_h1_max_sub_const hU u (1 / 2 - ω)
  obtain ⟨vm, hmf, hmg⟩ := exists_h1_max_sub_const hU (-u) (1 / 2 - ω)
  refine ⟨vp - vm, ?_, ?_⟩
  · funext x
    simp only [H1Function.sub_toFun, hpf, hmf, H1Function.neg_toFun, haarMode_soft]
  · filter_upwards [hpg, hmg] with x hpx hmx
    simp only [H1Function.sub_grad, hpx, hmx, Set.indicator_apply,
      H1Function.neg_toFun, H1Function.neg_grad, Set.mem_ofPred_eq]
    by_cases hp : 1 / 2 - ω < u x
    · have hm : ¬1 / 2 - ω < -u x := by linarith
      have hab : 1 / 2 - ω < |u x| := hp.trans_le (le_abs_self _)
      simp only [hp, hm, hab, ite_true, ite_false, sub_zero]
    · by_cases hm : 1 / 2 - ω < -u x
      · have hab : 1 / 2 - ω < |u x| := hm.trans_le (neg_le_abs _)
        simp only [hp, hm, hab, ite_true, ite_false, zero_sub, neg_neg]
      · have hab : ¬1 / 2 - ω < |u x| := not_lt.2 (abs_le.2 ⟨by linarith, by linarith⟩)
        simp only [hp, hm, hab, ite_false, sub_zero]

/-- The cutoff slope composed with an H¹ function has its piecewise classical weak gradient. -/
theorem haarMode_h1_slope (hU : IsOpenBoundedConvexDomain U) (u : H1Function U)
    {ω : ℝ} (hω : ω ≤ 1 / 2) :
    ∃ w : H1Function U, w.toFun = (fun x => Haar.cutoffSlope ω (u x)) ∧
      ∀ᵐ x ∂volume.restrict U,
        w.grad x = fun i => -(π / (2 * ω)) ^ 2 *
          (if 1 / 2 - ω < |u x| then Haar.cutoffProfile ω (u x) else 0) * u.grad x i := by
  obtain ⟨v, hvf, hvg⟩ := haarMode_h1_soft hU u hω
  obtain ⟨z, hzf, hzg⟩ := haarMode_h1_sin hU ((π / (2 * ω)) • v)
  refine ⟨(-(π / (2 * ω))) • z, ?_, ?_⟩
  · funext x
    simp only [H1Function.smul_toFun, hzf, hvf]
    exact (haarMode_soft_trig hω (u x)).2.symm
  · filter_upwards [hvg] with x hx
    simp only [H1Function.smul_grad, hzg, H1Function.smul_toFun, hvf, hx,
      Pi.smul_apply, smul_eq_mul]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← (haarMode_soft_trig hω (u x)).1]
    split_ifs
    · ring
    · simp only [Pi.zero_apply, mul_zero, zero_mul]

/-- The profile composed with an H¹ function has its classical weak gradient. -/
theorem haarMode_h1_profile (hU : IsOpenBoundedConvexDomain U) (u : H1Function U)
    {ω : ℝ} (hω : ω ≤ 1 / 2) :
    ∃ w : H1Function U, w.toFun = (fun x => Haar.cutoffProfile ω (u x)) ∧
      w.grad = (fun x i => Haar.cutoffSlope ω (u x) * u.grad x i) := by
  have hd : deriv (Haar.cutoffProfile ω) = Haar.cutoffSlope ω :=
    funext fun t => (Haar.cutoffProfile_hasDerivAt hω t).deriv
  simpa only [hd] using haarMode_h1_comp hU u (Haar.cutoffProfile_contDiff hω)
    (abs_nonneg (π / (2 * ω))) (haarMode_profile_abs_le_one ω)
    (fun t => by rw [hd]; exact haarMode_slope_abs_le ω t)

end GMCExplicitDelta.Localization
