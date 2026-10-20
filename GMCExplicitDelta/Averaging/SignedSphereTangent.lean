module

public import GMCExplicitDelta.Averaging.SignedSpherePoly
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.Convex.Deriv

/-! # Convexity and the Contract tangent lower bound for signed sphere moments -/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Set
open scoped BigOperators
open GMCExplicitDelta.Insertion

namespace GMCExplicitDelta.Averaging

theorem hasDerivAt_spherePolyReal (d : ℕ) (lam : ℝ) :
    HasDerivAt (spherePolyReal d) (spherePolyDerivReal d lam) lam := by
  have hs : HasDerivAt
      (fun x : ℝ => ∑ j ∈ range 32, (Contract.spherePolyCoeff d j : ℝ) * x ^ (32 - j))
      (spherePolyDerivReal d lam) lam := by
    unfold spherePolyDerivReal
    apply HasDerivAt.fun_sum
    intro j hj
    have he : 32 - j - 1 = 31 - j := by omega
    simpa only [id_eq, he, mul_one, mul_assoc] using
      ((hasDerivAt_id lam).fun_pow (32 - j)).const_mul (Contract.spherePolyCoeff d j : ℝ)
  have hf : spherePolyReal d = fun x : ℝ =>
      (∑ j ∈ range 32, (Contract.spherePolyCoeff d j : ℝ) * x ^ (32 - j)) +
        (Contract.spherePolyCoeff d 32 : ℝ) := by
    funext x
    simp only [spherePolyReal, show 33 = 32 + 1 from rfl, sum_range_succ,
      Nat.sub_self, pow_zero, mul_one]
  rw [hf]
  exact hs.add_const _

theorem convexOn_signedSplitMoment (n : ℕ) : ConvexOn ℝ univ (signedSplitMoment n) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  unfold signedSplitMoment
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((integrable_signedSplit n x).const_mul a) ((integrable_signedSplit n y).const_mul b)]
  apply integral_mono (integrable_signedSplit n (a * x + b * y))
    (((integrable_signedSplit n x).const_mul a).add ((integrable_signedSplit n y).const_mul b))
  intro z
  have hq : z.1 ^ 2 + (a * x + b * y) * sqSum z.2 =
      a * (z.1 ^ 2 + x * sqSum z.2) + b * (z.1 ^ 2 + y * sqSum z.2) := by
    calc
      _ = (a + b) * z.1 ^ 2 + (a * x + b * y) * sqSum z.2 := by rw [hab, one_mul]
      _ = _ := by ring
  change (z.1 ^ 2 + (a * x + b * y) * sqSum z.2) ^ 32 ≤
    a * (z.1 ^ 2 + x * sqSum z.2) ^ 32 + b * (z.1 ^ 2 + y * sqSum z.2) ^ 32
  rw [hq]
  simpa only [smul_eq_mul] using
    ((by decide : Even 32).convexOn_pow (𝕜 := ℝ)).2 (mem_univ _) (mem_univ _) ha hb hab

theorem convexOn_spherePolyReal_succ (n : ℕ) : ConvexOn ℝ univ (spherePolyReal (n + 1)) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  have hr : 0 < radialMoment ((n + 1 : ℕ) : ℝ) 32 := radialMoment_pos (by positivity) 32
  apply le_of_mul_le_mul_left (a := radialMoment ((n + 1 : ℕ) : ℝ) 32) ?_ hr
  calc
    _ = signedSplitMoment n (a * x + b * y) := (signedSplitMoment_eq_spherePoly n _).symm
    _ ≤ a * signedSplitMoment n x + b * signedSplitMoment n y :=
      (convexOn_signedSplitMoment n).2 hx hy ha hb hab
    _ = _ := by rw [signedSplitMoment_eq_spherePoly, signedSplitMoment_eq_spherePoly]; ring

/-- A supporting-line estimate on an interval of diameter two. -/
theorem convex_tangent_lower {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f)
    {a x D : ℝ} (hd : HasDerivAt f D a) (ha : a ∈ Set.Icc (-1) 1) (hx : x ∈ Set.Icc (-1) 1) :
    f a - 2 * |D| ≤ f x := by
  have ht : D * (x - a) ≤ f x - f a := by
    rcases lt_trichotomy a x with h | h | h
    · have hs := hf.le_slope_of_hasDerivAt (mem_univ _) (mem_univ _) h hd
      rw [slope_def_field] at hs
      exact (le_div_iff₀ (sub_pos.mpr h)).mp hs
    · subst x
      simp only [sub_self, mul_zero, le_refl]
    · have hs := hf.slope_le_of_hasDerivAt (mem_univ _) (mem_univ _) h hd
      have hs' := (div_le_iff₀ (sub_pos.mpr h)).mp (show (f a - f x) / (a - x) ≤ D by
        simpa only [slope_def_field] using hs)
      linarith only [hs']
  have hdist : |x - a| ≤ 2 := abs_le.mpr ⟨by linarith only [ha.2, hx.1], by linarith only [hx.2, ha.1]⟩
  have hprod : |D * (x - a)| ≤ 2 * |D| := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hdist (abs_nonneg D)).trans_eq (mul_comm _ _)
  linarith only [ht, hprod, neg_abs_le (D * (x - a))]

theorem spherePolyReal_tangent_lower (n : ℕ) {a lam : ℝ}
    (ha : a ∈ Set.Icc (-1) 1) (hlam : lam ∈ Set.Icc (-1) 1) :
    spherePolyReal (n + 1) a - 2 * |spherePolyDerivReal (n + 1) a| ≤
      spherePolyReal (n + 1) lam :=
  convex_tangent_lower (convexOn_spherePolyReal_succ n) (hasDerivAt_spherePolyReal _ a) ha hlam

theorem sphereTangent_mem (d : ℕ) : (Contract.sphereTangent d : ℝ) ∈ Set.Icc (-1) 1 := by
  unfold Contract.sphereTangent
  split_ifs <;> norm_num

/-- The Contract rational tangent certificate bounds every real parameter in [-1,1]. -/
theorem sphereLower_le_spherePolyReal (n : ℕ) {lam : ℝ} (hlam : lam ∈ Set.Icc (-1) 1) :
    (Contract.sphereLower (n + 1) : ℝ) ≤ spherePolyReal (n + 1) lam := by
  have h := spherePolyReal_tangent_lower n (a := (Contract.sphereTangent (n + 1) : ℝ))
    (sphereTangent_mem (n + 1)) hlam
  rw [spherePolyReal_rat, spherePolyDerivReal_rat] at h
  simpa only [Contract.sphereLower, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_abs] using h

end GMCExplicitDelta.Averaging
