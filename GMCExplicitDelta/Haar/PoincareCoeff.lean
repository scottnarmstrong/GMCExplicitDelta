module

public import GMCExplicitDelta.Haar.PoincareTorus
public import Homogenization.Sobolev.WeakDerivatives
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The mixed coefficient identity for weak derivatives on a box

For `g` with weak partial derivative `gᵢ` on the open box `U = ∏ⱼ (aⱼ, aⱼ + ℓ)`,
`∫_U gᵢ · boxMode {i} n = -(π nᵢ/ℓ) ∫_U g · boxMode ∅ n` (integration by parts against the mode that
is a sine in the `i`-th coordinate, which vanishes on the two faces orthogonal to `eᵢ`). The test
mode is not compactly supported, so it is multiplied by product cutoffs
`∏ⱼ χ_ε(xⱼ)`, `χ_ε(t) = ρ((t-a)/ε - 1)ρ((a+ℓ-t)/ε - 1)` (`ρ = Real.smoothTransition`); the
boundary-layer term `sin(π nᵢ(tᵢ - aᵢ)/ℓ) χ_ε'(tᵢ)` stays bounded and tends to zero pointwise.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open Homogenization

namespace GMCExplicitDelta.Haar.Torus

/-! ### The one-dimensional cutoff -/

/-- `χ_ε(t) = ρ((t - a)/ε - 1) ρ((a + ℓ - t)/ε - 1)`. -/
def cutoff (a ℓ ε t : ℝ) : ℝ :=
  Real.smoothTransition ((t - a) / ε - 1) * Real.smoothTransition ((a + ℓ - t) / ε - 1)

theorem contDiff_cutoff (a ℓ ε : ℝ) {n : ℕ∞} : ContDiff ℝ n (cutoff a ℓ ε) := by
  unfold cutoff
  refine ContDiff.mul ?_ ?_
  · exact Real.smoothTransition.contDiff.comp (by fun_prop)
  · exact Real.smoothTransition.contDiff.comp (by fun_prop)

theorem cutoff_nonneg (a ℓ ε t : ℝ) : 0 ≤ cutoff a ℓ ε t :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem cutoff_le_one (a ℓ ε t : ℝ) : cutoff a ℓ ε t ≤ 1 :=
  (mul_le_mul (Real.smoothTransition.le_one _) (Real.smoothTransition.le_one _)
    (Real.smoothTransition.nonneg _) zero_le_one).trans (by norm_num)

theorem mem_Ioo_of_cutoff_ne_zero {a ℓ ε t : ℝ} (hε : 0 < ε) (h : cutoff a ℓ ε t ≠ 0) :
    t ∈ Ioo (a + ε) (a + ℓ - ε) := by
  unfold cutoff at h
  have h1 : Real.smoothTransition ((t - a) / ε - 1) ≠ 0 := left_ne_zero_of_mul h
  have h2 : Real.smoothTransition ((a + ℓ - t) / ε - 1) ≠ 0 := right_ne_zero_of_mul h
  rw [Ne, Real.smoothTransition.zero_iff_nonpos, not_le, sub_pos, one_lt_div hε] at h1 h2
  constructor <;> linarith

/-- Deep inside the interval the cutoff is locally `1`. -/
theorem cutoff_eventuallyEq_one {a ℓ ε t : ℝ} (hε : 0 < ε) (h1 : 2 * ε < t - a)
    (h2 : 2 * ε < a + ℓ - t) : cutoff a ℓ ε =ᶠ[𝓝 t] fun _ => 1 := by
  have hopen : IsOpen ({s : ℝ | 2 * ε < s - a} ∩ {s : ℝ | 2 * ε < a + ℓ - s}) :=
    (isOpen_lt continuous_const (continuous_id.sub continuous_const)).inter
      (isOpen_lt continuous_const (continuous_const.sub continuous_id))
  filter_upwards [hopen.mem_nhds (show t ∈ {s : ℝ | 2 * ε < s - a} ∩ {s : ℝ | 2 * ε < a + ℓ - s}
    from ⟨h1, h2⟩)] with s hs
  have hs1 : 2 * ε < s - a := hs.1
  have hs2 : 2 * ε < a + ℓ - s := hs.2
  unfold cutoff
  rw [Real.smoothTransition.one_of_one_le, Real.smoothTransition.one_of_one_le, mul_one]
  · rw [le_sub_iff_add_le, le_div_iff₀ hε]; linarith
  · rw [le_sub_iff_add_le, le_div_iff₀ hε]; linarith

theorem cutoff_eq_one_of_deep {a ℓ ε t : ℝ} (hε : 0 < ε) (h1 : 2 * ε < t - a)
    (h2 : 2 * ε < a + ℓ - t) : cutoff a ℓ ε t = 1 :=
  (cutoff_eventuallyEq_one hε h1 h2).eq_of_nhds

theorem deriv_smoothTransition_of_one_lt {u : ℝ} (hu : 1 < u) :
    deriv Real.smoothTransition u = 0 := by
  have h : Real.smoothTransition =ᶠ[𝓝 u] fun _ => 1 := by
    filter_upwards [lt_mem_nhds hu] with v hv
    exact Real.smoothTransition.one_of_one_le hv.le
  rw [h.deriv_eq]
  simp

theorem deriv_smoothTransition_of_neg {u : ℝ} (hu : u < 0) :
    deriv Real.smoothTransition u = 0 := by
  have h : Real.smoothTransition =ᶠ[𝓝 u] fun _ => 0 := by
    filter_upwards [gt_mem_nhds hu] with v hv
    exact Real.smoothTransition.zero_of_nonpos hv.le
  rw [h.deriv_eq]
  simp

theorem exists_bound_deriv_smoothTransition :
    ∃ C, ∀ u, |deriv Real.smoothTransition u| ≤ C := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  have hs : HasCompactSupport (deriv Real.smoothTransition) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := 1)) fun u hu => ?_
    rcases not_and_or.mp hu with h | h
    · exact deriv_smoothTransition_of_neg (not_le.mp h)
    · exact deriv_smoothTransition_of_one_lt (not_le.mp h)
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
  exact ⟨C, fun u => by simpa [Real.norm_eq_abs] using hC u⟩

theorem hasDerivAt_cutoff (a ℓ ε t : ℝ) :
    HasDerivAt (cutoff a ℓ ε)
      (deriv Real.smoothTransition ((t - a) / ε - 1) * (1 / ε) *
          Real.smoothTransition ((a + ℓ - t) / ε - 1) +
        Real.smoothTransition ((t - a) / ε - 1) *
          (deriv Real.smoothTransition ((a + ℓ - t) / ε - 1) * (-1 / ε))) t := by
  have hd : ∀ u, HasDerivAt Real.smoothTransition (deriv Real.smoothTransition u) u :=
    fun u => (Real.smoothTransition.contDiff (n := 1)).differentiable (by simp) u |>.hasDerivAt
  have h1 : HasDerivAt (fun s : ℝ => (s - a) / ε - 1) (1 / ε) t := by
    have := ((hasDerivAt_id t).sub_const a).div_const ε |>.sub_const 1
    simpa using this
  have h2 : HasDerivAt (fun s : ℝ => (a + ℓ - s) / ε - 1) (-1 / ε) t := by
    have := ((hasDerivAt_id t).const_sub (a + ℓ)).div_const ε |>.sub_const 1
    simpa using this
  exact ((hd _).comp t h1).mul ((hd _).comp t h2)

/-- The boundary-layer term is uniformly bounded: `|sin(π m (t-a)/ℓ) χ_ε'(t)| ≤ K` on `(a, a+ℓ)`. -/
theorem exists_bound_sin_mul_deriv_cutoff {ℓ : ℝ} (hℓ : 0 < ℓ) (m : ℤ) :
    ∃ K, ∀ a ε t, 0 < ε → t ∈ Ioo a (a + ℓ) →
      |Real.sin (Real.pi * m * (t - a) / ℓ) * deriv (cutoff a ℓ ε) t| ≤ K := by
  obtain ⟨C, hC⟩ := exists_bound_deriv_smoothTransition
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
  refine ⟨2 * (2 * Real.pi * |(m : ℝ)| / ℓ * C), fun a ε t hε ht => ?_⟩
  rw [(hasDerivAt_cutoff a ℓ ε t).deriv]
  set S := Real.sin (Real.pi * m * (t - a) / ℓ)
  have hS1 : |S| ≤ Real.pi * |(m : ℝ)| * (t - a) / ℓ := by
    refine (Real.abs_sin_le_abs).trans (le_of_eq ?_)
    rw [abs_div, abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hℓ,
      abs_of_pos (sub_pos.2 ht.1)]
  have hS2 : |S| ≤ Real.pi * |(m : ℝ)| * (a + ℓ - t) / ℓ := by
    have e : Real.pi * m * (t - a) / ℓ = (m : ℝ) * Real.pi - Real.pi * m * (a + ℓ - t) / ℓ := by
      rw [eq_sub_iff_add_eq, ← add_div, div_eq_iff hℓ.ne']
      ring
    have : S = -((-1) ^ m * Real.sin (Real.pi * m * (a + ℓ - t) / ℓ)) := by
      show Real.sin (Real.pi * m * (t - a) / ℓ) = _
      rw [e, Real.sin_int_mul_pi_sub]
    rw [this, abs_neg, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
    refine (Real.abs_sin_le_abs).trans (le_of_eq ?_)
    rw [abs_div, abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hℓ,
      abs_of_pos (sub_pos.2 ht.2)]
  have hρ1 : ∀ u, |Real.smoothTransition u| ≤ 1 := fun u => by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg u)]
    exact Real.smoothTransition.le_one u
  have hmε : 0 ≤ Real.pi * |(m : ℝ)| / ℓ := by positivity
  -- first term
  have hT1 : |S * (deriv Real.smoothTransition ((t - a) / ε - 1) * (1 / ε) *
      Real.smoothTransition ((a + ℓ - t) / ε - 1))| ≤ 2 * Real.pi * |(m : ℝ)| / ℓ * C := by
    by_cases hu : 1 < (t - a) / ε - 1
    · rw [deriv_smoothTransition_of_one_lt hu]
      simp only [zero_mul, mul_zero, abs_zero]
      positivity
    · have hta : t - a ≤ 2 * ε := by
        rw [not_lt, sub_le_iff_le_add, div_le_iff₀ hε] at hu
        linarith
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (one_div_pos.2 hε)]
      calc |S| * (|deriv Real.smoothTransition ((t - a) / ε - 1)| * (1 / ε) *
            |Real.smoothTransition ((a + ℓ - t) / ε - 1)|)
          ≤ (Real.pi * |(m : ℝ)| * (2 * ε) / ℓ) * (C * (1 / ε) * 1) := by
            have hSb : |S| ≤ Real.pi * |(m : ℝ)| * (2 * ε) / ℓ :=
              hS1.trans (div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_left hta (by positivity)) hℓ.le)
            refine mul_le_mul hSb ?_ (by positivity) (by positivity)
            exact mul_le_mul (mul_le_mul_of_nonneg_right (hC _) (by positivity)) (hρ1 _)
              (abs_nonneg _) (mul_nonneg hC0 (by positivity))
        _ = 2 * Real.pi * |(m : ℝ)| / ℓ * C * (ε * (1 / ε)) := by ring
        _ = 2 * Real.pi * |(m : ℝ)| / ℓ * C := by rw [mul_one_div_cancel hε.ne', mul_one]
  have hT2 : |S * (Real.smoothTransition ((t - a) / ε - 1) *
      (deriv Real.smoothTransition ((a + ℓ - t) / ε - 1) * (-1 / ε)))| ≤
        2 * Real.pi * |(m : ℝ)| / ℓ * C := by
    by_cases hv : 1 < (a + ℓ - t) / ε - 1
    · rw [deriv_smoothTransition_of_one_lt hv]
      simp only [zero_mul, mul_zero, abs_zero]
      positivity
    · have hta : a + ℓ - t ≤ 2 * ε := by
        rw [not_lt, sub_le_iff_le_add, div_le_iff₀ hε] at hv
        linarith
      rw [abs_mul, abs_mul, abs_mul, abs_div, abs_neg, abs_one, abs_of_pos hε]
      calc |S| * (|Real.smoothTransition ((t - a) / ε - 1)| *
            (|deriv Real.smoothTransition ((a + ℓ - t) / ε - 1)| * (1 / ε)))
          ≤ (Real.pi * |(m : ℝ)| * (2 * ε) / ℓ) * (1 * (C * (1 / ε))) := by
            have hSb : |S| ≤ Real.pi * |(m : ℝ)| * (2 * ε) / ℓ :=
              hS2.trans (div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_left hta (by positivity)) hℓ.le)
            refine mul_le_mul hSb ?_ (by positivity) (by positivity)
            exact mul_le_mul (hρ1 _) (mul_le_mul_of_nonneg_right (hC _) (by positivity))
              (by positivity) zero_le_one
        _ = 2 * Real.pi * |(m : ℝ)| / ℓ * C * (ε * (1 / ε)) := by ring
        _ = 2 * Real.pi * |(m : ℝ)| / ℓ * C := by rw [mul_one_div_cancel hε.ne', mul_one]
  rw [mul_add]
  refine (abs_add_le _ _).trans ?_
  linarith

/-! ### The product test functions -/

variable {d : ℕ}

/-- The one-dimensional factors of `boxMode a ℓ O n`. -/
def modeFactor (a : Fin d → ℝ) (ℓ : ℝ) (O : Finset (Fin d)) (n : Fin d → ℤ) (j : Fin d)
    (t : ℝ) : ℝ :=
  if j ∈ O then Real.sin (Real.pi * n j * (t - a j) / ℓ)
  else Real.cos (Real.pi * n j * (t - a j) / ℓ)

theorem boxMode_eq_prod_modeFactor (a : Fin d → ℝ) (ℓ : ℝ) (O : Finset (Fin d))
    (n : Fin d → ℤ) (x : Fin d → ℝ) :
    boxMode a ℓ O n x = ∏ j, modeFactor a ℓ O n j (x j) := rfl

theorem modeFactor_of_mem (a : Fin d → ℝ) (ℓ : ℝ) {O : Finset (Fin d)} (n : Fin d → ℤ)
    {j : Fin d} (hj : j ∈ O) :
    modeFactor a ℓ O n j = fun t => Real.sin (Real.pi * n j * (t - a j) / ℓ) := by
  funext t
  simp [modeFactor, hj]

theorem modeFactor_of_notMem (a : Fin d → ℝ) (ℓ : ℝ) {O : Finset (Fin d)} (n : Fin d → ℤ)
    {j : Fin d} (hj : j ∉ O) :
    modeFactor a ℓ O n j = fun t => Real.cos (Real.pi * n j * (t - a j) / ℓ) := by
  funext t
  simp [modeFactor, hj]

theorem contDiff_modeFactor (a : Fin d → ℝ) (ℓ : ℝ) (O : Finset (Fin d)) (n : Fin d → ℤ)
    (j : Fin d) {m : ℕ∞} : ContDiff ℝ m (modeFactor a ℓ O n j) := by
  by_cases hj : j ∈ O
  · rw [modeFactor_of_mem a ℓ n hj]
    exact Real.contDiff_sin.comp (by fun_prop)
  · rw [modeFactor_of_notMem a ℓ n hj]
    exact Real.contDiff_cos.comp (by fun_prop)

theorem abs_modeFactor_le (a : Fin d → ℝ) (ℓ : ℝ) (O : Finset (Fin d)) (n : Fin d → ℤ)
    (j : Fin d) (t : ℝ) : |modeFactor a ℓ O n j t| ≤ 1 := by
  unfold modeFactor
  split_ifs
  · exact Real.abs_sin_le_one _
  · exact Real.abs_cos_le_one _

/-- Derivative of the sine factor. -/
theorem hasDerivAt_modeFactor_sin (a : Fin d → ℝ) (ℓ : ℝ) (n : Fin d → ℤ) (i : Fin d)
    (t : ℝ) :
    HasDerivAt (modeFactor a ℓ {i} n i)
      (Real.pi * n i / ℓ * modeFactor a ℓ ∅ n i t) t := by
  rw [modeFactor_of_mem a ℓ n (Finset.mem_singleton_self i),
    modeFactor_of_notMem a ℓ n (Finset.notMem_empty i)]
  beta_reduce
  have h : HasDerivAt (fun s : ℝ => Real.pi * n i * (s - a i) / ℓ) (Real.pi * n i / ℓ) t := by
    have := (((hasDerivAt_id t).sub_const (a i)).const_mul (Real.pi * n i)).div_const ℓ
    simpa using this
  have := (Real.hasDerivAt_sin _).comp t h
  rw [show Real.pi * n i / ℓ * Real.cos (Real.pi * n i * (t - a i) / ℓ) =
      Real.cos (Real.pi * n i * (t - a i) / ℓ) * (Real.pi * n i / ℓ) by ring]
  exact this

/-- One factor of the cutoff test function. -/
def testFactor (a : Fin d → ℝ) (ℓ ε : ℝ) (O : Finset (Fin d)) (n : Fin d → ℤ) (j : Fin d)
    (t : ℝ) : ℝ :=
  modeFactor a ℓ O n j t * cutoff (a j) ℓ ε t

theorem contDiff_testFactor (a : Fin d → ℝ) (ℓ ε : ℝ) (O : Finset (Fin d)) (n : Fin d → ℤ)
    (j : Fin d) {m : ℕ∞} : ContDiff ℝ m (testFactor a ℓ ε O n j) :=
  (contDiff_modeFactor a ℓ O n j).mul (contDiff_cutoff _ _ _)

theorem abs_testFactor_le (a : Fin d → ℝ) (ℓ ε : ℝ) (O : Finset (Fin d)) (n : Fin d → ℤ)
    (j : Fin d) (t : ℝ) : |testFactor a ℓ ε O n j t| ≤ 1 := by
  unfold testFactor
  rw [abs_mul, abs_of_nonneg (cutoff_nonneg _ _ _ _)]
  exact (mul_le_mul (abs_modeFactor_le a ℓ O n j t) (cutoff_le_one _ _ _ _)
    (cutoff_nonneg _ _ _ _) zero_le_one).trans (by norm_num)

/-- The cutoff test function `∏ⱼ modeFactor j (xⱼ) χ_ε(xⱼ)`. -/
def testFun (a : Fin d → ℝ) (ℓ ε : ℝ) (O : Finset (Fin d)) (n : Fin d → ℤ)
    (x : Fin d → ℝ) : ℝ :=
  ∏ j, testFactor a ℓ ε O n j (x j)

theorem contDiff_testFun (a : Fin d → ℝ) (ℓ ε : ℝ) (O : Finset (Fin d)) (n : Fin d → ℤ)
    {m : ℕ∞} : ContDiff ℝ m (testFun a ℓ ε O n) := by
  show ContDiff ℝ m (fun x : Fin d → ℝ => ∏ j ∈ Finset.univ, testFactor a ℓ ε O n j (x j))
  refine contDiff_prod (t := Finset.univ)
    (f := fun j (x : Fin d → ℝ) => testFactor a ℓ ε O n j (x j)) fun j _ => ?_
  exact (contDiff_testFactor a ℓ ε O n j).comp (contDiff_apply ℝ ℝ j)

theorem abs_testFun_le (a : Fin d → ℝ) (ℓ ε : ℝ) (O : Finset (Fin d)) (n : Fin d → ℤ)
    (x : Fin d → ℝ) : |testFun a ℓ ε O n x| ≤ 1 := by
  unfold testFun
  rw [Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun j _ => abs_nonneg _) fun j _ => abs_testFactor_le a ℓ ε O n j _

theorem testFun_eq_zero_of_not_mem (a : Fin d → ℝ) {ℓ ε : ℝ} (hε : 0 < ε) (O : Finset (Fin d))
    (n : Fin d → ℤ) {x : Fin d → ℝ}
    (hx : x ∉ Set.pi Set.univ fun j => Icc (a j + ε) (a j + ℓ - ε)) :
    testFun a ℓ ε O n x = 0 := by
  simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
  obtain ⟨j, hj⟩ := hx
  unfold testFun
  refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
  unfold testFactor
  have : cutoff (a j) ℓ ε (x j) = 0 := by
    by_contra h
    exact hj (Ioo_subset_Icc_self (mem_Ioo_of_cutoff_ne_zero hε h))
  rw [this, mul_zero]

theorem hasCompactSupport_testFun (a : Fin d → ℝ) {ℓ ε : ℝ} (hε : 0 < ε) (O : Finset (Fin d))
    (n : Fin d → ℤ) : HasCompactSupport (testFun a ℓ ε O n) :=
  HasCompactSupport.intro (isCompact_univ_pi fun _ => isCompact_Icc)
    fun _ hx => testFun_eq_zero_of_not_mem a hε O n hx

theorem tsupport_testFun_subset (a : Fin d → ℝ) {ℓ ε : ℝ} (hε : 0 < ε) (O : Finset (Fin d))
    (n : Fin d → ℤ) :
    tsupport (testFun a ℓ ε O n) ⊆ Set.pi Set.univ fun j => Ioo (a j) (a j + ℓ) := by
  have hK : tsupport (testFun a ℓ ε O n) ⊆
      Set.pi Set.univ fun j => Icc (a j + ε) (a j + ℓ - ε) := by
    refine closure_minimal (fun x hx => ?_) (isClosed_set_pi fun _ _ => isClosed_Icc)
    by_contra h
    exact hx (testFun_eq_zero_of_not_mem a hε O n h)
  refine hK.trans fun x hx j _ => ?_
  have := hx j (Set.mem_univ j)
  exact ⟨by linarith [this.1], by linarith [this.2]⟩

/-- Directional derivative of a coordinate product. -/
theorem fderiv_prod_apply_basisVec (h : Fin d → ℝ → ℝ) (hd : ∀ j, Differentiable ℝ (h j))
    (x : Fin d → ℝ) (i : Fin d) :
    fderiv ℝ (fun y : Fin d → ℝ => ∏ j, h j (y j)) x (basisVec i) =
      deriv (h i) (x i) * ∏ j ∈ Finset.univ.erase i, h j (x j) := by
  classical
  have hj : ∀ j ∈ (Finset.univ : Finset (Fin d)),
      HasFDerivAt (fun y : Fin d → ℝ => h j (y j))
        (deriv (h j) (x j) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j)
        x := fun j _ =>
    ((hd j (x j)).hasDerivAt).comp_hasFDerivAt x (hasFDerivAt_apply j x)
  rw [(HasFDerivAt.finsetProd hj).fderiv]
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, basisVec_apply]
  rw [Finset.sum_eq_single i]
  · rw [ite_eq_left rfl, mul_one]
    ring
  · intro j _ hji
    simp [hji]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-! ### The coefficient identity -/

/-- For `x` in the open box, eventually (as `ε → 0`) every coordinate is `2ε`-deep. -/
theorem eventually_deep {a : Fin d → ℝ} {ℓ : ℝ} {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) {x : Fin d → ℝ}
    (hx : x ∈ Set.pi Set.univ fun j => Ioo (a j) (a j + ℓ)) :
    ∀ᶠ k in atTop, ∀ j, 2 * ε k < x j - a j ∧ 2 * ε k < a j + ℓ - x j := by
  refine Filter.eventually_all.2 fun j => ?_
  have hj := hx j (Set.mem_univ j)
  have h1 : 0 < min (x j - a j) (a j + ℓ - x j) / 2 :=
    half_pos (lt_min (sub_pos.2 hj.1) (sub_pos.2 hj.2))
  filter_upwards [(tendsto_order.1 hε).2 _ h1] with k hk
  constructor
  · linarith [min_le_left (x j - a j) (a j + ℓ - x j)]
  · linarith [min_le_right (x j - a j) (a j + ℓ - x j)]

/-- **Mixed coefficient identity.** For `g` with weak `i`-th partial derivative `gᵢ` on the open
box, `∫_U gᵢ · boxMode {i} n = -(π nᵢ/ℓ) ∫_U g · boxMode ∅ n`. -/
theorem integral_weakDeriv_mul_boxMode (a : Fin d → ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin d)
    (n : Fin d → ℤ) {g gi : (Fin d → ℝ) → ℝ}
    (hw : HasWeakPartialDerivOn (Set.pi Set.univ fun j => Ioo (a j) (a j + ℓ)) i g gi)
    (hg : IntegrableOn g (Set.pi Set.univ fun j => Ioo (a j) (a j + ℓ)))
    (hgi : IntegrableOn gi (Set.pi Set.univ fun j => Ioo (a j) (a j + ℓ))) :
    ∫ x in Set.pi Set.univ (fun j => Ioo (a j) (a j + ℓ)), gi x * boxMode a ℓ {i} n x =
      -(Real.pi * n i / ℓ) *
        ∫ x in Set.pi Set.univ (fun j => Ioo (a j) (a j + ℓ)), g x * boxMode a ℓ ∅ n x := by
  classical
  set U : Set (Fin d → ℝ) := Set.pi Set.univ fun j => Ioo (a j) (a j + ℓ) with hU
  set ε : ℕ → ℝ := fun k => ℓ / ((k : ℝ) + 3) with hεdef
  have hεpos : ∀ k, 0 < ε k := fun k => div_pos hℓ (by positivity)
  have hεlim : Tendsto ε atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ 3 tendsto_natCast_atTop_atTop)
  have hUmeas : MeasurableSet U := MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  -- the weak identity for every cutoff level
  set ψ : ℕ → (Fin d → ℝ) → ℝ := fun k => testFun a ℓ (ε k) {i} n
  have hdiff : ∀ k j, Differentiable ℝ (testFactor a ℓ (ε k) {i} n j) := fun k j =>
    (contDiff_testFactor a ℓ (ε k) {i} n j (m := 1)).differentiable (by simp)
  have hweak : ∀ k, ∫ x in U, g x * (deriv (testFactor a ℓ (ε k) {i} n i) (x i) *
      ∏ j ∈ Finset.univ.erase i, testFactor a ℓ (ε k) {i} n j (x j)) =
      -∫ x in U, gi x * ψ k x := by
    intro k
    have h := hw (ψ k) (contDiff_testFun a ℓ (ε k) {i} n)
      (hasCompactSupport_testFun a (hεpos k) {i} n) (tsupport_testFun_subset a (hεpos k) {i} n)
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show _ = g x * (fderiv ℝ (fun y : Fin d → ℝ => ∏ j, testFactor a ℓ (ε k) {i} n j (y j)) x)
      (basisVec i)
    rw [fderiv_prod_apply_basisVec _ (hdiff k) x i]
  -- bounds
  obtain ⟨K, hK⟩ := exists_bound_sin_mul_deriv_cutoff hℓ (n i)
  have hderivBound : ∀ k, ∀ x ∈ U, |deriv (testFactor a ℓ (ε k) {i} n i) (x i) *
      ∏ j ∈ Finset.univ.erase i, testFactor a ℓ (ε k) {i} n j (x j)| ≤
        Real.pi * |(n i : ℝ)| / ℓ + K := by
    intro k x hx
    have hxi := hx i (Set.mem_univ i)
    rw [abs_mul]
    have hprod : |∏ j ∈ Finset.univ.erase i, testFactor a ℓ (ε k) {i} n j (x j)| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one₀ (fun j _ => abs_nonneg _) fun j _ =>
        abs_testFactor_le a ℓ (ε k) {i} n j _
    have hder : |deriv (testFactor a ℓ (ε k) {i} n i) (x i)| ≤ Real.pi * |(n i : ℝ)| / ℓ + K := by
      have hD : HasDerivAt (testFactor a ℓ (ε k) {i} n i)
          (Real.pi * n i / ℓ * modeFactor a ℓ ∅ n i (x i) * cutoff (a i) ℓ (ε k) (x i) +
            modeFactor a ℓ {i} n i (x i) * deriv (cutoff (a i) ℓ (ε k)) (x i)) (x i) :=
        (hasDerivAt_modeFactor_sin a ℓ n i (x i)).mul
          ((contDiff_cutoff (a i) ℓ (ε k) (n := 1)).differentiable (by simp) (x i)).hasDerivAt
      rw [hD.deriv]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul, abs_mul, abs_of_nonneg (cutoff_nonneg _ _ _ _)]
        have h1 := abs_modeFactor_le a ℓ ∅ n i (x i)
        have h2 := cutoff_le_one (a i) ℓ (ε k) (x i)
        have h3 : |Real.pi * (n i : ℝ) / ℓ| = Real.pi * |(n i : ℝ)| / ℓ := by
          rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hℓ]
        rw [h3]
        have hpos : 0 ≤ Real.pi * |(n i : ℝ)| / ℓ := by positivity
        calc Real.pi * |(n i : ℝ)| / ℓ * |modeFactor a ℓ ∅ n i (x i)| *
              cutoff (a i) ℓ (ε k) (x i) ≤ Real.pi * |(n i : ℝ)| / ℓ * 1 * 1 :=
              mul_le_mul (mul_le_mul_of_nonneg_left h1 hpos) h2 (cutoff_nonneg _ _ _ _)
                (by positivity)
          _ = Real.pi * |(n i : ℝ)| / ℓ := by ring
      · have := hK (a i) (ε k) (x i) (hεpos k) hxi
        simpa [modeFactor] using this
    calc |deriv (testFactor a ℓ (ε k) {i} n i) (x i)| *
          |∏ j ∈ Finset.univ.erase i, testFactor a ℓ (ε k) {i} n j (x j)|
        ≤ (Real.pi * |(n i : ℝ)| / ℓ + K) * 1 :=
          mul_le_mul hder hprod (abs_nonneg _) (le_trans (abs_nonneg _) hder)
      _ = _ := mul_one _
  -- pointwise limits
  have hlimψ : ∀ x ∈ U, ∀ᶠ k in atTop, ψ k x = boxMode a ℓ {i} n x := by
    intro x hx
    filter_upwards [eventually_deep hεlim hx] with k hk
    show testFun a ℓ (ε k) {i} n x = boxMode a ℓ {i} n x
    rw [testFun, boxMode_eq_prod_modeFactor]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [testFactor, cutoff_eq_one_of_deep (hεpos k) (hk j).1 (hk j).2, mul_one]
  have hlimD : ∀ x ∈ U, ∀ᶠ k in atTop,
      deriv (testFactor a ℓ (ε k) {i} n i) (x i) *
        ∏ j ∈ Finset.univ.erase i, testFactor a ℓ (ε k) {i} n j (x j) =
      Real.pi * n i / ℓ * boxMode a ℓ ∅ n x := by
    intro x hx
    filter_upwards [eventually_deep hεlim hx] with k hk
    have hloc : testFactor a ℓ (ε k) {i} n i =ᶠ[𝓝 (x i)] modeFactor a ℓ {i} n i := by
      filter_upwards [cutoff_eventuallyEq_one (hεpos k) (hk i).1 (hk i).2] with t ht
      simp only [testFactor, ht, mul_one]
    rw [hloc.deriv_eq, (hasDerivAt_modeFactor_sin a ℓ n i (x i)).deriv,
      boxMode_eq_prod_modeFactor, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    have hrest : ∏ j ∈ Finset.univ.erase i, testFactor a ℓ (ε k) {i} n j (x j) =
        ∏ j ∈ Finset.univ.erase i, modeFactor a ℓ ∅ n j (x j) := by
      refine Finset.prod_congr rfl fun j hj => ?_
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      rw [testFactor, cutoff_eq_one_of_deep (hεpos k) (hk j).1 (hk j).2, mul_one,
        modeFactor_of_notMem a ℓ n (show j ∉ ({i} : Finset (Fin d)) by simpa using hji),
        modeFactor_of_notMem a ℓ n (Finset.notMem_empty j)]
    rw [hrest]
    ring
  -- dominated convergence
  have hA : Tendsto (fun k => ∫ x in U, gi x * ψ k x) atTop
      (𝓝 (∫ x in U, gi x * boxMode a ℓ {i} n x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => |gi x|) (fun k => ?_)
      hgi.norm (fun k => ?_) ?_
    · exact hgi.aestronglyMeasurable.mul
        (contDiff_testFun a ℓ (ε k) {i} n (m := 0)).continuous.aestronglyMeasurable
    · refine Eventually.of_forall fun x => ?_
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (abs_testFun_le a ℓ (ε k) {i} n x)
    · filter_upwards [ae_restrict_mem hUmeas] with x hx
      exact tendsto_const_nhds.congr' ((hlimψ x hx).mono fun k hk => by
        show gi x * boxMode a ℓ {i} n x = gi x * ψ k x
        rw [hk])
  have hB : Tendsto (fun k => ∫ x in U, g x * (deriv (testFactor a ℓ (ε k) {i} n i) (x i) *
      ∏ j ∈ Finset.univ.erase i, testFactor a ℓ (ε k) {i} n j (x j))) atTop
      (𝓝 (∫ x in U, g x * (Real.pi * n i / ℓ * boxMode a ℓ ∅ n x))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => (Real.pi * |(n i : ℝ)| / ℓ + K) * |g x|) (fun k => ?_)
      (hg.norm.const_mul _) (fun k => ?_) ?_
    · refine hg.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable ?_)
      refine Continuous.mul ?_ (continuous_finsetProd _ fun j _ =>
        (contDiff_testFactor a ℓ (ε k) {i} n j (m := 0)).continuous.comp (continuous_apply j))
      exact ((contDiff_testFactor a ℓ (ε k) {i} n i (m := 1)).continuous_deriv le_rfl).comp
        (continuous_apply i)
    · filter_upwards [ae_restrict_mem hUmeas] with x hx
      rw [Real.norm_eq_abs, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hderivBound k x hx) (abs_nonneg _)
    · filter_upwards [ae_restrict_mem hUmeas] with x hx
      exact tendsto_const_nhds.congr' ((hlimD x hx).mono fun k hk => by
        show g x * (Real.pi * n i / ℓ * boxMode a ℓ ∅ n x) =
          g x * (deriv (testFactor a ℓ (ε k) {i} n i) (x i) *
            ∏ j ∈ Finset.univ.erase i, testFactor a ℓ (ε k) {i} n j (x j))
        rw [hk])
  have hB' : Tendsto (fun k => ∫ x in U, g x * (deriv (testFactor a ℓ (ε k) {i} n i) (x i) *
      ∏ j ∈ Finset.univ.erase i, testFactor a ℓ (ε k) {i} n j (x j))) atTop
      (𝓝 (-∫ x in U, gi x * boxMode a ℓ {i} n x)) := by
    simp only [hweak]
    exact hA.neg
  have huniq := tendsto_nhds_unique hB hB'
  have hpull : ∫ x in U, g x * (Real.pi * n i / ℓ * boxMode a ℓ ∅ n x) =
      Real.pi * n i / ℓ * ∫ x in U, g x * boxMode a ℓ ∅ n x := by
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  rw [hpull] at huniq
  linear_combination huniq

end GMCExplicitDelta.Haar.Torus
