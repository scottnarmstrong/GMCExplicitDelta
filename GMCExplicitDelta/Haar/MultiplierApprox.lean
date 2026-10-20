module

public import GMCExplicitDelta.Haar.CutoffProfile
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Smooth approximations of the plateau curvature and its primitives. -/
@[expose] public section

open Real Set Filter
open scoped Topology

namespace GMCExplicitDelta.Haar

/-- The primitive based at zero. -/
noncomputable def primitive (f : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, f t

theorem primitive_hasDerivAt {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (primitive f) (f x) x :=
  intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
    (hf.stronglyMeasurableAtFilter _ _) hf.continuousAt

theorem primitive_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (primitive f) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun x => (primitive_hasDerivAt hf.continuous x).differentiableAt, ?_⟩
  have he : deriv (primitive f) = f := funext fun x => (primitive_hasDerivAt hf.continuous x).deriv
  rw [he]
  exact hf

/-- A smooth boundary-layer switch. Its transition interval is `[c,c+ε]`. -/
noncomputable def layerSwitch (c ε x : ℝ) : ℝ := Real.smoothTransition ((x - c) / ε)

theorem layerSwitch_contDiff (c ε : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (layerSwitch c ε) := by
  unfold layerSwitch
  exact Real.smoothTransition.contDiff.comp (by fun_prop)

theorem layerSwitch_bounds (c ε x : ℝ) :
    0 ≤ layerSwitch c ε x ∧ layerSwitch c ε x ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-- Smooth approximation of the piecewise second derivative. We integrate this
twice, so derivatives of a transition switch never enter the multiplier bounds. -/
noncomputable def curvatureApprox (ω ε x : ℝ) : ℝ :=
  -(π / (2 * ω)) ^ 2 *
    ((1 - layerSwitch (-(1 / 2 - ω)) ε x) * cos (π / (2 * ω) * (x + (1 / 2 - ω))) +
      layerSwitch (1 / 2 - ω) ε x * cos (π / (2 * ω) * (x - (1 / 2 - ω))))

theorem curvatureApprox_contDiff (ω ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (curvatureApprox ω ε) := by
  unfold curvatureApprox
  exact contDiff_const.mul
    (((contDiff_const.sub (layerSwitch_contDiff _ _)).mul (by fun_prop)).add
      ((layerSwitch_contDiff _ _).mul (by fun_prop)))

theorem abs_curvatureApprox_le (ω ε x : ℝ) :
    |curvatureApprox ω ε x| ≤ 2 * (π / (2 * ω)) ^ 2 := by
  have hl := layerSwitch_bounds (-(1 / 2 - ω)) ε x
  have hr := layerSwitch_bounds (1 / 2 - ω) ε x
  have h1 : |1 - layerSwitch (-(1 / 2 - ω)) ε x| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hl.2)]
    linarith only [hl.1]
  have h2 : |layerSwitch (1 / 2 - ω) ε x| ≤ 1 := by
    rw [abs_of_nonneg hr.1]
    exact hr.2
  have hs : |(1 - layerSwitch (-(1 / 2 - ω)) ε x) * cos (π / (2 * ω) * (x + (1 / 2 - ω))) +
      layerSwitch (1 / 2 - ω) ε x * cos (π / (2 * ω) * (x - (1 / 2 - ω)))| ≤ 2 := by
    calc
      _ ≤ |(1 - layerSwitch (-(1 / 2 - ω)) ε x) * cos (π / (2 * ω) * (x + (1 / 2 - ω)))| +
          |layerSwitch (1 / 2 - ω) ε x * cos (π / (2 * ω) * (x - (1 / 2 - ω)))| := abs_add_le _ _
      _ ≤ 1 * 1 + 1 * 1 := add_le_add
        (by rw [abs_mul]; exact mul_le_mul h1 (abs_cos_le_one _) (abs_nonneg _) zero_le_one)
        (by rw [abs_mul]; exact mul_le_mul h2 (abs_cos_le_one _) (abs_nonneg _) zero_le_one)
      _ = 2 := by norm_num
  unfold curvatureApprox
  rw [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg _)]
  exact (mul_le_mul_of_nonneg_left hs (sq_nonneg _)).trans_eq (mul_comm _ _)

/-- Smooth slope approximants with a uniformly bounded derivative. -/
noncomputable def slopeApprox (ω ε : ℝ) : ℝ → ℝ := primitive (curvatureApprox ω ε)

/-- Smooth profile approximants, normalized to have value one at zero. -/
noncomputable def profileApprox (ω ε x : ℝ) : ℝ := 1 + primitive (slopeApprox ω ε) x

theorem slopeApprox_contDiff (ω ε : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (slopeApprox ω ε) :=
  primitive_contDiff (curvatureApprox_contDiff ω ε)

theorem slopeApprox_hasDerivAt (ω ε x : ℝ) :
    HasDerivAt (slopeApprox ω ε) (curvatureApprox ω ε x) x :=
  primitive_hasDerivAt (curvatureApprox_contDiff ω ε).continuous x

theorem profileApprox_contDiff (ω ε : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (profileApprox ω ε) :=
  contDiff_const.add (primitive_contDiff (slopeApprox_contDiff ω ε))

theorem profileApprox_hasDerivAt (ω ε x : ℝ) :
    HasDerivAt (profileApprox ω ε) (slopeApprox ω ε x) x := by
  unfold profileApprox
  exact (primitive_hasDerivAt (slopeApprox_contDiff ω ε).continuous x).const_add 1

theorem norm_slopeApprox_le (ω ε x : ℝ) :
    ‖slopeApprox ω ε x‖ ≤ 2 * (π / (2 * ω)) ^ 2 * |x| := by
  unfold slopeApprox primitive
  simpa only [sub_zero] using
    (intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := x) (fun t _ => by
        simpa only [Real.norm_eq_abs] using abs_curvatureApprox_le ω ε t))

theorem abs_le_abs_of_mem_zero_uIoc {t x : ℝ} (ht : t ∈ uIoc 0 x) : |t| ≤ |x| := by
  rcases le_total 0 x with hx | hx
  · rw [uIoc_of_le hx, mem_Ioc] at ht
    rw [abs_of_nonneg hx, abs_of_nonneg ht.1.le]
    exact ht.2
  · rw [uIoc_of_ge hx, mem_Ioc] at ht
    rw [abs_of_nonpos hx, abs_of_nonpos ht.2]
    exact neg_le_neg ht.1.le

theorem norm_profileApprox_le (ω ε x : ℝ) :
    ‖profileApprox ω ε x‖ ≤ 1 + 2 * (π / (2 * ω)) ^ 2 * |x| ^ 2 := by
  have hi : ‖primitive (slopeApprox ω ε) x‖ ≤
      (2 * (π / (2 * ω)) ^ 2 * |x|) * |x| := by
    apply le_trans (intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := x) (C := 2 * (π / (2 * ω)) ^ 2 * |x|) (fun t ht =>
        (norm_slopeApprox_le ω ε t).trans
          (mul_le_mul_of_nonneg_left (abs_le_abs_of_mem_zero_uIoc ht) (by positivity))))
    rw [sub_zero]
  calc
    ‖profileApprox ω ε x‖ ≤ ‖(1 : ℝ)‖ + ‖primitive (slopeApprox ω ε) x‖ := norm_add_le _ _
    _ ≤ 1 + (2 * (π / (2 * ω)) ^ 2 * |x|) * |x| := by
      rw [norm_one]
      exact add_le_add le_rfl hi
    _ = _ := by ring

end GMCExplicitDelta.Haar
