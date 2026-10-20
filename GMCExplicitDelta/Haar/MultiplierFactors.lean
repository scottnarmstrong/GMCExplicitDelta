module

public import GMCExplicitDelta.Haar.MultiplierLimits
public import Mathlib.Analysis.SpecificLimits.Basic

/-! Smooth scaled factors for each component of the cutoff gradient. -/
@[expose] public section

open Real Filter
open scoped Topology

namespace GMCExplicitDelta.Haar

noncomputable def multiplierFactor (ω S : ℝ) (slope : Bool) (y : ℝ) : ℝ :=
  if slope then cutoffSlope ω (y / S) / S else cutoffProfile ω (y / S)

noncomputable def multiplierFactorDeriv (ω S : ℝ) (slope : Bool) (y : ℝ) : ℝ :=
  if slope then cutoffCurvature ω (y / S) / S ^ 2 else cutoffSlope ω (y / S) / S

noncomputable def multiplierFactorApprox (ω S ε : ℝ) (slope : Bool) (y : ℝ) : ℝ :=
  if slope then slopeApprox ω ε (y / S) / S else profileApprox ω ε (y / S)

noncomputable def multiplierFactorDerivApprox (ω S ε : ℝ) (slope : Bool) (y : ℝ) : ℝ :=
  if slope then curvatureApprox ω ε (y / S) / S ^ 2 else slopeApprox ω ε (y / S) / S

theorem multiplierFactor_continuous {ω : ℝ} (hω : ω ≤ 1 / 2) (S : ℝ) (b : Bool) :
    Continuous (multiplierFactor ω S b) := by
  cases b
  · exact (cutoffProfile_contDiff hω).continuous.comp (by fun_prop)
  · exact ((cutoffSlope_continuous hω).comp (by fun_prop)).div_const S

theorem multiplierFactorDeriv_measurable (ω S : ℝ) (b : Bool) (hω : ω ≤ 1 / 2) :
    Measurable (multiplierFactorDeriv ω S b) := by
  cases b
  · exact ((cutoffSlope_continuous hω).measurable.comp (by fun_prop)).div_const S
  · exact ((cutoffCurvature_measurable ω).comp (by fun_prop)).div_const (S ^ 2)

theorem multiplierFactorApprox_contDiff (ω S ε : ℝ) (b : Bool) :
    ContDiff ℝ (⊤ : ℕ∞) (multiplierFactorApprox ω S ε b) := by
  cases b
  · exact (profileApprox_contDiff ω ε).comp (by fun_prop)
  · exact ((slopeApprox_contDiff ω ε).comp (by fun_prop)).div_const S

theorem multiplierFactorApprox_hasDerivAt (ω S ε : ℝ) (b : Bool) (y : ℝ) :
    HasDerivAt (multiplierFactorApprox ω S ε b) (multiplierFactorDerivApprox ω S ε b y) y := by
  have hy : HasDerivAt (fun y : ℝ => y / S) (1 / S) y := (hasDerivAt_id y).div_const S
  cases b
  · unfold multiplierFactorApprox multiplierFactorDerivApprox
    have h := (profileApprox_hasDerivAt ω ε (y / S)).comp y hy
    simpa only [multiplierFactorApprox, multiplierFactorDerivApprox, Bool.false_eq_true,
      ite_false, Function.comp_def, div_eq_mul_inv, one_mul] using h
  · unfold multiplierFactorApprox multiplierFactorDerivApprox
    have h := ((slopeApprox_hasDerivAt ω ε (y / S)).comp y hy).div_const S
    simpa only [multiplierFactorApprox, multiplierFactorDerivApprox, ite_true,
      Function.comp_def, div_eq_mul_inv, one_mul, pow_two, mul_assoc, mul_inv_rev] using h

theorem multiplierFactorApprox_tendsto {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n)
    (hεlim : Tendsto ε atTop (𝓝 0)) {ω : ℝ} (hω : ω ≤ 1 / 2) (S : ℝ) (b : Bool) (y : ℝ) :
    Tendsto (fun n => multiplierFactorApprox ω S (ε n) b y) atTop (𝓝 (multiplierFactor ω S b y)) := by
  cases b
  · exact profileApprox_tendsto hε hεlim hω (y / S)
  · exact (slopeApprox_tendsto hε hεlim hω (y / S)).div_const S

theorem multiplierFactorDerivApprox_tendsto {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n)
    (hεlim : Tendsto ε atTop (𝓝 0)) {ω : ℝ} (hω : ω ≤ 1 / 2) (S : ℝ) (b : Bool) (y : ℝ) :
    Tendsto (fun n => multiplierFactorDerivApprox ω S (ε n) b y) atTop
      (𝓝 (multiplierFactorDeriv ω S b y)) := by
  cases b
  · exact (slopeApprox_tendsto hε hεlim hω (y / S)).div_const S
  · exact (tendsto_const_nhds.congr' (curvatureApprox_eventuallyEq hε hεlim hω).symm).div_const (S ^ 2)

/-- A coarse common bound used only for dominated convergence, not for the
sharp energy estimate. -/
noncomputable def multiplierFactorBound (ω S : ℝ) : ℝ :=
  let C := 1 + 2 * (π / (2 * ω)) ^ 2
  max C (max (C / |S|) (C / |S| ^ 2))

theorem multiplierFactorBound_nonneg (ω S : ℝ) : 0 ≤ multiplierFactorBound ω S :=
  (by positivity : 0 ≤ 1 + 2 * (π / (2 * ω)) ^ 2).trans (le_max_left _ _)

theorem multiplierFactorApprox_bounds (ω S ε : ℝ) (b : Bool) (y : ℝ) (hy : |y / S| ≤ 1) :
    ‖multiplierFactorApprox ω S ε b y‖ ≤ multiplierFactorBound ω S ∧
      ‖multiplierFactorDerivApprox ω S ε b y‖ ≤ multiplierFactorBound ω S := by
  let C := 1 + 2 * (π / (2 * ω)) ^ 2
  have hs : ‖slopeApprox ω ε (y / S)‖ ≤ C := by
    calc
      _ ≤ 2 * (π / (2 * ω)) ^ 2 * |y / S| := norm_slopeApprox_le _ _ _
      _ ≤ 2 * (π / (2 * ω)) ^ 2 * 1 := mul_le_mul_of_nonneg_left hy (by positivity)
      _ ≤ C := by dsimp only [C]; linarith
  have hp : ‖profileApprox ω ε (y / S)‖ ≤ C := by
    calc
      _ ≤ 1 + 2 * (π / (2 * ω)) ^ 2 * |y / S| ^ 2 := norm_profileApprox_le _ _ _
      _ ≤ 1 + 2 * (π / (2 * ω)) ^ 2 * 1 :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg _) hy) (by positivity))
      _ = C := by ring
  have hc : ‖curvatureApprox ω ε (y / S)‖ ≤ C := by
    have h := abs_curvatureApprox_le ω ε (y / S)
    rw [← Real.norm_eq_abs] at h
    exact h.trans (by dsimp only [C]; linarith)
  have hsd : ‖slopeApprox ω ε (y / S) / S‖ ≤ C / |S| := by
    rw [norm_div, Real.norm_eq_abs S]
    exact div_le_div_of_nonneg_right hs (abs_nonneg _)
  have hcd : ‖curvatureApprox ω ε (y / S) / S ^ 2‖ ≤ C / |S| ^ 2 := by
    rw [norm_div, norm_pow, Real.norm_eq_abs S]
    exact div_le_div_of_nonneg_right hc (sq_nonneg _)
  cases b
  · exact ⟨hp.trans (le_max_left _ _),
      hsd.trans ((le_max_left _ _).trans (le_max_right _ _))⟩
  · exact ⟨hsd.trans ((le_max_left _ _).trans (le_max_right _ _)),
      hcd.trans ((le_max_right _ _).trans (le_max_right _ _))⟩

theorem multiplierFactor_bounds {ω : ℝ} (hω : ω ≤ 1 / 2) (S : ℝ) (b : Bool) (y : ℝ)
    (hy : |y / S| ≤ 1) :
    ‖multiplierFactor ω S b y‖ ≤ multiplierFactorBound ω S ∧
      ‖multiplierFactorDeriv ω S b y‖ ≤ multiplierFactorBound ω S := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε : ∀ n, 0 < ε n := fun n => by dsimp only [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  exact ⟨le_of_tendsto (multiplierFactorApprox_tendsto hε hεlim hω S b y).norm
      (Filter.Eventually.of_forall (fun n => (multiplierFactorApprox_bounds ω S (ε n) b y hy).1)),
    le_of_tendsto (multiplierFactorDerivApprox_tendsto hε hεlim hω S b y).norm
      (Filter.Eventually.of_forall (fun n => (multiplierFactorApprox_bounds ω S (ε n) b y hy).2))⟩

end GMCExplicitDelta.Haar
