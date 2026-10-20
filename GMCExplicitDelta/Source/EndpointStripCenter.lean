module

public import GMCExplicitDelta.Source.EndpointStripField
public import SubdiffusiveProcess.Assumptions.Actions
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Centering: `E[f(g(z)) ∂_e g(z)] = 0` from stationarity
-/

@[expose] public section

namespace GMCExplicitDelta.Source

open Homogenization MeasureTheory ProbabilityTheory Filter Topology
open SubdiffusiveProcess.Model SubdiffusiveProcess.Model.PotentialField

variable {d : ℕ}

theorem zero_smul_mem_openCube {t : ℝ} (ht : |t| < 1 / 2) :
    t • diagDir d ∈ openCubeSet (originCube d 0) := by
  intro i
  simp [diagDir, originCube, cubeScaleFactor]
  rw [abs_lt] at ht
  constructor <;> linarith [ht.1, ht.2]

theorem hasDerivAt_ray (g : PotentialField d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => g (s • diagDir d)) (deriv g (t • diagDir d) (diagDir d)) t := by
  have h1 : HasDerivAt (fun s : ℝ => s • diagDir d) (diagDir d) t := by
    simpa using (hasDerivAt_id t).smul_const (diagDir d)
  exact (g.hasFDerivAt (t • diagDir d)).comp_hasDerivAt t h1

/-- Origin version of the centering identity. -/
theorem integral_centering_origin {μ : Measure (PotentialField d)} [IsProbabilityMeasure μ]
    (hS : ∀ z : Vec d, Measure.map (translate z) μ = μ)
    (hW : Integrable (fun g : PotentialField d => g2Observable g) μ)
    {f : ℝ → ℝ} (hf : Continuous f) {Cf : ℝ} (hfb : ∀ x, |f x| ≤ Cf) :
    ∫ g, f (g 0) * (deriv g 0 (diagDir d)) ∂μ = 0 := by
  set F0 : ℝ → ℝ := fun x => ∫ s in (0:ℝ)..x, f s with hF0
  have hF0c : Continuous F0 := by
    exact continuous_iff_continuousAt.2 fun x => (hf.integral_hasStrictDerivAt 0 x).hasDerivAt.continuousAt
  have hF0d : ∀ x, HasDerivAt F0 (f x) x := fun x => (hf.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hCf : 0 ≤ Cf := (abs_nonneg _).trans (hfb 0)
  have hF0b : ∀ x, |F0 x| ≤ Cf * |x| := by
    intro x
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := x) (f := f) (C := Cf)
      (fun s _ => by rw [Real.norm_eq_abs]; exact hfb s)
    rw [Real.norm_eq_abs, sub_zero] at this
    exact this
  set Φ : ℝ → ℝ := fun t => ∫ g, F0 (g (t • diagDir d)) ∂μ with hΦ
  have hconst : ∀ t, Φ t = Φ 0 := by
    intro t
    simp only [hΦ, zero_smul]
    have h1 : ∀ s : Vec d, ∫ g, F0 (g s) ∂μ = ∫ g, F0 (g 0) ∂μ := by
      intro s
      have hm := integral_map (μ := μ) (φ := translate s) (f := fun g : PotentialField d => F0 (g 0))
        (measurable_translate s).aemeasurable (hF0c.comp (continuous_eval 0)).aestronglyMeasurable
      rw [hS s] at hm
      simpa using hm.symm
    exact h1 _
  have hd1 : HasDerivAt Φ 0 0 := by
    have : Φ = fun _ => Φ 0 := funext hconst
    rw [this]; exact hasDerivAt_const _ _
  have hd2 : HasDerivAt Φ (∫ g, f (g ((0:ℝ) • diagDir d)) * deriv g ((0:ℝ) • diagDir d) (diagDir d) ∂μ) 0 := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
      (F := fun t g => F0 (g (t • diagDir d)))
      (F' := fun t g => f (g (t • diagDir d)) * deriv g (t • diagDir d) (diagDir d))
      (x₀ := 0) (bound := fun g => Cf * g2Observable g) (s := Metric.ball (0:ℝ) (1 / 2)) (Metric.ball_mem_nhds 0 (by norm_num)) ?_ ?_ ?_ ?_ ?_ ?_).2
    · exact Eventually.of_forall fun t => (hF0c.comp ((continuous_eval _))).aestronglyMeasurable
    · refine Integrable.mono' (g := fun g => Cf * g2Observable g) (hW.const_mul _)
        (by simpa [Function.comp_def] using (hF0c.comp (continuous_eval (d := d) 0)).aestronglyMeasurable)
        (Eventually.of_forall fun g => ?_)
      simp only [zero_smul, Real.norm_eq_abs]
      refine (hF0b _).trans ?_
      exact mul_le_mul_of_nonneg_left (abs_apply_le_g2Observable g (by
        simpa using zero_smul_mem_openCube (d := d) (t := 0) (by norm_num))) hCf
    · refine Continuous.aestronglyMeasurable ?_
      have := (continuous_eval (d := d) 0).comp continuous_id
      simp only [zero_smul]
      exact (hf.comp (continuous_eval 0)).mul (((continuous_eval_deriv 0)).clm_apply continuous_const)
    · refine Eventually.of_forall fun g t ht => ?_
      have ht' : |t| < 1 / 2 := by simpa [Real.dist_eq] using ht
      have hx := zero_smul_mem_openCube (d := d) ht'
      rw [Real.norm_eq_abs, abs_mul]
      have h1 := hfb (g (t • diagDir d))
      have h2 : |deriv g (t • diagDir d) (diagDir d)| ≤ g2Observable g := by
        have := (deriv g (t • diagDir d)).le_opNorm (diagDir d)
        rw [← Real.norm_eq_abs]
        calc _ ≤ ‖deriv g (t • diagDir d)‖ * ‖diagDir d‖ := this
          _ ≤ ‖deriv g (t • diagDir d)‖ * 1 := by gcongr; exact norm_diagDir_le
          _ ≤ _ := by rw [mul_one]; exact norm_deriv_le_g2Observable g hx
      exact mul_le_mul h1 h2 (abs_nonneg _) hCf
    · exact hW.const_mul _
    · refine Eventually.of_forall fun g t _ => ?_
      exact (hF0d (g (t • diagDir d))).comp t (hasDerivAt_ray g t)
  have := hd1.unique hd2
  simpa using this.symm

end GMCExplicitDelta.Source
