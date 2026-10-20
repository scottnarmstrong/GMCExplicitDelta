module

public import GMCExplicitDelta.Source.EndpointStripSource
public import Homogenization.Geometry.ConvexDomain
public import Mathlib.Analysis.Calculus.MeanValue

/-! # Translated unit-cube controls for the rescaled layers (S1(c)) -/

@[expose] public section

open MeasureTheory Homogenization ProbabilityTheory
open SubdiffusiveProcess.Model

namespace GMCExplicitDelta.Assembly.GridMax

variable {d : ℕ}

/-- Undo the marginal triadic scaling. -/
noncomputable def unscale (i : ℕ) (g : PotentialField d) : PotentialField d :=
  PotentialField.spatialScale ((3 : ℝ) ^ i) g

/-- The unscaled layer viewed around the center of a translated unit cube. -/
noncomputable def regularLayer (i : ℕ) (z : Homogenization.Vec d) (ω : PotentialSample d) : PotentialField d :=
  PotentialField.translate (((3 : ℝ) ^ i)⁻¹ • z) (unscale i (ω i))

/-- The regularity control of the layer on that cube. -/
noncomputable def W (i : ℕ) (z : Homogenization.Vec d) (ω : PotentialSample d) : ℝ :=
  PotentialField.g2Observable (regularLayer i z ω)

/-- The regularity observable is measurable on samples. -/
theorem W_measurable (i : ℕ) (z : Homogenization.Vec d) : Measurable (W i z) :=
  PotentialField.g2Observable_measurable.comp
    ((PotentialField.measurable_translate _).comp
      ((PotentialField.continuous_spatialScale _).measurable.comp (measurable_pi_apply i)))

/-- It is a nonnegative control. -/
theorem W_nonneg (i : ℕ) (z : Homogenization.Vec d) (ω : PotentialSample d) : 0 ≤ W i z ω :=
  Source.g2Observable_nonneg _

/-- Scaling back and translating restores precisely the zero-layer law. -/
theorem regularLayer_map (M : GMCModel d) (i : ℕ) (z : Homogenization.Vec d) :
    M.P.toMeasure.map (regularLayer i z) = (zeroPotentialLaw M.P).toMeasure := by
  have hu : Measurable (unscale (d := d) i) := (PotentialField.continuous_spatialScale _).measurable
  have hc : Measurable (fun ω : PotentialSample d => ω i) := measurable_pi_apply i
  have hundo (g : PotentialField d) : unscale i (PotentialField.triadicScale i g) = g := by
    apply PotentialField.ext
    intro x
    simp only [unscale, PotentialField.spatialScale_apply, PotentialField.triadicScale_apply, smul_smul]
    rw [inv_mul_cancel₀ (by positivity : (3 : ℝ) ^ i ≠ 0), one_smul]
  have hun : M.P.toMeasure.map (fun ω : PotentialSample d => unscale i (ω i)) =
      (zeroPotentialLaw M.P).toMeasure := by
    calc
      _ = ((potentialMarginalLaw M.P i).toMeasure).map (unscale i) := by
        rw [potentialMarginalLaw, ProbabilityMeasure.toMeasure_map, Measure.map_map hu hc]
        rfl
      _ = (((zeroPotentialLaw M.P).toMeasure).map (PotentialField.triadicScale i)).map (unscale i) := by
        rw [M.shellPrefix.marginal_scaling i, ProbabilityMeasure.toMeasure_map]
      _ = _ := by
        rw [Measure.map_map hu (PotentialField.measurable_triadicScale i)]
        simp only [Function.comp_def, hundo]
        change Measure.map id _ = _
        exact Measure.map_id
  rw [show regularLayer i z = PotentialField.translate (((3 : ℝ) ^ i)⁻¹ • z) ∘
    (fun ω => unscale i (ω i)) from rfl,
    ← Measure.map_map (f := fun ω : PotentialSample d => unscale i (ω i))
      (PotentialField.measurable_translate _) (hu.comp hc), hun]
  exact M.G1.stationary _

/-- The exact unit Orlicz bound is retained after marginal scaling and translation. -/
theorem W_orlicz (M : GMCModel d) (i : ℕ) (z : Homogenization.Vec d) :
    Integrable (fun ω => Real.exp (W i z ω ^ 2 / M.delta ^ 2)) M.P.toMeasure ∧
      ∫ ω, Real.exp (W i z ω ^ 2 / M.delta ^ 2) ∂M.P.toMeasure ≤ 2 := by
  have hm : Measurable (regularLayer i z) :=
    (PotentialField.measurable_translate _).comp
      ((PotentialField.continuous_spatialScale _).measurable.comp (measurable_pi_apply i))
  let f := fun g : PotentialField d => Real.exp (PotentialField.g2Observable g ^ 2 / M.delta ^ 2)
  have hf : AEStronglyMeasurable f (M.P.toMeasure.map (regularLayer i z)) := by
    rw [regularLayer_map]
    exact ((PotentialField.g2Observable_measurable.pow_const 2).div_const _).exp.aestronglyMeasurable
  have hi : Integrable f (M.P.toMeasure.map (regularLayer i z)) := by
    rw [regularLayer_map]
    exact (Source.endpointModel_of_gmc M).expSq_int
  refine ⟨(integrable_map_measure hf hm.aemeasurable).1 hi, ?_⟩
  have he := integral_map hm.aemeasurable hf
  rw [regularLayer_map] at he
  exact he.symm.trans_le (Source.endpointModel_of_gmc M).expSq_le

/-- A field's G2 observable controls its Lipschitz constant on the open unit cube. -/
theorem field_increment_le (g : PotentialField d) {x y : Homogenization.Vec d}
    (hx : x ∈ openCubeSet (originCube d 0)) (hy : y ∈ openCubeSet (originCube d 0)) :
    |g x - g y| ≤ PotentialField.g2Observable g * ‖x - y‖ := by
  simpa only [Real.norm_eq_abs] using
    (convex_openCubeSet (originCube d 0)).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun x _ => (g.hasFDerivAt x).hasFDerivWithinAt)
      (fun x hx => Source.norm_deriv_le_g2Observable g hx) hy hx

/-- Contraction preserves the open centered unit cube. -/
theorem contracted_mem {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) {x : Homogenization.Vec d}
    (hx : x ∈ openCubeSet (originCube d 0)) : r • x ∈ openCubeSet (originCube d 0) := by
  rw [mem_openCubeSet_originCube_iff] at hx ⊢
  intro k
  have hk := hx k
  norm_num only [zpow_zero, mul_one, Pi.smul_apply, smul_eq_mul] at hk ⊢
  constructor <;> nlinarith

/-- Values of the rescaled translated layer at normalized coordinates. -/
theorem regularLayer_apply (i : ℕ) (z : Homogenization.Vec d) (ω : PotentialSample d)
    (x : Homogenization.Vec d) :
    regularLayer i z ω (((3 : ℝ) ^ i)⁻¹ • x) = ω i (x + z) := by
  simp only [regularLayer, unscale, PotentialField.translate_apply, PotentialField.spatialScale_apply,
    smul_add, smul_smul]
  rw [mul_inv_cancel₀ (by positivity : (3 : ℝ) ^ i ≠ 0)]
  simp only [one_smul]

/-- S1(c), with the exact geometric factor 3⁻ⁱ. -/
theorem layer_increment_le (i : ℕ) (z : Homogenization.Vec d) (ω : PotentialSample d)
    {x y : Homogenization.Vec d} (hx : x ∈ openCubeSet (originCube d 0))
    (hy : y ∈ openCubeSet (originCube d 0)) :
    |ω i (x + z) - ω i (y + z)| ≤ ((3 : ℝ) ^ i)⁻¹ * W i z ω * ‖x - y‖ := by
  have hr : 0 < ((3 : ℝ) ^ i)⁻¹ := inv_pos.2 (by positivity)
  have hr1 : ((3 : ℝ) ^ i)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).2 (one_le_pow₀ (by norm_num))
  have h := field_increment_le (regularLayer i z ω)
    (contracted_mem hr hr1 hx) (contracted_mem hr hr1 hy)
  rw [regularLayer_apply, regularLayer_apply, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hr] at h
  exact h.trans_eq (by unfold W; ring)

end GMCExplicitDelta.Assembly.GridMax
