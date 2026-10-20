module

public import GMCExplicitDelta.Source.EndpointStripSource
public import GMCExplicitDelta.Source.MomentRatios

/-! # Model moment ratios from the endpoint-strip law (step S4) -/

@[expose] public section

namespace GMCExplicitDelta.Source

open Homogenization MeasureTheory ProbabilityTheory
open SubdiffusiveProcess.Model SubdiffusiveProcess.Model.PotentialField

/-- Fourth and higher even moments with the sharpened endpoint proxy. -/
theorem source_even_moment_ratio {d : ℕ} (M : GMCModel d) (x : Vec d)
    {k : ℕ} (hk : 2 ≤ k) :
    Integrable (fun ω : PotentialSample d => (ω 0 x) ^ (2 * k)) M.P.toMeasure ∧
      ∫ ω, (ω 0 x) ^ (2 * k) ∂M.P.toMeasure ≤
        (if k = 2 then (GMCExplicitDelta.Contract.ratioC2 : ℝ) else
          (GMCExplicitDelta.Contract.ratioC3 : ℝ)) *
        ((2 * k - 1).doubleFactorial : ℝ) * ((3 - 2 * Real.sqrt 2) / 16 * M.delta ^ 2) ^ k := by
  have hE := endpointModel_of_gmc M
  set μ := (zeroPotentialLaw M.P).toMeasure with hμ
  have hδ := M.shellPrefix.delta_pos
  obtain ⟨hint, h1⟩ := hE.nu_exp
  have hXm : Measurable (fun ω : PotentialSample d => ω 0 x) :=
    (PotentialField.measurable_eval x).comp (measurable_pi_apply 0)
  -- the law of `ω 0 x` under `P` is the law of `g 0`
  have hlaw : M.P.toMeasure.map (fun ω : PotentialSample d => ω 0 x) = lawZero μ := by
    rw [← map_eval_eq hE.stat x]
    rw [hμ, zeroPotentialLaw, potentialMarginalLaw, ProbabilityMeasure.toMeasure_map,
      Measure.map_map (PotentialField.measurable_eval x) (measurable_pi_apply 0)]
    rfl
  have hα : 0 < (1 + stripK) ^ 2 := by have := stripK_pos; positivity
  have hmE : AEStronglyMeasurable (fun y : ℝ =>
      Real.exp ((1 + stripK) ^ 2 * y ^ 2 / M.delta ^ 2)) (M.P.toMeasure.map (fun ω : PotentialSample d => ω 0 x)) := by
    rw [hlaw]; exact hint.aestronglyMeasurable
  have hint' : Integrable (fun ω : PotentialSample d =>
      Real.exp ((1 + stripK) ^ 2 * (ω 0 x) ^ 2 / M.delta ^ 2)) M.P.toMeasure := by
    have := (integrable_map_measure hmE hXm.aemeasurable).1 (by rw [hlaw]; exact hint)
    exact this
  have h1' : ∫ ω, Real.exp ((1 + stripK) ^ 2 * (ω 0 x) ^ 2 / M.delta ^ 2) ∂M.P.toMeasure ≤
      Real.sqrt 3 := by
    have := integral_map (μ := M.P.toMeasure) hXm.aemeasurable hmE
    rw [hlaw] at this
    rw [← this]; exact h1
  let α := (1 + stripK) ^ 2
  have hα0 : α ≠ 0 := hα.ne'
  let Z : PotentialSample d → ℝ := fun ω => α * (ω 0 x) ^ 2 / M.delta ^ 2
  have hZm : Measurable Z := by dsimp [Z]; fun_prop
  have hZ0 : ∀ ω, 0 ≤ Z ω := fun ω => by dsimp [Z]; positivity
  have hnorm : Integrable (fun ω => Z ω ^ k) M.P.toMeasure ∧
      ∫ ω, Z ω ^ k ∂M.P.toMeasure ≤
        (if k = 2 then (GMCExplicitDelta.Contract.ratioC2 : ℝ) else
          (GMCExplicitDelta.Contract.ratioC3 : ℝ)) * gaussianSquareMoment k := by
    by_cases hk2 : k = 2
    · subst k
      simpa only [ite_eq_left rfl, ite_true] using integral_sq_le_ratioC2 hZm hZ0 hint' h1'
    · simpa only [ite_eq_right hk2] using integral_pow_le_ratioC3 hZm hZ0 hint' h1' (by omega)
  have hpt : ∀ ω : PotentialSample d, (ω 0 x) ^ (2 * k) =
      (M.delta ^ 2 / α) ^ k * Z ω ^ k := by
    intro ω
    dsimp [Z]
    rw [← mul_pow, pow_mul]
    congr 1
    field_simp [hα0]
  simp_rw [hpt]
  refine ⟨hnorm.1.const_mul _, ?_⟩
  rw [integral_const_mul]
  have hscale : M.delta ^ 2 / (2 * α) = (3 - 2 * Real.sqrt 2) / 16 * M.delta ^ 2 := by
    rw [div_eq_iff (by dsimp [α]; positivity)]
    dsimp [α]
    linear_combination (-(M.delta ^ 2) / 8) * stripAlpha_mul
  calc
    _ ≤ (M.delta ^ 2 / α) ^ k *
        ((if k = 2 then (GMCExplicitDelta.Contract.ratioC2 : ℝ) else
          (GMCExplicitDelta.Contract.ratioC3 : ℝ)) * gaussianSquareMoment k) :=
      mul_le_mul_of_nonneg_left hnorm.2 (by positivity)
    _ = _ := by
      unfold gaussianSquareMoment
      rw [← hscale, show M.delta ^ 2 / (2 * α) = (M.delta ^ 2 / α) / 2 by field_simp [hα0],
        div_pow]
      ring_nf
      norm_num

/-- The rational all-even proxy dominates the sharp endpoint proxy. -/
theorem endpoint_proxy_le_proxyA : (3 - 2 * Real.sqrt 2) / 16 ≤
    (GMCExplicitDelta.Contract.proxyA : ℝ) := by
  have hs : (1.41421356 : ℝ) ≤ Real.sqrt 2 := by
    exact Real.le_sqrt_of_sq_le (by norm_num)
  norm_num [GMCExplicitDelta.Contract.proxyA]
  linarith only [hs]

/-- S4: the model fourth moment, with the exact contract constants. -/
theorem source_fourth_moment_ratio {d : ℕ} (M : GMCModel d) (x : Vec d) :
    Integrable (fun ω : PotentialSample d => (ω 0 x) ^ 4) M.P.toMeasure ∧
      ∫ ω, (ω 0 x) ^ 4 ∂M.P.toMeasure ≤
        (GMCExplicitDelta.Contract.ratioC2 : ℝ) * 3 *
          ((GMCExplicitDelta.Contract.proxyA : ℝ) * M.delta ^ 2) ^ 2 := by
  obtain ⟨hi, hb⟩ := source_even_moment_ratio M x (k := 2) (by norm_num)
  norm_num [Nat.doubleFactorial] at hi hb
  refine ⟨hi, hb.trans ?_⟩
  apply mul_le_mul_of_nonneg_left
  · apply pow_le_pow_left₀
    · have hs : Real.sqrt (2 : ℝ) ≤ 3 / 2 := by
        rw [Real.sqrt_le_left (by norm_num)]; norm_num
      exact mul_nonneg (by linarith only [hs]) (sq_nonneg _)
    · exact mul_le_mul_of_nonneg_right endpoint_proxy_le_proxyA (sq_nonneg _)
  · norm_num [GMCExplicitDelta.Contract.ratioC2]

/-- S4: every higher even model moment, with the exact contract constants. -/
theorem source_high_even_moment_ratio {d : ℕ} (M : GMCModel d) (x : Vec d)
    {k : ℕ} (hk : 3 ≤ k) :
    Integrable (fun ω : PotentialSample d => (ω 0 x) ^ (2 * k)) M.P.toMeasure ∧
      ∫ ω, (ω 0 x) ^ (2 * k) ∂M.P.toMeasure ≤
        (GMCExplicitDelta.Contract.ratioC3 : ℝ) * ((2 * k - 1).doubleFactorial : ℝ) *
          ((GMCExplicitDelta.Contract.proxyA : ℝ) * M.delta ^ 2) ^ k := by
  obtain ⟨hi, hb⟩ := source_even_moment_ratio M x (k := k) (by omega)
  rw [ite_eq_right (by omega : k ≠ 2)] at hb
  refine ⟨hi, hb.trans ?_⟩
  apply mul_le_mul_of_nonneg_left
  · apply pow_le_pow_left₀
    · have hs : Real.sqrt (2 : ℝ) ≤ 3 / 2 := by
        rw [Real.sqrt_le_left (by norm_num)]; norm_num
      exact mul_nonneg (by linarith only [hs]) (sq_nonneg _)
    · exact mul_le_mul_of_nonneg_right endpoint_proxy_le_proxyA (sq_nonneg _)
  · have hc : (0 : ℝ) ≤ GMCExplicitDelta.Contract.ratioC3 := by norm_num [GMCExplicitDelta.Contract.ratioC3]
    exact mul_nonneg hc (Nat.cast_nonneg _)

end GMCExplicitDelta.Source
