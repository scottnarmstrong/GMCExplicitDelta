module

public import GMCExplicitDelta.Source.EndpointStripLaw
public import GMCExplicitDelta.Source.MomentBounds
public import SubdiffusiveProcess.Model.GMCModel

/-!
# The all-even source moment bound

`E g₀(x)^{2k} ≤ (2k-1)!! ((3-2√2)/16 δ²)^k`, from the endpoint-strip Hessian argument.
-/

@[expose] public section

namespace GMCExplicitDelta.Source

open Homogenization MeasureTheory ProbabilityTheory
open SubdiffusiveProcess.Model SubdiffusiveProcess.Model.PotentialField

/-- The standing model supplies the hypotheses of the endpoint-strip argument for the law of `g₀`. -/
theorem endpointModel_of_gmc {d : ℕ} (M : GMCModel d) :
    EndpointModel d M.delta (zeroPotentialLaw M.P).toMeasure where
  dim_pos := lt_of_lt_of_le two_pos M.shellPrefix.dimension
  delta_pos := M.shellPrefix.delta_pos
  stat := M.G1.stationary
  neg := congrArg ProbabilityMeasure.toMeasure M.G3.negation
  indep := M.G1.range_dependence
  expSq_int := by
    have key : ∀ g : PotentialField d,
        Real.exp ((M.delta⁻¹ * max (g2Observable g) 0) ^ (2:ℝ)) =
          Real.exp (g2Observable g ^ 2 / M.delta ^ 2) := by
      intro g
      rw [max_eq_left (g2Observable_nonneg g), Real.rpow_two]
      congr 1
      field_simp
    exact M.G2.regularity_expectation.1.congr (Filter.Eventually.of_forall key)
  expSq_le := by
    have key : ∀ g : PotentialField d,
        Real.exp ((M.delta⁻¹ * max (g2Observable g) 0) ^ (2:ℝ)) =
          Real.exp (g2Observable g ^ 2 / M.delta ^ 2) := by
      intro g
      rw [max_eq_left (g2Observable_nonneg g), Real.rpow_two]
      congr 1
      field_simp
    calc ∫ g, Real.exp (g2Observable g ^ 2 / M.delta ^ 2) ∂(zeroPotentialLaw M.P).toMeasure
        = ∫ g, Real.exp ((M.delta⁻¹ * max (g2Observable g) 0) ^ (2:ℝ))
            ∂(zeroPotentialLaw M.P).toMeasure :=
          integral_congr_ae (Filter.Eventually.of_forall fun g => (key g).symm)
      _ ≤ 2 := M.G2.regularity_expectation.2

/-- `(1+K)² (3 - 2√2) = 8`, i.e. `1/(2α) = (3-2√2)/16`. -/
theorem stripAlpha_mul : (1 + stripK) ^ 2 * (3 - 2 * Real.sqrt 2) = 8 := by
  unfold stripK
  have := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  nlinarith

/-- **All-even source moment bound.** -/
theorem source_even_moment {d : ℕ}
    (M : SubdiffusiveProcess.Model.GMCModel d) (x : Homogenization.Vec d) (k : ℕ) :
    MeasureTheory.Integrable (fun ω : SubdiffusiveProcess.Model.PotentialSample d => (ω 0 x) ^ (2 * k))
        M.P.toMeasure ∧
    ∫ ω, (ω 0 x) ^ (2 * k) ∂M.P.toMeasure ≤
      ((2 * k - 1).doubleFactorial : ℝ) * ((3 - 2 * Real.sqrt 2) / 16 * M.delta ^ 2) ^ k := by
  have hE := endpointModel_of_gmc M
  set μ := (zeroPotentialLaw M.P).toMeasure with hμ
  have hδ := M.shellPrefix.delta_pos
  obtain ⟨hint, h1⟩ := hE.nu_exp
  obtain ⟨hx2, h2⟩ := hE.nu_sq
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
  have hmS : AEStronglyMeasurable (fun y : ℝ => y ^ 2)
      (M.P.toMeasure.map (fun ω : PotentialSample d => ω 0 x)) := by
    rw [hlaw]; exact hx2.aestronglyMeasurable
  have hint' : Integrable (fun ω : PotentialSample d =>
      Real.exp ((1 + stripK) ^ 2 * (ω 0 x) ^ 2 / M.delta ^ 2)) M.P.toMeasure := by
    have := (integrable_map_measure hmE hXm.aemeasurable).1 (by rw [hlaw]; exact hint)
    exact this
  have h1' : ∫ ω, Real.exp ((1 + stripK) ^ 2 * (ω 0 x) ^ 2 / M.delta ^ 2) ∂M.P.toMeasure ≤
      Real.sqrt 3 := by
    have := integral_map (μ := M.P.toMeasure) hXm.aemeasurable hmE
    rw [hlaw] at this
    rw [← this]; exact h1
  have h2' : (1 + stripK) ^ 2 * ∫ ω, (ω 0 x) ^ 2 ∂M.P.toMeasure ≤ M.delta ^ 2 / 2 := by
    have := integral_map (μ := M.P.toMeasure) hXm.aemeasurable hmS
    rw [hlaw] at this
    rw [← this]; exact h2
  obtain ⟨hI, hB⟩ := integral_pow_two_mul_le (μ := M.P.toMeasure)
    (X := fun ω : PotentialSample d => ω 0 x) hXm hα hδ hint' h1' h2' k
  refine ⟨hI, hB.trans (le_of_eq ?_)⟩
  have h8 := stripAlpha_mul
  have e : M.delta ^ 2 / (2 * (1 + stripK) ^ 2) = (3 - 2 * Real.sqrt 2) / 16 * M.delta ^ 2 := by
    rw [div_eq_iff (by positivity)]
    linear_combination (-(M.delta ^ 2) / 8) * h8
  rw [e]

end GMCExplicitDelta.Source
