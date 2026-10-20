module

public import GMCExplicitDelta.Source.ExpMomentSeries
public import GMCExplicitDelta.Source.ExpMomentNumerics
public import GMCExplicitDelta.Source.EndpointStripSource

/-! # The first source exponential moment, conditional on the sharp variance bound -/

@[expose] public section

namespace GMCExplicitDelta.Source

open Homogenization MeasureTheory ProbabilityTheory Real
open SubdiffusiveProcess.Model SubdiffusiveProcess.Model.PotentialField

/-- A point in the zero layer has the same law as evaluation at the origin under the field law. -/
theorem source_eval_identDistrib {d : ℕ} (M : GMCModel d) (x : Vec d) :
    IdentDistrib (fun ω : PotentialSample d => ω 0 x) (fun g : PotentialField d => g 0)
      M.P.toMeasure (zeroPotentialLaw M.P).toMeasure := by
  have hE := endpointModel_of_gmc M
  refine ⟨((measurable_eval x).comp (measurable_pi_apply 0)).aemeasurable,
    measurable_eval0.aemeasurable, ?_⟩
  change M.P.toMeasure.map (fun ω : PotentialSample d => ω 0 x) =
    lawZero (zeroPotentialLaw M.P).toMeasure
  rw [← map_eval_eq hE.stat x]
  rw [zeroPotentialLaw, potentialMarginalLaw, ProbabilityMeasure.toMeasure_map,
    Measure.map_map (measurable_eval x) (measurable_pi_apply 0)]
  rfl

/-- Sign symmetry of the source at every point. -/
theorem source_eval_symm {d : ℕ} (M : GMCModel d) (x : Vec d) :
    IdentDistrib (fun ω : PotentialSample d => ω 0 x) (fun ω : PotentialSample d => -(ω 0 x))
      M.P.toMeasure M.P.toMeasure := by
  have hE := endpointModel_of_gmc M
  have hX : Measurable (fun ω : PotentialSample d => ω 0 x) :=
    (measurable_eval x).comp (measurable_pi_apply 0)
  have hID := source_eval_identDistrib M x
  have hlaw : M.P.toMeasure.map (fun ω : PotentialSample d => ω 0 x) =
      lawZero (zeroPotentialLaw M.P).toMeasure := hID.map_eq
  refine ⟨hX.aemeasurable, hX.neg.aemeasurable, ?_⟩
  calc
    _ = lawZero (zeroPotentialLaw M.P).toMeasure := hID.map_eq
    _ = (lawZero (zeroPotentialLaw M.P).toMeasure).map (fun y : ℝ => -y) :=
      (lawZero_neg hE.neg).symm
    _ = _ := by rw [← hlaw, Measure.map_map measurable_neg hX]; rfl

/-- S7: exactly the frozen exponential-moment conjuncts, with the variance estimate as an input.
It does not import the statements of the variance or exponential-moment theorems. -/
theorem exp_moment_of_variance {d : ℕ} (M : GMCModel d) (x : Vec d)
    (hvar : ∫ ω : PotentialSample d, (ω 0 x) ^ 2 ∂M.P.toMeasure ≤
      sourceVarianceTrue * M.delta ^ 2) :
    Integrable (fun ω : PotentialSample d => exp (ω 0 x)) M.P.toMeasure ∧
    Integrable (fun ω : PotentialSample d => exp (-(ω 0 x))) M.P.toMeasure ∧
    (∫ ω, exp (ω 0 x) ∂M.P.toMeasure ≤ 1 + 1816027 / 1000000000 * M.delta ^ 2) ∧
    (∫ ω, exp (-(ω 0 x)) ∂M.P.toMeasure ≤ 1 + 1816027 / 1000000000 * M.delta ^ 2) ∧
    tauSq M.P ≤ 1816027 / 1000000000 * M.delta ^ 2 := by
  have hID := source_eval_identDistrib M x
  have hsym := source_eval_symm M x
  have hint : Integrable (fun ω : PotentialSample d => exp (ω 0 x)) M.P.toMeasure :=
    (hID.comp measurable_exp).symm.integrable_snd M.G4.exponential_integrable
  have hneg := (hsym.comp measurable_exp).integrable_snd hint
  have ha : 0 ≤ sourceProxyTrue := by
    unfold sourceProxyTrue
    have h := GMCNumerics.sqrt_two_enclosure.2
    linarith only [h]
  have hs : M.delta ^ 2 ≤ 1 / 4 := by
    calc
      _ ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ M.shellPrefix.delta_pos.le M.shellPrefix.delta_le_half 2
      _ = _ := by norm_num
  have hb := integral_exp_le_of_even_moments hsym (fun k => (source_even_moment M x k).1)
    ha (sq_nonneg _) hs (fun k => (source_even_moment M x k).2) hvar
  have hbκ : ∫ ω : PotentialSample d, exp (ω 0 x) ∂M.P.toMeasure ≤
      1 + (GMCExplicitDelta.Contract.kappaQ1 : ℝ) * M.delta ^ 2 := by
    calc
      _ ≤ 1 + M.delta ^ 2 * (sourceVarianceTrue / 2 +
          4 * (exp (sourceProxyTrue / 8) - 1 - sourceProxyTrue / 8)) := hb
      _ ≤ 1 + M.delta ^ 2 * (GMCExplicitDelta.Contract.kappaQ1 : ℝ) :=
        add_le_add_right (mul_le_mul_of_nonneg_left source_exp_constant_le_kappa (sq_nonneg _)) 1
      _ = _ := by ring
  have hbLit : ∫ ω : PotentialSample d, exp (ω 0 x) ∂M.P.toMeasure ≤
      1 + 1816027 / 1000000000 * M.delta ^ 2 := by
    simpa only [GMCExplicitDelta.Contract.kappaQ1, Rat.cast_div, Rat.cast_ofNat] using hbκ
  refine ⟨hint, hneg, hbLit, ?_, ?_⟩
  · rw [← integral_exp_eq_neg_of_symm hsym]
    exact hbLit
  · have heq : (∫ ω : PotentialSample d, exp (ω 0 x) ∂M.P.toMeasure) =
        ∫ g : PotentialField d, exp (g 0) ∂(zeroPotentialLaw M.P).toMeasure := by
      simpa only [Function.comp_def] using (hID.comp measurable_exp).integral_eq
    unfold tauSq
    rw [← heq]
    have hl := log_le_sub_one_of_pos (integral_exp_pos hint)
    linarith only [hl, hbLit]

end GMCExplicitDelta.Source
