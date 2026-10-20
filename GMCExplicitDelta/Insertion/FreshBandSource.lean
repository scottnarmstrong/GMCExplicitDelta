module

public import GMCExplicitDelta.Source.MomentRatiosModel
public import GMCExplicitDelta.Source.ExpMomentModel
public import GMCExplicitDelta.Source.BandMajorantMoments
public import GMCExplicitDelta.StatementProofs.SourceVariance
public import GMCExplicitDelta.StatementProofs.SourceEvenMoment
public import GMCExplicitDelta.Insertion.FreshBandOperator
public import Mathlib.Probability.IdentDistribIndep

/-! # The band majorant at arbitrary layers and spatial points -/

@[expose] public section

open Homogenization MeasureTheory ProbabilityTheory
open SubdiffusiveProcess.Model SubdiffusiveProcess.Model.PotentialField

namespace GMCExplicitDelta.Insertion

/-- Every layer at every spatial point has the zero-layer origin law. -/
theorem layer_eval_identDistrib {d : ℕ} (M : GMCModel d) (k : ℕ) (x : Vec d) :
    IdentDistrib (fun ω : PotentialSample d => ω k x)
      (fun ω : PotentialSample d => ω 0 0) M.P.toMeasure M.P.toMeasure := by
  have hfield : IdentDistrib (fun ω : PotentialSample d => ω k x)
      (fun g : PotentialField d => g 0) M.P.toMeasure (zeroPotentialLaw M.P).toMeasure := by
    refine ⟨((measurable_eval x).comp (measurable_pi_apply k)).aemeasurable,
      Source.measurable_eval0.aemeasurable, ?_⟩
    calc
      M.P.toMeasure.map (fun ω : PotentialSample d => ω k x) =
          ((potentialMarginalLaw M.P k).toMeasure).map (fun g : PotentialField d => g x) := by
        rw [potentialMarginalLaw, ProbabilityMeasure.toMeasure_map,
          Measure.map_map (measurable_eval x) (measurable_pi_apply k)]
        rfl
      _ = ((zeroPotentialLaw M.P).toMeasure).map
          (fun g : PotentialField d => triadicScale k g x) := by
        rw [M.shellPrefix.marginal_scaling k, ProbabilityMeasure.toMeasure_map,
          Measure.map_map (measurable_eval x) (measurable_triadicScale k)]
        rfl
      _ = ((zeroPotentialLaw M.P).toMeasure).map
          (fun g : PotentialField d => g ((((3 : ℝ) ^ k)⁻¹) • x)) := rfl
      _ = ((zeroPotentialLaw M.P).toMeasure).map (fun g : PotentialField d => g 0) :=
        Source.map_eval_eq (Source.endpointModel_of_gmc M).stat _
  exact hfield.trans (Source.source_eval_identDistrib M 0).symm

/-- Gaussian even moments and their integrability transport to every layer. -/
theorem layer_even_moment {d : ℕ} (M : GMCModel d) (k : ℕ) (x : Vec d) (n : ℕ) :
    Integrable (fun ω : PotentialSample d => (ω k x) ^ (2 * n)) M.P.toMeasure ∧
      ∫ ω, (ω k x) ^ (2 * n) ∂M.P.toMeasure ≤
        ((2 * n - 1).doubleFactorial : ℝ) *
          ((3 - 2 * Real.sqrt 2) / 16 * M.delta ^ 2) ^ n := by
  have hid := (layer_eval_identDistrib M k x).comp (measurable_id.pow_const (2 * n))
  have hb := StatementProofs.source_even_moment (M := M) (x := 0) (k := n)
  exact ⟨hid.integrable_iff.mpr hb.1, hid.integral_eq.trans_le hb.2⟩

/-- Sign symmetry also transports to every layer and point. -/
theorem layer_eval_symm {d : ℕ} (M : GMCModel d) (k : ℕ) (x : Vec d) :
    IdentDistrib (fun ω : PotentialSample d => ω k x)
      (fun ω : PotentialSample d => -(ω k x)) M.P.toMeasure M.P.toMeasure := by
  have hid := layer_eval_identDistrib M k x
  exact hid.trans ((Source.source_eval_symm M 0).trans (hid.comp measurable_neg).symm)

/-- Independence of the one-point layer variables. -/
theorem independent_layer_eval {d : ℕ} (M : GMCModel d) (x : Vec d) :
    iIndepFun (fun k : ℕ => fun ω : PotentialSample d => ω k x) M.P.toMeasure := by
  exact M.shellPrefix.independent.comp (fun _ => fun g : PotentialField d => g x)
    (fun _ => measurable_eval x)

/-- Every finite sum of layers has a symmetric one-point law. -/
theorem layer_sum_symm {d : ℕ} (M : GMCModel d) (I : Finset ℕ) (x : Vec d) :
    IdentDistrib (fun ω : PotentialSample d => ∑ k ∈ I, ω k x)
      (fun ω : PotentialSample d => -(∑ k ∈ I, ω k x)) M.P.toMeasure M.P.toMeasure := by
  have hind := independent_layer_eval M x
  have hp := IdentDistrib.pi (fun k => layer_eval_symm M k x) hind
    (hind.comp (fun _ => fun t : ℝ => -t) (fun _ => measurable_neg))
  have hm : Measurable (fun f : ℕ → ℝ => ∑ k ∈ I, f k) :=
    Finset.measurable_sum I (fun k _ => measurable_pi_apply k)
  simpa only [Function.comp_def, Finset.sum_neg_distrib] using hp.comp hm

/-- The one-band even majorant is the rescaled contract series. -/
theorem bandEvenMajorant_eq_rescale (δ : ℝ) :
    Source.bandEvenMajorant Contract.proxyA Contract.varU (δ ^ 2)
        Contract.ratioC2 Contract.ratioC3 =
      PowerSeries.rescale (δ ^ 2 / 2) Contract.bandSeries := by
  ext n
  simp only [Source.bandEvenMajorant, Contract.bandSeries, PowerSeries.coeff_mk,
    PowerSeries.coeff_rescale]
  split_ifs with hn0 hn1 hn2
  · subst n; norm_num
  · subst n; norm_num; ring
  · subst n; ring
  · ring

/-- S9 instantiated for any finite set of model layers at a fixed spatial point. -/
theorem layer_sum_band_moments {d : ℕ} (M : GMCModel d) (I : Finset ℕ) (x : Vec d) :
    (∀ n : ℕ, Integrable (fun ω : PotentialSample d => (∑ k ∈ I, ω k x) ^ n) M.P.toMeasure) ∧
    (∀ n : ℕ, ∫ ω : PotentialSample d, (∑ k ∈ I, ω k x) ^ (2 * n) ∂M.P.toMeasure ≤
      ((2 * n).factorial : ℝ) * (M.delta ^ 2) ^ n *
        PowerSeries.coeff n (Contract.bandSeries ^ I.card) / 2 ^ n) := by
  have hvar (k : ℕ) : ∫ ω : PotentialSample d, (ω k x) ^ 2 ∂M.P.toMeasure ≤
      (Contract.varU : ℝ) * M.delta ^ 2 := by
    have hid := (layer_eval_identDistrib M k x).comp (measurable_id.pow_const 2)
    refine hid.integral_eq.trans_le ?_
    have hv := (StatementProofs.source_variance (M := M) (x := 0)).2
    have hv' : ∫ ω : PotentialSample d, (ω 0 0) ^ 2 ∂M.P.toMeasure ≤
        Source.sourceVarianceTrue * M.delta ^ 2 := by
      convert hv using 1
      unfold Source.sourceVarianceTrue
      ring
    exact hv'.trans (mul_le_mul_of_nonneg_right
      (Source.sourceVarianceTrue_le.trans (by norm_num [Contract.varU])) (sq_nonneg _))
  have hfour (k : ℕ) : ∫ ω : PotentialSample d, (ω k x) ^ 4 ∂M.P.toMeasure ≤
      (Contract.ratioC2 : ℝ) * 3 * ((Contract.proxyA : ℝ) * M.delta ^ 2) ^ 2 := by
    have hid := (layer_eval_identDistrib M k x).comp (measurable_id.pow_const 4)
    exact hid.integral_eq.trans_le (Source.source_fourth_moment_ratio M 0).2
  have hhigh (k n : ℕ) (hn : 3 ≤ n) :
      ∫ ω : PotentialSample d, (ω k x) ^ (2 * n) ∂M.P.toMeasure ≤
        (Contract.ratioC3 : ℝ) * ((2 * n - 1).doubleFactorial : ℝ) *
          ((Contract.proxyA : ℝ) * M.delta ^ 2) ^ n := by
    have hid := (layer_eval_identDistrib M k x).comp (measurable_id.pow_const (2 * n))
    exact hid.integral_eq.trans_le (Source.source_high_even_moment_ratio M 0 hn).2
  have hb := Source.independent_sum_moment_majorant I
    (fun k : ℕ => fun ω : PotentialSample d => ω k x)
    (fun k => (measurable_eval x).comp (measurable_pi_apply k))
    (independent_layer_eval M x) (fun k => layer_eval_symm M k x)
    (fun k n => (layer_even_moment M k x n).1)
    (by norm_num [Contract.proxyA]) (by norm_num [Contract.varU]) (sq_nonneg M.delta)
    (by norm_num [Contract.ratioC2]) (by norm_num [Contract.ratioC3]) hvar hfour hhigh
  refine ⟨hb.1, fun n => (hb.2.2 n).trans_eq ?_⟩
  rw [Source.bandMajorant_pow_even_coeff, bandEvenMajorant_eq_rescale,
    ← map_pow, PowerSeries.coeff_rescale]
  rw [div_pow]
  ring

/-- The factorial band majorant is dominated by the corresponding Gaussian moments. -/
theorem layer_sum_gaussian_moments {d : ℕ} (M : GMCModel d) (I : Finset ℕ)
    (x : Vec d) (n : ℕ) :
    ∫ ω : PotentialSample d, (∑ k ∈ I, ω k x) ^ (2 * n) ∂M.P.toMeasure ≤
      ((2 * n - 1).doubleFactorial : ℝ) *
        ((I.card : ℝ) * Contract.proxyA * M.delta ^ 2) ^ n := by
  have hb := (layer_sum_band_moments M I x).2 n
  have hc := (Contract.bandSeries_pow_coeff_bounds I.card n).2
  calc
    _ ≤ ((2 * n).factorial : ℝ) * (M.delta ^ 2) ^ n *
        (((I.card : ℝ) * Contract.proxyA) ^ n / n.factorial) / 2 ^ n := by
      exact hb.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hc (by positivity)) (by positivity))
    _ = _ := by
      rw [Source.factorial_two_mul_eq]
      push_cast
      have hf : (n.factorial : ℝ) ≠ 0 := by positivity
      have ht : (2 : ℝ) ^ n ≠ 0 := by positivity
      field_simp
      ring

end GMCExplicitDelta.Insertion
