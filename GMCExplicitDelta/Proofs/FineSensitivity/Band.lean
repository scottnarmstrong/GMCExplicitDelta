module

public import GMCExplicitDelta.Proofs.FineSensitivity.SubGaussian
public import GMCExplicitDelta.Proofs.FineSensitivity.Ratio
public import GMCExplicitDelta.Source.MomentRatiosModel

/-! # Model-level sub-Gaussian bounds for fresh bands -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open SubdiffusiveProcess.Model
open scoped NNReal

namespace GMCExplicitDelta.Assembly

variable {d : ℕ}

/-- The nonnegative contract proxy for one layer. -/
noncomputable def fineSourceProxy (M : GMCModel d) : ℝ≥0 :=
  ⟨(Contract.proxyA : ℝ) * M.delta ^ 2, mul_nonneg (by norm_num [Contract.proxyA]) (sq_nonneg _)⟩

/-- The all-even source theorem supplies S8's exact sub-Gaussian parameter. -/
theorem fine_source_hasSubgaussianMGF (M : GMCModel d) (x : Homogenization.Vec d) :
    HasSubgaussianMGF (fun ω : PotentialSample d => ω 0 x) (fineSourceProxy M) M.P.toMeasure := by
  apply fine_hasSubgaussianMGF_of_even (Source.source_eval_symm M x)
    (fun k => (Source.source_even_moment M x k).1)
  intro k
  refine (Source.source_even_moment M x k).2.trans ?_
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply pow_le_pow_left₀
  · have hs : Real.sqrt (2 : ℝ) ≤ 3 / 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    exact mul_nonneg (by linarith only [hs]) (sq_nonneg _)
  · exact mul_le_mul_of_nonneg_right Source.endpoint_proxy_le_proxyA (sq_nonneg _)

/-- Exact marginal scaling, evaluated at a point. -/
theorem fine_layer_identDistrib (M : GMCModel d) (i : ℕ) (x : Homogenization.Vec d) :
    IdentDistrib (fun ω : PotentialSample d => ω i x)
      (fun g : PotentialField d => g ((((3 : ℝ) ^ i)⁻¹) • x))
      M.P.toMeasure (zeroPotentialLaw M.P).toMeasure := by
  refine ⟨((PotentialField.measurable_eval x).comp (measurable_pi_apply i)).aemeasurable,
    (PotentialField.measurable_eval _).aemeasurable, ?_⟩
  change M.P.toMeasure.map ((fun g : PotentialField d => g x) ∘
    (fun ω : PotentialSample d => ω i)) = _
  rw [← Measure.map_map (PotentialField.measurable_eval x) (measurable_pi_apply i)]
  change ((potentialMarginalLaw M.P i).toMeasure).map (fun g : PotentialField d => g x) = _
  rw [M.shellPrefix.marginal_scaling i, ProbabilityMeasure.toMeasure_map,
    Measure.map_map (PotentialField.measurable_eval x)
      (PotentialField.continuous_triadicScale i).measurable]
  rfl

/-- Every layer, at every point, has the same sub-Gaussian proxy. -/
theorem fine_layer_hasSubgaussianMGF (M : GMCModel d) (i : ℕ) (x : Homogenization.Vec d) :
    HasSubgaussianMGF (fun ω : PotentialSample d => ω i x) (fineSourceProxy M) M.P.toMeasure := by
  let y : Homogenization.Vec d := (((3 : ℝ) ^ i)⁻¹) • x
  have hzero : IdentDistrib (fun g : PotentialField d => g y)
      (fun g : PotentialField d => g 0) (zeroPotentialLaw M.P).toMeasure
        (zeroPotentialLaw M.P).toMeasure := by
    refine ⟨(PotentialField.measurable_eval y).aemeasurable,
      (PotentialField.measurable_eval 0).aemeasurable, ?_⟩
    exact Source.map_eval_eq (Source.endpointModel_of_gmc M).stat y
  exact (fine_source_hasSubgaussianMGF M 0).congr_identDistrib
    ((Source.source_eval_identDistrib M 0).trans
      ((fine_layer_identDistrib M i x).trans hzero).symm)

/-- Independence of the layers adds their sub-Gaussian proxies exactly. -/
theorem fine_band_hasSubgaussianMGF (M : GMCModel d) (k L : ℕ) (x : Homogenization.Vec d) :
    HasSubgaussianMGF (fun ω : PotentialSample d => fineBand k L ω x)
      ((L - k) • fineSourceProxy M) M.P.toMeasure := by
  have hind : iIndepFun (fun i : ℕ => fun ω : PotentialSample d => ω i x) M.P.toMeasure :=
    M.shellPrefix.independent.comp (fun _ => fun g : PotentialField d => g x)
      (fun _ => PotentialField.measurable_eval x)
  have h := HasSubgaussianMGF.sum_of_iIndepFun hind
    (s := Finset.Ioc k L) (fun i _ => fine_layer_hasSubgaussianMGF M i x)
  simpa only [fineBand, Finset.sum_const, Nat.card_Ioc] using h

end GMCExplicitDelta.Assembly
