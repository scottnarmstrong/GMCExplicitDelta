module

public import GMCExplicitDelta.Assembly.ModelInduction
public import GMCExplicitDelta.Insertion.FreshAffine
public import GMCExplicitDelta.Insertion.FreshCoshMoment
public import GMCExplicitDelta.Insertion.FreshBandSource
public import GMCExplicitDelta.Insertion.FreshExponential
public import GMCExplicitDelta.Insertion.FreshSpatialMoment
public import Homogenization.Geometry.BoundedConvexDomain

/-! # The affine seed and its band-moment estimate (K1–K2) -/

@[expose] public section

open scoped ENNReal
open MeasureTheory hiding average
open Homogenization Homogenization.Book.Ch02
open SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab (normalizedDefect ahom aCutoffCoeffOnData paperENNRealLpNorm)

namespace GMCExplicitDelta.Assembly

variable {d : ℕ}

/-- Normalized volume on a Chapter 2 domain. -/
noncomputable abbrev domainProbability (U : Domain d) : Measure (Vec d) :=
  (U.isDomain.toBoundedMeasurableDomain U.nonempty).normalizedVolume

instance domainProbability_isProbabilityMeasure (U : Domain d) :
    IsProbabilityMeasure (domainProbability U) :=
  ⟨(U.isDomain.toBoundedMeasurableDomain U.nonempty).normalizedVolume_apply_univ⟩

/-- The Chapter 2 average is integration against normalized volume. -/
theorem average_eq_integral_domainProbability (U : Domain d) (f : Vec d → ℝ) :
    average U f = ∫ x, f x ∂domainProbability U := by
  rw [domainProbability, BoundedMeasurableDomain.normalizedVolume, integral_smul_measure,
    ENNReal.toReal_inv]
  rfl

/-- A continuous function is integrable on a bounded domain, also for normalized volume. -/
theorem integrable_domainProbability_of_continuous {U : Domain d} {f : Vec d → ℝ}
    (hf : Continuous f) : Integrable f (domainProbability U) := by
  have hc : IsCompact (closure (U : Set (Vec d))) :=
    U.isBoundedDomain.isBounded.isCompact_closure
  have hi : IntegrableOn f (closure (U : Set (Vec d))) volume :=
    hf.continuousOn.integrableOn_compact hc
  exact (U.isDomain.toBoundedMeasurableDomain U.nonempty).integrable_normalizedVolume
    f (hi.mono_set subset_closure)

/-- The literal cutoff has the logarithm used in the affine seed. -/
theorem log_aCutoff_sub_log_ahom (M : GMCModel d) (m : ℕ) (ω : PotentialSample d)
    (x : Vec d) :
    Real.log (aCutoff M m ω x) - Real.log (ahom M m) =
      (∑ k ∈ Finset.range (m + 1), ω k x) - normShift M m := by
  rw [aCutoff, Real.log_exp, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one,
    normShift]
  ring

/-- K1 at the model's actual normalization. -/
theorem normalizedDefect_le_affine {d : ℕ} [NeZero d] (M : GMCModel d) (m : ℕ)
    (U : Domain d) (ω : PotentialSample d) (hpos : 0 < ahom M m) :
    normalizedDefect M m U ω ≤ ENNReal.ofReal (average U
      (fun x => Real.cosh ((∑ k ∈ Finset.range (m + 1), ω k x) - normShift M m) - 1)) := by
  have hb := Insertion.paperScalarProbeMaxOn_le_average_cosh_log_sub
    (aCutoffCoeffOnData M m ω U) hpos
  simpa only [normalizedDefect, log_aCutoff_sub_log_ahom] using hb

/-- Symmetry places the deterministic normalization shift at its nonnegative magnitude. -/
theorem integral_cosh_sub_eq_abs {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Y : Ω → ℝ} (hsym : ProbabilityTheory.IdentDistrib Y (fun ω => -Y ω) μ μ)
    (H : ℝ) :
    (∫ ω, (Real.cosh (Y ω - H) - 1) ^ (32 : ℕ) ∂μ) =
      ∫ ω, (Real.cosh (|H| + Y ω) - 1) ^ (32 : ℕ) ∂μ := by
  rcases le_total 0 H with hH | hH
  · have hm : Measurable (fun y : ℝ => (Real.cosh (y - H) - 1) ^ (32 : ℕ)) :=
      ((measurable_id.sub measurable_const).cosh.sub measurable_const).pow_const 32
    have hi := (hsym.comp hm).integral_eq
    simp only [abs_of_nonneg hH]
    calc
      _ = ∫ ω, (Real.cosh (-Y ω - H) - 1) ^ (32 : ℕ) ∂μ := hi
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        rw [show -Y ω - H = -(H + Y ω) by ring, Real.cosh_neg]
  · simp only [abs_of_nonpos hH]
    apply integral_congr_ae
    filter_upwards [] with ω
    rw [show Y ω - H = -H + Y ω by ring]

/-- The same absolute exponential envelope controls a deterministic shift of the cosh power. -/
theorem integrable_coshPow_shift {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Y : Ω → ℝ} (hY : Measurable Y) (p : ℕ)
    (hexp : Integrable (fun ω => Real.exp (p * |Y ω|)) μ) (H : ℝ) :
    Integrable (fun ω => (Real.cosh (H + Y ω) - 1) ^ p) μ := by
  have hm : Measurable (fun ω => (Real.cosh (H + Y ω) - 1) ^ p) :=
    ((measurable_const.add hY).cosh.sub measurable_const).pow_const p
  apply (hexp.const_mul (Real.exp (p * |H|))).mono' hm.aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_of_nonneg (pow_nonneg (sub_nonneg.mpr (Real.one_le_cosh _)) p),
    ← Real.exp_add]
  calc
    _ = Insertion.coshPow p |H + Y ω| := by simp only [Insertion.coshPow, Real.cosh_abs]
    _ ≤ Real.exp (p * |H + Y ω|) := Insertion.coshPow_le_exp p (abs_nonneg _)
    _ ≤ Real.exp (p * (|H| + |Y ω|)) := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg p)
      simpa only [Real.norm_eq_abs] using norm_add_le H (Y ω)
    _ = _ := by congr 1; ring

/-- Joint continuity of a layer evaluation in the sample and spatial point. -/
theorem continuous_layer_eval_pair (k : ℕ) :
    Continuous (fun q : PotentialSample d × Vec d => q.1 k q.2) := by
  exact ContinuousEval.continuous_eval.comp
    (((continuous_subtype_val.comp ((continuous_apply k).comp continuous_fst)).fst).prodMk
      continuous_snd)

/-- Swap a jointly measurable curried function, in a context with abstract carriers. -/
theorem measurable_uncurry_of_swapped {Ω S β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace β] (f : Ω → S → β)
    (hf : Measurable (fun q : S × Ω => f q.2 q.1)) :
    Measurable (Function.uncurry f) := by
  exact hf.comp (show Measurable (Prod.swap : Ω × S → S × Ω) from measurable_swap)

/-- K1, Jensen, S9 and I2 give the initial moment at the exact deterministic shift. -/
theorem normalizedDefect_moment_le_band {d : ℕ} [NeZero d] (M : GMCModel d) (m : ℕ)
    (U : Domain d) (hpos : 0 < ahom M m) :
    (∫⁻ ω, (normalizedDefect M m U ω) ^ (32 : ℕ) ∂M.P.toMeasure) ≤
      ENNReal.ofReal (Contract.bandSeriesEval M.delta (m + 1)
        (Real.cosh |normShift M m| - 1)) := by
  let I := Finset.range (m + 1)
  let Y : Vec d → PotentialSample d → ℝ := fun x ω => ∑ k ∈ I, ω k x
  let H := normShift M m
  let ψ : PotentialSample d → Vec d → ℝ := fun ω x => Real.cosh (Y x ω - H) - 1
  have hYm (x : Vec d) : Measurable (Y x) :=
    Finset.measurable_sum I (fun k _ =>
      (PotentialField.measurable_eval x).comp (measurable_pi_apply k))
  have hsym (x : Vec d) := Insertion.layer_sum_symm M I x
  have hexp (x : Vec d) : Integrable (fun ω => Real.exp (32 * |Y x ω|)) M.P.toMeasure :=
    Insertion.integrable_exp_mul_abs_of_gaussian_moments (hYm x) (hsym x)
      (fun n => (Insertion.layer_sum_band_moments M I x).1 (2 * n))
      (fun n => Insertion.layer_sum_gaussian_moments M I x n) 32
  have hpi (x : Vec d) : Integrable (fun ω => ψ ω x ^ 32) M.P.toMeasure := by
    have hi := integrable_coshPow_shift (hYm x) 32 (hexp x) (-H)
    simpa only [ψ, sub_eq_add_neg, add_comm (-H)] using hi
  have hB (x : Vec d) : ∫ ω, ψ ω x ^ 32 ∂M.P.toMeasure ≤
      Contract.bandSeriesEval M.delta (m + 1) (Real.cosh |H| - 1) := by
    change (∫ ω, (Real.cosh (Y x ω - H) - 1) ^ (32 : ℕ) ∂M.P.toMeasure) ≤ _
    rw [integral_cosh_sub_eq_abs (hsym x)]
    apply Insertion.integral_coshPow_le_band (hYm x) (hsym x).map_eq M.delta (m + 1)
      (hexp x) _ (abs_nonneg H)
    intro n
    simpa only [I, Finset.card_range] using (Insertion.layer_sum_band_moments M I x).2 n
  have hcontx (ω : PotentialSample d) : Continuous (ψ ω) := by
    have hs : Continuous (fun x : Vec d => ∑ k ∈ I, ω k x) :=
      continuous_finsetSum I (fun k _ => (ω k).1.1.continuous)
    exact (Real.continuous_cosh.comp (hs.sub continuous_const)).sub continuous_const
  have hswapm : Measurable (fun q : Vec d × PotentialSample d => ψ q.2 q.1) :=
    measurable_uncurry_of_continuous_of_measurable hcontx
      (fun x => ((hYm x).sub measurable_const).cosh.sub measurable_const)
  have hψm : Measurable (Function.uncurry ψ) := measurable_uncurry_of_swapped ψ hswapm
  have hnn (ω : PotentialSample d) (x : Vec d) : 0 ≤ ψ ω x :=
    sub_nonneg.mpr (Real.one_le_cosh _)
  have hj := Insertion.lintegral_pow_spatial_integral_le
    (μ := M.P.toMeasure) (ν := domainProbability U) hψm hnn
    (fun ω => integrable_domainProbability_of_continuous (hcontx ω))
    (fun ω => integrable_domainProbability_of_continuous ((hcontx ω).pow 32)) hpi hB
  refine le_trans (lintegral_mono (fun ω => ?_)) hj
  have ha := normalizedDefect_le_affine M m U ω hpos
  rw [average_eq_integral_domainProbability] at ha
  exact pow_le_pow_left' ha 32

/-- Convert a finite 32nd moment estimate to the paper's literal ENNReal norm. -/
theorem paperENNRealLpNorm_le_of_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ≥0∞) {B : ℝ} (hB : 0 ≤ B)
    (hm : (∫⁻ ω, X ω ^ (32 : ℕ) ∂μ) ≤ ENNReal.ofReal B) :
    paperENNRealLpNorm μ 32 X ≤ ENNReal.ofReal (B ^ ((1 : ℝ) / 32)) := by
  unfold paperENNRealLpNorm
  change (∫⁻ ω, X ω ^ ((32 : ℕ) : ℝ) ∂μ) ^ ((32 : ℝ)⁻¹) ≤ _
  have hr := ENNReal.rpow_le_rpow hm (show (0 : ℝ) ≤ 1 / 32 by norm_num)
  rw [ENNReal.ofReal_rpow_of_nonneg hB (by norm_num)] at hr
  simpa only [ENNReal.rpow_natCast, one_div] using hr

/-- The K2 moment estimate expressed as the paper's norm. -/
theorem normalizedDefect_norm_le_band {d : ℕ} [NeZero d] (M : GMCModel d) (m : ℕ)
    (U : Domain d) (hpos : 0 < ahom M m) :
    paperENNRealLpNorm M.P.toMeasure 32 (normalizedDefect M m U) ≤
      ENNReal.ofReal ((Contract.bandSeriesEval M.delta (m + 1)
        (Real.cosh |normShift M m| - 1)) ^ ((1 : ℝ) / 32)) := by
  apply paperENNRealLpNorm_le_of_moment
  · apply tsum_nonneg
    intro n
    exact mul_nonneg
      (mul_nonneg (pow_nonneg (sq_nonneg _) _) (Contract.bandSeries_pow_coeff_bounds _ _).1)
      (Insertion.coshL_pow_eval_nonneg n 32 (sub_nonneg.mpr (Real.one_le_cosh _)))
  · exact normalizedDefect_moment_le_band M m U hpos

end GMCExplicitDelta.Assembly
