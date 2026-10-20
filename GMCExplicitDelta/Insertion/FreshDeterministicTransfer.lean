module

public import GMCExplicitDelta.Insertion.FreshConditionalMoment
public import GMCExplicitDelta.Insertion.FreshMixedWeights
public import GMCExplicitDelta.Insertion.FreshFieldSymmetry

/-! # I3 for deterministic old spatial weights and the actual fresh field -/

@[expose] public section

open MeasureTheory Homogenization SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab (negatePotentialSequence
  measurable_negatePotentialSequence potentialSequenceLaw_negation)
open scoped ENNReal

namespace GMCExplicitDelta.Insertion

/-- The even increment in the old competitor. -/
noncomputable def freshEvenEnergy {d : ℕ} (I : Finset ℕ) (ν : Measure (Vec d))
    (w : Vec d → ℝ) (ω : PotentialSample d) : ℝ :=
  ∫ x, w x * (Real.cosh (∑ k ∈ I, ω k x) - 1) ∂ν

/-- The odd increment in the old competitor. -/
noncomputable def freshOddEnergy {d : ℕ} (I : Finset ℕ) (ν : Measure (Vec d))
    (z : Vec d → ℝ) (ω : PotentialSample d) : ℝ :=
  ∫ x, z x * Real.sinh (∑ k ∈ I, ω k x) ∂ν

/-- The sharp conditional transfer for deterministic old weights. Its weight
hypotheses are exactly the masses and nonnegativity established by I1. -/
theorem deterministic_weight_moment_transfer {d : ℕ} (M : GMCModel d) (I : Finset ℕ)
    {ν : Measure (Vec d)} [SigmaFinite ν] {w z : Vec d → ℝ}
    (hw : Measurable w) (hz : Measurable z) (hw0 : ∀ x, 0 ≤ w x)
    (hiw : Integrable w ν) (hiz : Integrable z ν) {j : ℝ} (hj : 0 ≤ j)
    (hwmass : ∫ x, w x ∂ν = j + 1)
    (hzmass : ∫ x, |z x| ∂ν ≤ Real.sqrt (j * (j + 2))) :
    (∫⁻ ω : PotentialSample d, ENNReal.ofReal
      ((j + freshEvenEnergy I ν w ω + freshOddEnergy I ν z ω) ^ (32 : ℕ)) ∂M.P.toMeasure) ≤
      ENNReal.ofReal (Contract.bandSeriesEval M.delta I.card j) := by
  have hT := measurable_layer_sum_uncurry (d := d) I
  have hE : Measurable (freshEvenEnergy I ν w) := by
    have hm : StronglyMeasurable (fun q : PotentialSample d × Vec d =>
        w q.2 * (Real.cosh (∑ k ∈ I, q.1 k q.2) - 1)) :=
      ((hw.comp measurable_snd).mul (hT.cosh.sub measurable_const)).stronglyMeasurable
    exact hm.integral_prod_right'.measurable
  have hO : Measurable (freshOddEnergy I ν z) := by
    have hm : StronglyMeasurable (fun q : PotentialSample d × Vec d =>
        z q.2 * Real.sinh (∑ k ∈ I, q.1 k q.2)) :=
      ((hz.comp measurable_snd).mul hT.sinh).stronglyMeasurable
    exact hm.integral_prod_right'.measurable
  have hE0 (ω : PotentialSample d) : 0 ≤ freshEvenEnergy I ν w ω :=
    integral_nonneg fun x => mul_nonneg (hw0 x) (sub_nonneg.mpr (Real.one_le_cosh _))
  have htneg (ω : PotentialSample d) (x : Vec d) :
      (∑ k ∈ I, (negatePotentialSequence ω) k x) = -(∑ k ∈ I, ω k x) := by
    simp only [negatePotentialSequence, PotentialField.negate_apply, Finset.sum_neg_distrib]
  have hEe (ω : PotentialSample d) :
      freshEvenEnergy I ν w (negatePotentialSequence ω) = freshEvenEnergy I ν w ω := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      dsimp only
      rw [htneg ω x, Real.cosh_neg]
  have hOo (ω : PotentialSample d) :
      freshOddEnergy I ν z (negatePotentialSequence ω) = -freshOddEnergy I ν z ω := by
    unfold freshOddEnergy
    rw [← integral_neg]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      dsimp only
      rw [htneg ω x, Real.sinh_neg, mul_neg]
  have hwN : (∫⁻ x, ENNReal.ofReal (w x) ∂ν) = ENNReal.ofReal (j + 1) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hiw (Filter.Eventually.of_forall hw0), hwmass]
  have hzN : (∫⁻ x, ENNReal.ofReal |z x| ∂ν) ≤ ENNReal.ofReal (Real.sqrt (j * (j + 2))) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hiz.abs
      (Filter.Eventually.of_forall fun x => abs_nonneg (z x))]
    exact ENNReal.ofReal_le_ofReal hzmass
  have hEb (ω : PotentialSample d) : ENNReal.ofReal (freshEvenEnergy I ν w ω) ≤
      ∫⁻ x, ENNReal.ofReal (w x) * ENNReal.ofReal (Real.cosh (∑ k ∈ I, ω k x) - 1) ∂ν := by
    have hb := enorm_integral_le_lintegral_enorm (μ := ν)
      (fun x => w x * (Real.cosh (∑ k ∈ I, ω k x) - 1))
    change ‖freshEvenEnergy I ν w ω‖ₑ ≤ _ at hb
    rw [Real.enorm_eq_ofReal (hE0 ω)] at hb
    refine hb.trans_eq (lintegral_congr fun x => ?_)
    rw [Real.enorm_eq_ofReal (mul_nonneg (hw0 x) (sub_nonneg.mpr (Real.one_le_cosh _))),
      ENNReal.ofReal_mul (hw0 x)]
  have hOb (ω : PotentialSample d) : ENNReal.ofReal |freshOddEnergy I ν z ω| ≤
      ∫⁻ x, ENNReal.ofReal |z x| * ENNReal.ofReal |Real.sinh (∑ k ∈ I, ω k x)| ∂ν := by
    have hb := enorm_integral_le_lintegral_enorm (μ := ν)
      (fun x => z x * Real.sinh (∑ k ∈ I, ω k x))
    change ‖freshOddEnergy I ν z ω‖ₑ ≤ _ at hb
    rw [Real.enorm_eq_ofReal_abs] at hb
    refine hb.trans_eq (lintegral_congr fun x => ?_)
    rw [Real.enorm_eq_ofReal_abs, abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
  have hmixed (k l : ℕ) (hl : Even l) :
      (∫⁻ ω : PotentialSample d, ENNReal.ofReal (freshEvenEnergy I ν w ω) ^ k *
        ENNReal.ofReal |freshOddEnergy I ν z ω| ^ l ∂M.P.toMeasure) ≤
      ENNReal.ofReal ((j + 1) ^ k * Real.sqrt (j * (j + 2)) ^ l) *
        bandMomentApply M.delta I.card ((formalCosh - 1) ^ k * formalSinh ^ l) := by
    have hb := weighted_layer_sum_mixed_powers_le M I (ν := ν)
      (fun x => ENNReal.ofReal (w x)) (fun x => ENNReal.ofReal |z x|)
      hw.ennreal_ofReal (continuous_abs.measurable.comp hz).ennreal_ofReal k l hl
    refine (le_trans (lintegral_mono fun ω => ?_) hb).trans ?_
    · exact (mul_le_mul_left (pow_le_pow_left' (hEb ω) k) _).trans
        (mul_le_mul_right (pow_le_pow_left' (hOb ω) l) _)
    · rw [hwN]
      refine (mul_le_mul_left (mul_le_mul_right (pow_le_pow_left' hzN l) _) _).trans_eq ?_
      rw [← ENNReal.ofReal_pow (add_nonneg hj (by norm_num)),
        ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
        ← ENNReal.ofReal_mul (pow_nonneg (add_nonneg hj (by norm_num)) _)]
  exact lintegral_competitor_moment_le_band
    (⟨measurable_negatePotentialSequence, potentialSequenceLaw_negation M⟩)
    M.delta I.card hj hE hO hE0 hEe hOo hmixed

end GMCExplicitDelta.Insertion
