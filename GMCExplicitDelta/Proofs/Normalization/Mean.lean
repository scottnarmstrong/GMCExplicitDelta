module

public import GMCExplicitDelta.Proofs.Normalization.Shift
public import GMCExplicitDelta.Proofs.Normalization.Drift
public import GMCExplicitDelta.Coarse.Affine
public import SubdiffusiveProcess.CoarseGrainingVocab.ReciprocalLowerSupport

/-! # Mean seed from affine trials and exact cutoff expectations -/

@[expose] public section

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta.Assembly

open Contract Coarse

variable {d : ℕ}

/-- Negation of all shells turns the inverse average into a constant times a mean-one average. -/
theorem inverse_cutoff_average_eq (M : SubdiffusiveProcess.Model.GMCModel d) (m : ℕ)
    (U : Ch02.Domain d) (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    Ch02.average U (fun x => (SubdiffusiveProcess.Model.aCutoff M m ω x)⁻¹) =
      Real.exp (2 * (m + 1 : ℝ) * SubdiffusiveProcess.Model.tauSq M.P) *
        Ch02.average U (SubdiffusiveProcess.Model.aCutoff M m (negatePotentialSequence ω)) := by
  have hp : ∀ x, (SubdiffusiveProcess.Model.aCutoff M m ω x)⁻¹ =
      Real.exp (2 * (m + 1 : ℝ) * SubdiffusiveProcess.Model.tauSq M.P) *
        SubdiffusiveProcess.Model.aCutoff M m (negatePotentialSequence ω) x := by
    intro x
    rw [aCutoff_negatePotentialSequence, ← mul_assoc, ← Real.exp_add]
    simp only [show 2 * (m + 1 : ℝ) * SubdiffusiveProcess.Model.tauSq M.P +
      -2 * (m + 1 : ℝ) * SubdiffusiveProcess.Model.tauSq M.P = 0 by ring,
      Real.exp_zero, one_mul]
  simp_rw [hp]
  unfold Ch02.average
  rw [integral_const_mul]
  ring

theorem inverse_cutoff_average_integrable (M : SubdiffusiveProcess.Model.GMCModel d) (m : ℕ)
    (U : Ch02.Domain d) :
    Integrable (fun ω => Ch02.average U
      (fun x => (SubdiffusiveProcess.Model.aCutoff M m ω x)⁻¹)) M.P.toMeasure := by
  have hi : Integrable (fun ω => Ch02.average U (SubdiffusiveProcess.Model.aCutoff M m ω))
      (Measure.map negatePotentialSequence M.P.toMeasure) := by
    rw [potentialSequenceLaw_negation M]
    exact integrable_aCutoff_average M m U
  simpa only [inverse_cutoff_average_eq, Function.comp_def] using
    (hi.comp_measurable measurable_negatePotentialSequence).const_mul
      (Real.exp (2 * (m + 1 : ℝ) * SubdiffusiveProcess.Model.tauSq M.P))

theorem integral_inverse_cutoff_average (M : SubdiffusiveProcess.Model.GMCModel d) (m : ℕ)
    (U : Ch02.Domain d) :
    ∫ ω, Ch02.average U (fun x => (SubdiffusiveProcess.Model.aCutoff M m ω x)⁻¹) ∂M.P.toMeasure =
      Real.exp (2 * (m + 1 : ℝ) * SubdiffusiveProcess.Model.tauSq M.P) := by
  simp_rw [inverse_cutoff_average_eq]
  rw [integral_const_mul, Homogenization.integral_comp_eq_of_map_eq
    measurable_negatePotentialSequence (potentialSequenceLaw_negation M)
    (fun ω => Ch02.average U (SubdiffusiveProcess.Model.aCutoff M m ω))
    (integrable_aCutoff_average M m U).aestronglyMeasurable,
    integral_aCutoff_average, mul_one]

/-- Affine and constant-flux trials, integrated over the cutoff law. -/
theorem frozenJ_mean_le_trial (M : SubdiffusiveProcess.Model.GMCModel d) (m : ℕ)
    (U : Ch02.Domain d) (e : Homogenization.Vec d) (he : vecNormSq e = 1) :
    ∫⁻ ω, ENNReal.ofReal (frozenJ M m U e e ω) ∂M.P.toMeasure ≤
      ENNReal.ofReal (((ahom M m)⁻¹ + ahom M m *
        Real.exp (2 * (m + 1 : ℝ) * SubdiffusiveProcess.Model.tauSq M.P)) / 2 - 1) := by
  let A := fun ω => Ch02.average U (SubdiffusiveProcess.Model.aCutoff M m ω)
  let B := fun ω => Ch02.average U (fun x => (SubdiffusiveProcess.Model.aCutoff M m ω x)⁻¹)
  let f := fun ω => (A ω / ahom M m + ahom M m * B ω) / 2 - 1
  have hiA : Integrable A M.P.toMeasure := integrable_aCutoff_average M m U
  have hiB : Integrable B M.P.toMeasure := inverse_cutoff_average_integrable M m U
  have hi : Integrable f M.P.toMeasure :=
    (((hiA.div_const _).add (hiB.const_mul _)).div_const 2).sub (integrable_const 1)
  have hp : ∀ ω, frozenJ M m U e e ω ≤ f ω := by
    intro ω
    exact normalized_response_le_trial M m U (driftSeed_ahom_pos M m) ω e he
  have hf0 : ∀ ω, 0 ≤ f ω := fun ω =>
    (Ch02.responseJ_nonneg U (aCutoffCoeffOnData M m ω U).toCoeffOn _ _).trans (hp ω)
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal (f ω) ∂M.P.toMeasure :=
      lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hp ω)
    _ = ENNReal.ofReal (∫ ω, f ω ∂M.P.toMeasure) :=
      (ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hf0)).symm
    _ = _ := by
      dsimp [f]
      have hsub := integral_sub
        (((hiA.div_const (ahom M m)).add (hiB.const_mul (ahom M m))).div_const 2)
        (integrable_const (1 : ℝ))
      have hadd := integral_add (hiA.div_const (ahom M m)) (hiB.const_mul (ahom M m))
      simp only [Pi.add_apply] at hsub hadd
      rw [hsub, integral_div, hadd, integral_div, integral_const_mul]
      simp only [A, B, integral_aCutoff_average, integral_inverse_cutoff_average,
        integral_const, probReal_univ, smul_eq_mul, one_mul, one_div]

/-- The deterministic normalization lies in the interval where the affine trial is bounded. -/
theorem frozenJ_mean_le_exp (M : SubdiffusiveProcess.Model.GMCModel d) (m : ℕ)
    (U : Ch02.Domain d) (e : Homogenization.Vec d) (he : vecNormSq e = 1) :
    ∫⁻ ω, ENNReal.ofReal (frozenJ M m U e e ω) ∂M.P.toMeasure ≤
      ENNReal.ofReal ((Real.exp (2 * (m + 1 : ℝ) * SubdiffusiveProcess.Model.tauSq M.P) - 1) / 2) := by
  refine (frozenJ_mean_le_trial M m U e he).trans (ENNReal.ofReal_le_ofReal ?_)
  have ha := driftSeed_ahom_pos M m
  have hb := ahom_le_one M m
  have ht := M.G4.tauSq_pos.le
  have hl := SubdiffusiveProcess.Section5.homogenized_coefficient_reciprocal_lower M m
  have ht0 : 0 ≤ (m + 1 : ℝ) * SubdiffusiveProcess.Model.tauSq M.P := by positivity
  have hl2 : Real.exp (-(2 * (m + 1 : ℝ) * SubdiffusiveProcess.Model.tauSq M.P)) ≤ ahom M m :=
    (Real.exp_le_exp.mpr (by nlinarith)).trans hl
  have hc : 1 ≤ ahom M m * Real.exp (2 * (m + 1 : ℝ) * SubdiffusiveProcess.Model.tauSq M.P) := by
    have hh := mul_le_mul_of_nonneg_right hl2
      (Real.exp_pos (2 * (m + 1 : ℝ) * SubdiffusiveProcess.Model.tauSq M.P)).le
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at hh
    exact hh
  have hh := mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hc)
  have hinv : (ahom M m)⁻¹ * ahom M m = 1 := inv_mul_cancel₀ ha.ne'
  apply (mul_le_mul_iff_right₀ ha).mp
  nlinarith only [hh, hinv]

theorem frozenJ_mean_planar_le_exp (M : SubdiffusiveProcess.Model.GMCModel 2) (m : ℕ)
    (U : Ch02.Domain 2) (e : Homogenization.Vec 2) (he : vecNormSq e = 1) :
    ∫⁻ ω, ENNReal.ofReal (frozenJ M m U e e ω) ∂M.P.toMeasure ≤
      ENNReal.ofReal (Real.exp ((m + 1 : ℝ) * SubdiffusiveProcess.Model.tauSq M.P) - 1) := by
  have ha := ahom_eq_planarLambda_of_streamFunction M m
    planarZeroNormalStreamFunctionOn_openCubeSet_originCube (driftSeed_ahom_pos M m)
  have hh := frozenJ_mean_le_trial M m U e he
  rw [ha, planarLambda] at hh
  have h1 : (Real.exp (-(m + 1 : ℝ) * SubdiffusiveProcess.Model.tauSq M.P))⁻¹ =
      Real.exp ((m + 1 : ℝ) * SubdiffusiveProcess.Model.tauSq M.P) := by
    rw [← Real.exp_neg, neg_mul, neg_neg]
  have h2 : Real.exp (-(m + 1 : ℝ) * SubdiffusiveProcess.Model.tauSq M.P) *
      Real.exp (2 * (m + 1 : ℝ) * SubdiffusiveProcess.Model.tauSq M.P) =
      Real.exp ((m + 1 : ℝ) * SubdiffusiveProcess.Model.tauSq M.P) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h1, h2] at hh
  convert hh using 1
  congr 1
  ring

theorem meanSeed_bound_proof (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (M : SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) (hm : m + 1 ≤ row.h) :
    ∀ n, m ≤ n → ∀ z e : Homogenization.Vec d, vecNormSq e = 1 →
      ∫⁻ ω, ENNReal.ofReal (frozenJ M m (cubeAt z n) e e ω) ∂M.P.toMeasure ≤
        ENNReal.ofReal (row.meanseed M.delta) := by
  intro n _ z e he
  have ht := (StatementProofs.source_exp_moment (M := M) (x := 0)).2.2.2.2
  have ht0 := M.G4.tauSq_pos.le
  have hg : (m + 1 : ℝ) * SubdiffusiveProcess.Model.tauSq M.P ≤ row.gammaH M.delta := by
    have hh : (m + 1 : ℝ) ≤ row.h := by exact_mod_cast hm
    calc
      _ ≤ (row.h : ℝ) * SubdiffusiveProcess.Model.tauSq M.P := mul_le_mul_of_nonneg_right hh ht0
      _ ≤ (row.h : ℝ) * (1816027 / 1000000000 * M.delta ^ 2) :=
        mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg _)
      _ = _ := by unfold Row.gammaH kappaQ1; push_cast; ring
  by_cases hd2 : d = 2
  · subst d
    refine (frozenJ_mean_planar_le_exp M m (cubeAt z n) e he).trans ?_
    apply ENNReal.ofReal_le_ofReal
    change _ ≤ Real.exp (row.gammaH M.delta) - 1
    exact sub_le_sub_right (Real.exp_le_exp.mpr hg) 1
  · refine (frozenJ_mean_le_exp M m (cubeAt z n) e he).trans ?_
    apply ENNReal.ofReal_le_ofReal
    dsimp [Row.meanseed]
    rw [ite_eq_right hd2]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact sub_le_sub_right (Real.exp_le_exp.mpr (by linarith)) 1

end GMCExplicitDelta.Assembly
