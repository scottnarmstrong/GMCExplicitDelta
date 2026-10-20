module

public import GMCExplicitDelta.Insertion.FreshWeightBound
public import GMCExplicitDelta.Insertion.FreshDeterministicTransferAE

/-! # The conditional transfer applied to the actual old maximizer weights -/

@[expose] public section

open MeasureTheory hiding average
open Homogenization Homogenization.Book.Ch02
open SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab (ScalarCoeffOnData)
open Matrix
open scoped ENNReal

namespace GMCExplicitDelta.Insertion

/-- The nonnegative even energy density of two old gradients. -/
noncomputable def competitorEvenWeight {d : ℕ} (a : Vec d → ℝ) (v u : Vec d → Vec d) : Vec d → ℝ :=
  fun x => a x * (vecNormSq (v x) + vecNormSq (u x)) / 2

/-- The signed odd energy density of two old gradients. -/
noncomputable def competitorOddWeight {d : ℕ} (a : Vec d → ℝ) (v u : Vec d → Vec d) : Vec d → ℝ :=
  fun x => a x * (vecNormSq (v x) - vecNormSq (u x)) / 2

theorem integrable_competitorEvenWeight {d : ℕ} {U : Domain d} {a : Vec d → ℝ}
    (h : ScalarCoeffOnData U a) (i : Fin d) {v u : Vec d → Vec d}
    (hv : GradMemL2On (U : Set (Vec d)) v) (hu : GradMemL2On (U : Set (Vec d)) u) :
    Integrable (competitorEvenWeight a v u) (volumeMeasureOn (U : Set (Vec d))) := by
  have hi := ((Coarse.integrable_energy h i hv).add (Coarse.integrable_energy h i hu)).div_const 2
  change Integrable (fun x => (a x * vecDot (v x) (v x) + a x * vecDot (u x) (u x)) / 2)
    (volumeMeasureOn (U : Set (Vec d))) at hi
  convert hi using 1
  funext x
  unfold competitorEvenWeight vecNormSq
  ring

theorem integrable_competitorOddWeight {d : ℕ} {U : Domain d} {a : Vec d → ℝ}
    (h : ScalarCoeffOnData U a) (i : Fin d) {v u : Vec d → Vec d}
    (hv : GradMemL2On (U : Set (Vec d)) v) (hu : GradMemL2On (U : Set (Vec d)) u) :
    Integrable (competitorOddWeight a v u) (volumeMeasureOn (U : Set (Vec d))) := by
  have hi := ((Coarse.integrable_energy h i hv).sub (Coarse.integrable_energy h i hu)).div_const 2
  change Integrable (fun x => (a x * vecDot (v x) (v x) - a x * vecDot (u x) (u x)) / 2)
    (volumeMeasureOn (U : Set (Vec d))) at hi
  convert hi using 1
  funext x
  unfold competitorOddWeight vecNormSq
  ring

/-- I3 for the old C12 maximizers, with all deterministic weight assumptions proved. -/
theorem old_competitor_weighted_moment {d : ℕ} (M : GMCModel d) (I : Finset ℕ)
    {U : Domain d} {a : Vec d → ℝ} (h : ScalarCoeffOnData U a)
    {e : Vec d} (he : e ⬝ᵥ e = 1) {v u : Solution U h.toCoeffOn}
    (hv : IsResponseMaximizer U h.toCoeffOn e 0 v)
    (hu : IsResponseMaximizer U h.toCoeffOn 0 e u) :
    (∫⁻ ω : PotentialSample d, ENNReal.ofReal ((responseJ U h.toCoeffOn e e +
      freshEvenEnergy I (Assembly.domainProbability U)
        (competitorEvenWeight a v.toH1.grad u.toH1.grad) ω +
      freshOddEnergy I (Assembly.domainProbability U)
        (competitorOddWeight a v.toH1.grad u.toH1.grad) ω) ^ (32 : ℕ)) ∂M.P.toMeasure) ≤
      ENNReal.ofReal (Contract.bandSeriesEval M.delta I.card (responseJ U h.toCoeffOn e e)) := by
  obtain ⟨i⟩ := Coarse.nonempty_fin_of_dot_one he
  have hiw := (U.isDomain.toBoundedMeasurableDomain U.nonempty).integrable_normalizedVolume _
    (integrable_competitorEvenWeight h i v.toH1.gradMemL2 u.toH1.gradMemL2)
  have hiz := (U.isDomain.toBoundedMeasurableDomain U.nonempty).integrable_normalizedVolume _
    (integrable_competitorOddWeight h i v.toH1.gradMemL2 u.toH1.gradMemL2)
  have hw0 : ∀ᵐ x ∂Assembly.domainProbability U,
      0 ≤ competitorEvenWeight a v.toH1.grad u.toH1.grad x := by
    apply Measure.ae_smul_measure
    filter_upwards [Coarse.a_pos_ae h] with x hx
    exact div_nonneg (mul_nonneg hx.le (add_nonneg (vecNormSq_nonneg _) (vecNormSq_nonneg _)))
      (by norm_num)
  have hwM : (∫ x, competitorEvenWeight a v.toH1.grad u.toH1.grad x
      ∂Assembly.domainProbability U) = responseJ U h.toCoeffOn e e + 1 := by
    rw [← Assembly.average_eq_integral_domainProbability]
    exact average_old_even_weight h he hv hu
  have hzM : (∫ x, |competitorOddWeight a v.toH1.grad u.toH1.grad x|
      ∂Assembly.domainProbability U) ≤
      Real.sqrt (responseJ U h.toCoeffOn e e * (responseJ U h.toCoeffOn e e + 2)) := by
    rw [← Assembly.average_eq_integral_domainProbability]
    exact average_abs_old_odd_weight h he hv hu
  exact deterministic_weight_moment_transfer_ae M I hiw hiz hw0
    (responseJ_nonneg U h.toCoeffOn e e) hwM hzM

end GMCExplicitDelta.Insertion
