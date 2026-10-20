module

public import GMCExplicitDelta.Proofs.FineSensitivity.Remainder
public import GMCExplicitDelta.Proofs.FineSensitivity.JointRatio
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Measurability in the fresh sample, with the old coefficient fixed -/

@[expose] public section

open MeasureTheory Homogenization Homogenization.Book.Ch02 Matrix
open SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab (ScalarCoeffOnData)
open scoped Matrix.Norms.Elementwise

namespace GMCExplicitDelta.Assembly

noncomputable local instance fineRemainderMeasContinuousENorm {n : ℕ} : ContinuousENorm (Matrix (Fin n) (Fin n) ℝ) :=
  SeminormedAddGroup.toContinuousENorm

local instance fineRemainderMeasPseudoMetrizableSpace {n : ℕ} : TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin n) (Fin n) ℝ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin n → Fin n → ℝ))

local instance fineRemainderMeasSecondCountableTopology {n : ℕ} : SecondCountableTopology (Matrix (Fin n) (Fin n) ℝ) :=
  inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℝ))

local instance fineRemainderMeasBorelSpace {n : ℕ} : BorelSpace (Matrix (Fin n) (Fin n) ℝ) :=
  inferInstanceAs (BorelSpace (Fin n → Fin n → ℝ))

local instance fineRemainderMeasMeasurableAdd {n : ℕ} : MeasurableAdd₂ (Mat n) :=
  inferInstanceAs (MeasurableAdd₂ (Fin n → Fin n → ℝ))

local instance fineRemainderMeasMeasurableSub {n : ℕ} : MeasurableSub₂ (Mat n) :=
  inferInstanceAs (MeasurableSub₂ (Fin n → Fin n → ℝ))

/-- Measurable parameter-dependent weights can be integrated against a fixed Gram field. -/
theorem measurable_fineWeightedGram {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] {d : ℕ} (ν : Measure E) [SFinite ν]
    {w : Ω → E → ℝ} (hw : Measurable (Function.uncurry w))
    {G : E → Mat d} (hG : Measurable G) :
    Measurable (fun ω => fineWeightedGram ν (w ω) G) := by
  have h : Measurable (fun p : Ω × E => w p.1 p.2 • ((G p.2)ᵀ * G p.2)) := by
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    change Measurable (fun p : Ω × E => w p.1 p.2 * ∑ l, G p.2 l i * G p.2 l j)
    exact hw.mul (Finset.measurable_sum _ (fun l _ =>
      (((measurable_pi_apply i).comp ((measurable_pi_apply l).comp hG)).comp measurable_snd).mul
      (((measurable_pi_apply j).comp ((measurable_pi_apply l).comp hG)).comp measurable_snd)))
  have hi : StronglyMeasurable (fun ω => fineWeightedGram ν (w ω) G) :=
    h.stronglyMeasurable.integral_prod_right'
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  exact (((continuous_apply j).comp (continuous_apply i)).comp_stronglyMeasurable hi).measurable

theorem measurable_fineRemainderMatrix {d : ℕ} {U : Domain d} {a : Vec d → ℝ}
    (h : ScalarCoeffOnData U a) (ha : Measurable a)
    (M : GMCModel d) {k L : ℕ} (hkL : k ≤ L) (η : ℝ) :
    Measurable (fun ω => fineRemainderMatrix h (cutoffRatio M k L ω) η) := by
  have hr := measurable_cutoffRatio_uncurry M hkL
  have h₁ : Measurable (fun p : PotentialSample d × Vec d =>
      a p.2 * ((cutoffRatio M k L p.1 p.2 - 1)^2/(8*η))) :=
    (ha.comp measurable_snd).mul (((hr.sub measurable_const).pow_const 2).div_const _)
  have h₂ : Measurable (fun p : PotentialSample d × Vec d =>
      a p.2 * ((cutoffRatio M k L p.1 p.2 + (cutoffRatio M k L p.1 p.2)⁻¹ - 2)/2)) :=
    (ha.comp measurable_snd).mul (((hr.add hr.inv).sub measurable_const).div_const _)
  exact (measurable_fineWeightedGram _ h₁
    ((measurable_fineGradientMatrix h.toCoeffOn false).sub
      (measurable_fineGradientMatrix h.toCoeffOn true))).add
    (measurable_fineWeightedGram _ h₂ (measurable_fineGradientMatrix h.toCoeffOn true))

end GMCExplicitDelta.Assembly
