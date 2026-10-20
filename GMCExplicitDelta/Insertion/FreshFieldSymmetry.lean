module

public import SubdiffusiveProcess.CoarseGrainingVocab.ReciprocalLowerSupport

/-! # Whole-field sign symmetry for the conditional competitor expansion -/

@[expose] public section

open MeasureTheory Homogenization SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab

namespace GMCExplicitDelta.Insertion

/-- Odd measurable functionals of the fresh sample have zero expectation. This
uses the whole-field law, so it also applies to products of spatial integrals. -/
theorem integral_odd_field_functional_eq_zero {d : ℕ} (M : GMCModel d)
    {F : PotentialSample d → ℝ} (hF : AEStronglyMeasurable F M.P.toMeasure)
    (hodd : ∀ ω, F (negatePotentialSequence ω) = -F ω) :
    ∫ ω, F ω ∂M.P.toMeasure = 0 := by
  have he := integral_comp_eq_of_map_eq measurable_negatePotentialSequence
    (potentialSequenceLaw_negation M) F hF
  simp only [hodd, integral_neg] at he
  linarith only [he]

/-- An even functional times an odd power of an odd functional is killed by
whole-field symmetry, independently of correlations between spatial points. -/
theorem integral_even_mul_odd_pow_eq_zero {d : ℕ} (M : GMCModel d)
    {E O : PotentialSample d → ℝ} (k l : ℕ)
    (hE : Measurable E) (hO : Measurable O)
    (heven : ∀ ω, E (negatePotentialSequence ω) = E ω)
    (hodd : ∀ ω, O (negatePotentialSequence ω) = -O ω) :
    ∫ ω, E ω ^ k * O ω ^ (2 * l + 1) ∂M.P.toMeasure = 0 := by
  apply integral_odd_field_functional_eq_zero M
    ((hE.pow_const k).mul (hO.pow_const _)).aestronglyMeasurable
  intro ω
  change E (negatePotentialSequence ω) ^ k * O (negatePotentialSequence ω) ^ (2 * l + 1) =
    -(E ω ^ k * O ω ^ (2 * l + 1))
  rw [heven, hodd, Odd.neg_pow (odd_two_mul_add_one l), mul_neg]

end GMCExplicitDelta.Insertion
