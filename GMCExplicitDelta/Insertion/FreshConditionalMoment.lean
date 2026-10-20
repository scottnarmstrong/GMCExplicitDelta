module

public import GMCExplicitDelta.Insertion.FreshNonnegativeBinomial
public import GMCExplicitDelta.Insertion.FreshMomentExpand
public import GMCExplicitDelta.Insertion.FreshReferenceExpansion

/-! # Assemble the conditional scalar competitor moment from its mixed terms -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace GMCExplicitDelta.Insertion

/-- Symmetrization, deterministic-weight mixed moments and the exact formal
reference expansion give the sharp conditional band moment. -/
theorem lintegral_competitor_moment_le_band {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {τ : Ω → Ω} (hτ : MeasurePreserving τ μ μ) (δ : ℝ) (h : ℕ)
    {j : ℝ} (hj : 0 ≤ j) {E O : Ω → ℝ} (hE : Measurable E) (hO : Measurable O)
    (hE0 : ∀ ω, 0 ≤ E ω) (hEe : ∀ ω, E (τ ω) = E ω) (hOo : ∀ ω, O (τ ω) = -O ω)
    (hmixed : ∀ k l : ℕ, Even l →
      (∫⁻ ω, ENNReal.ofReal (E ω) ^ k * ENNReal.ofReal |O ω| ^ l ∂μ) ≤
        ENNReal.ofReal ((j + 1) ^ k * Real.sqrt (j * (j + 2)) ^ l) *
          bandMomentApply δ h ((formalCosh - 1) ^ k * formalSinh ^ l)) :
    (∫⁻ ω, ENNReal.ofReal ((j + E ω + O ω) ^ (32 : ℕ)) ∂μ) ≤
      ENNReal.ofReal (Contract.bandSeriesEval δ h j) := by
  have hY : Measurable (fun ω => ENNReal.ofReal |O ω|) :=
    (continuous_abs.measurable.comp hO).ennreal_ofReal
  have hinner (l : ℕ) (hl : Even l) :
      (∫⁻ ω, ENNReal.ofReal (j + E ω) ^ (32 - l) * ENNReal.ofReal |O ω| ^ l ∂μ) ≤
      ∑ k ∈ Finset.range (32 - l + 1),
        ENNReal.ofReal (j ^ (32 - l - k) * (Nat.choose (32 - l) k : ℝ) *
          (j + 1) ^ k * Real.sqrt (j * (j + 2)) ^ l) *
            bandMomentApply δ h ((formalCosh - 1) ^ k * formalSinh ^ l) := by
    calc
      _ = ∫⁻ ω, (ENNReal.ofReal j + ENNReal.ofReal (E ω)) ^ (32 - l) *
          ENNReal.ofReal |O ω| ^ l ∂μ := by
        apply lintegral_congr
        intro ω
        rw [ENNReal.ofReal_add hj (hE0 ω)]
      _ = _ := lintegral_const_add_pow_mul hE.ennreal_ofReal hY _ _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro k _
        refine (mul_le_mul_right (hmixed k l hl) _).trans_eq ?_
        rw [← mul_assoc]
        congr 1
        rw [← ENNReal.ofReal_pow hj, ← ENNReal.ofReal_natCast (Nat.choose (32 - l) k),
          ← ENNReal.ofReal_mul (pow_nonneg hj _),
          ← ENNReal.ofReal_mul (mul_nonneg (pow_nonneg hj _) (Nat.cast_nonneg _))]
        congr 1
        ring
  have hs := lintegral_pow_eq_even_binomial hτ (hE.const_add j) hO
    (fun ω => by rw [hEe ω]) hOo (by decide : Even (32 : ℕ))
  rw [hs, lintegral_even_binomial_sum (hE.const_add j) hO
    (fun ω => add_nonneg hj (hE0 ω)) 32, bandSeriesEval_eq_even_double_sum δ h hj]
  apply Finset.sum_le_sum
  intro l _
  by_cases hl : Even l
  · simp only [ite_eq_left hl]
    exact mul_le_mul_right (hinner l hl) _
  · simp only [ite_eq_right hl, le_refl]

end GMCExplicitDelta.Insertion
