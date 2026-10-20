module

public import GMCExplicitDelta.Insertion.FreshSeriesMoment

/-! # Mixed products of positive Taylor series -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace GMCExplicitDelta.Insertion

/-- Generalized Hölder and Tonelli compare a product of hyperbolic Taylor series
with the common total-degree moment majorant. The degree map permits both even
increments and odd hyperbolic factors without inserting zero coefficients. -/
theorem lintegral_prod_tsum_pow_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (k : ℕ)
    {X : Fin k → Ω → ℝ≥0∞} (hX : ∀ i, AEMeasurable (X i) μ)
    (a : Fin k → ℕ → ℝ≥0∞) (degree : Fin k → ℕ → ℕ)
    (B : ℕ → ℝ≥0∞) (hB0 : B 0 = 1)
    (hB : ∀ n : Fin k → ℕ, (∏ i : Fin k, a i (n i)) ≠ 0 → ∀ i : Fin k,
      ∫⁻ ω, X i ω ^ (∑ j : Fin k, degree j (n j)) ∂μ ≤
        B (∑ j : Fin k, degree j (n j))) :
    (∫⁻ ω, ∏ i : Fin k, ∑' n : ℕ, a i n * X i ω ^ degree i n ∂μ) ≤
      ∑' n : Fin k → ℕ, (∏ i : Fin k, a i (n i)) *
        B (∑ i : Fin k, degree i (n i)) := by
  have heq (ω : Ω) :
      (∏ i : Fin k, ∑' n : ℕ, a i n * X i ω ^ degree i n) =
      ∑' n : Fin k → ℕ, (∏ i : Fin k, a i (n i)) *
        ∏ i : Fin k, X i ω ^ degree i (n i) := by
    rw [← tsum_fin_product]
    apply tsum_congr
    intro n
    exact Finset.prod_mul_distrib
  calc
    _ = ∫⁻ ω, ∑' n : Fin k → ℕ, (∏ i : Fin k, a i (n i)) *
        ∏ i : Fin k, X i ω ^ degree i (n i) ∂μ := lintegral_congr heq
    _ ≤ _ := lintegral_tsum_monomials_le k hX (fun n : Fin k → ℕ => ∏ i : Fin k, a i (n i))
      (fun (n : Fin k → ℕ) (i : Fin k) => degree i (n i)) B hB0 hB

end GMCExplicitDelta.Insertion
