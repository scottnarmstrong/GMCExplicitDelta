module

public import GMCExplicitDelta.Insertion.FreshMixedMoment
public import GMCExplicitDelta.Insertion.FreshPositiveSeries
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-! # Termwise comparison of nonnegative spatial Taylor expansions -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace GMCExplicitDelta.Insertion

/-- Apply the common marginal-moment majorant to a nonnegative Taylor expansion.
Only indices with nonzero coefficient need a marginal bound; this retains the
parity restriction in the even/odd competitor expansion. -/
theorem lintegral_tsum_monomials_le {Ω J : Type*} [MeasurableSpace Ω] [Countable J]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (k : ℕ)
    {X : Fin k → Ω → ℝ≥0∞} (hX : ∀ i, AEMeasurable (X i) μ)
    (A : J → ℝ≥0∞) (powers : J → Fin k → ℕ) (B : ℕ → ℝ≥0∞) (hB0 : B 0 = 1)
    (hB : ∀ n : J, A n ≠ 0 → ∀ i : Fin k,
      ∫⁻ ω, X i ω ^ (∑ j : Fin k, powers n j) ∂μ ≤ B (∑ j : Fin k, powers n j)) :
    (∫⁻ ω, ∑' n : J, A n * ∏ i : Fin k, X i ω ^ powers n i ∂μ) ≤
      ∑' n : J, A n * B (∑ i : Fin k, powers n i) := by
  have hm (n : J) : AEMeasurable (fun ω => ∏ i : Fin k, X i ω ^ powers n i) μ := by
    simpa only [Finset.prod_fn] using
      Finset.aemeasurable_prod Finset.univ (fun i _ => (hX i).pow_const (powers n i))
  rw [lintegral_tsum (fun n => (hm n).const_mul (A n))]
  apply ENNReal.tsum_le_tsum
  intro n
  by_cases ha : A n = 0
  · simp only [ha, zero_mul, lintegral_zero, le_refl]
  rw [lintegral_const_mul'' (A n) (hm n)]
  apply mul_le_mul_right
  by_cases hn : (∑ i : Fin k, powers n i) = 0
  · have hz : ∀ i, powers n i = 0 := by
      simpa only [Finset.sum_eq_zero_iff, Finset.mem_univ, forall_true_left] using hn
    simp only [hz, pow_zero, Finset.prod_const_one, lintegral_const, measure_univ,
      mul_one, Finset.sum_const_zero, hB0, le_refl]
  · exact lintegral_prod_pow_le_of_marginal_moments Finset.univ
      (fun i _ => hX i) (powers n) (Nat.pos_of_ne_zero hn) rfl (fun i _ => hB n ha i)

end GMCExplicitDelta.Insertion
