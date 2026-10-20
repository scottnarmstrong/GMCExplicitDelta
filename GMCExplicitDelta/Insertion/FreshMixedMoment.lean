module

public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! # Mixed spatial moments without spatial independence -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace GMCExplicitDelta.Insertion

/-- The generalized Hölder step in I3: only the common total-order marginal moment
is needed, even when the spatial evaluations have arbitrary dependence. -/
theorem lintegral_prod_pow_le_of_marginal_moments
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (s : Finset ι)
    {X : ι → Ω → ℝ≥0∞} (hX : ∀ i ∈ s, AEMeasurable (X i) μ)
    (n : ι → ℕ) {N : ℕ} (hN : 0 < N) (hn : ∑ i ∈ s, n i = N)
    {B : ℝ≥0∞} (hB : ∀ i ∈ s, ∫⁻ ω, X i ω ^ N ∂μ ≤ B) :
    ∫⁻ ω, ∏ i ∈ s, X i ω ^ n i ∂μ ≤ B := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hsum : ∑ i ∈ s, (n i : ℝ) / N = 1 := by
    rw [← Finset.sum_div, ← Nat.cast_sum, hn, div_self hN0]
  have hp : ∀ i ∈ s, 0 ≤ (n i : ℝ) / N := fun i _ => by positivity
  have hh := ENNReal.lintegral_prod_norm_pow_le s
    (f := fun i ω => X i ω ^ N) (fun i hi => (hX i hi).pow_const N) hsum hp
  have heq (x : ℝ≥0∞) (i : ι) : (x ^ N) ^ ((n i : ℝ) / N) = x ^ n i := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    have he : (N : ℝ) * ((n i : ℝ) / N) = n i := by field_simp
    rw [he, ENNReal.rpow_natCast]
  simp only [heq] at hh
  refine hh.trans ?_
  calc
    _ ≤ ∏ i ∈ s, B ^ ((n i : ℝ) / N) :=
      Finset.prod_le_prod (fun i hi => ENNReal.rpow_le_rpow (hB i hi) (hp i hi))
    _ = B := by
      have hs (t : Finset ι) :
          (∏ i ∈ t, B ^ ((n i : ℝ) / N)) = B ^ (∑ i ∈ t, (n i : ℝ) / N) := by
        classical
        induction t using Finset.induction with
        | empty => simp
        | insert i t hi ih =>
          rw [Finset.prod_insert hi, Finset.sum_insert hi, ih,
            ENNReal.rpow_add_of_nonneg _ _
              (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
              (Finset.sum_nonneg fun j _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
      rw [hs, hsum, ENNReal.rpow_one]

end GMCExplicitDelta.Insertion
