module

public import GMCExplicitDelta.Insertion.FreshFunctionalBinomial

/-! # Scalar factors in the formal binomial moment expansion -/

@[expose] public section

open scoped ENNReal

namespace GMCExplicitDelta.Insertion

/-- Expand a deterministic old value and both deterministic weight masses. -/
theorem coefficientFunctional_const_add_pow_mul (B : ℕ → ℝ≥0∞)
    {f g : PowerSeries ℝ} (hf : ∀ n, 0 ≤ PowerSeries.coeff n f)
    (hg : ∀ n, 0 ≤ PowerSeries.coeff n g) {a v z : ℝ}
    (ha : 0 ≤ a) (hv : 0 ≤ v) (hz : 0 ≤ z) (p l : ℕ) :
    coefficientFunctional B ((PowerSeries.C a + PowerSeries.C v * f) ^ p *
      (PowerSeries.C z * g) ^ l) = ∑ k ∈ Finset.range (p + 1),
      ENNReal.ofReal (a ^ (p - k) * (p.choose k : ℝ) * v ^ k * z ^ l) *
        coefficientFunctional B (f ^ k * g ^ l) := by
  let c (k : ℕ) : ℝ := a ^ (p - k) * (p.choose k : ℝ) * v ^ k * z ^ l
  have hc (k : ℕ) : 0 ≤ c k := by
    dsimp only [c]
    positivity
  have heq : (PowerSeries.C a + PowerSeries.C v * f) ^ p * (PowerSeries.C z * g) ^ l =
      ∑ k ∈ Finset.range (p + 1), PowerSeries.C (c k) * (f ^ k * g ^ l) := by
    rw [add_comm (PowerSeries.C a) (PowerSeries.C v * f), add_pow, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    dsimp only [c]
    simp only [mul_pow, map_mul, map_pow, map_natCast]
    ring
  rw [heq, coefficientFunctional_sum _ _ _ (fun k _ n => ?_)]
  · apply Finset.sum_congr rfl
    intro k _
    exact coefficientFunctional_C_mul B (hc k) _
  · rw [PowerSeries.coeff_C_mul]
    exact mul_nonneg (hc _) (Source.coeff_mul_nonneg
      (Source.coeff_pow_nonneg hf _) (Source.coeff_pow_nonneg hg _) _)

end GMCExplicitDelta.Insertion
