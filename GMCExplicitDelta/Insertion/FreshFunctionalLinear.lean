module

public import GMCExplicitDelta.Insertion.FreshCoefficientFunctional

/-! # Positive linearity of the monomial moment functional -/

@[expose] public section

open scoped ENNReal

namespace GMCExplicitDelta.Insertion

/-- Coefficientwise upper bounds are preserved by every nonnegative monomial functional. -/
theorem coefficientFunctional_mono (B : ℕ → ℝ≥0∞) {f g : PowerSeries ℝ}
    (hfg : ∀ n, PowerSeries.coeff n f ≤ PowerSeries.coeff n g) :
    coefficientFunctional B f ≤ coefficientFunctional B g := by
  apply ENNReal.tsum_le_tsum
  intro n
  exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hfg n)) _

theorem coefficientFunctional_add (B : ℕ → ℝ≥0∞) {f g : PowerSeries ℝ}
    (hf : ∀ n, 0 ≤ PowerSeries.coeff n f) (hg : ∀ n, 0 ≤ PowerSeries.coeff n g) :
    coefficientFunctional B (f + g) = coefficientFunctional B f + coefficientFunctional B g := by
  unfold coefficientFunctional
  rw [← ENNReal.tsum_add]
  apply tsum_congr
  intro n
  rw [map_add, ENNReal.ofReal_add (hf n) (hg n), add_mul]

theorem coefficientFunctional_C_mul (B : ℕ → ℝ≥0∞) {c : ℝ} (hc : 0 ≤ c)
    (f : PowerSeries ℝ) :
    coefficientFunctional B (PowerSeries.C c * f) = ENNReal.ofReal c * coefficientFunctional B f := by
  unfold coefficientFunctional
  simp only [PowerSeries.coeff_C_mul, ENNReal.ofReal_mul hc]
  rw [← ENNReal.tsum_mul_left]
  exact tsum_congr fun n => mul_assoc _ _ _

/-- A finite positive polynomial expansion can be evaluated term by term. -/
theorem coefficientFunctional_sum {ι : Type*} (B : ℕ → ℝ≥0∞) (s : Finset ι)
    (f : ι → PowerSeries ℝ) (hf : ∀ i ∈ s, ∀ n, 0 ≤ PowerSeries.coeff n (f i)) :
    coefficientFunctional B (∑ i ∈ s, f i) = ∑ i ∈ s, coefficientFunctional B (f i) := by
  unfold coefficientFunctional
  calc
    _ = ∑' n : ℕ, ∑ i ∈ s, ENNReal.ofReal (PowerSeries.coeff n (f i)) * B n := by
      apply tsum_congr
      intro n
      rw [map_sum, ENNReal.ofReal_sum_of_nonneg (fun i hi => hf i hi n), Finset.sum_mul]
    _ = _ := Summable.tsum_finsetSum (fun i _ => ENNReal.summable)

end GMCExplicitDelta.Insertion
