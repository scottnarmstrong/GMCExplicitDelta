module

public import GMCExplicitDelta.Source.BandMajorant
public import GMCExplicitDelta.Insertion.FreshPositiveSeries
public import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-! # Positive coefficient functionals and Cauchy products -/

@[expose] public section

open scoped ENNReal

namespace GMCExplicitDelta.Insertion

/-- An arbitrary nonnegative monomial functional, applied to a real coefficient series. -/
noncomputable def coefficientFunctional (B : ℕ → ℝ≥0∞) (f : PowerSeries ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ, ENNReal.ofReal (PowerSeries.coeff n f) * B n

/-- Tonelli's reindexing of a double sum by total degree. -/
theorem tsum_antidiagonal_ennreal (F : ℕ × ℕ → ℝ≥0∞) :
    (∑' n : ℕ, ∑ p ∈ Finset.antidiagonal n, F p) = ∑' p : ℕ × ℕ, F p := by
  have he (n : ℕ) : (∑ p ∈ Finset.antidiagonal n, F p) =
      ∑' p : ↥(Finset.antidiagonal n), F p := by
    rw [← Finset.sum_attach, Finset.attach_eq_univ]
    exact (tsum_fintype (L := .unconditional _) _).symm
  simp_rw [he]
  rw [← ENNReal.tsum_sigma]
  exact Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq F

/-- Multiplication of positive Taylor series is convolution of monomial moments. -/
theorem coefficientFunctional_mul (B : ℕ → ℝ≥0∞) {f g : PowerSeries ℝ}
    (hf : ∀ n, 0 ≤ PowerSeries.coeff n f) (hg : ∀ n, 0 ≤ PowerSeries.coeff n g) :
    coefficientFunctional B (f * g) = ∑' n : ℕ,
      ENNReal.ofReal (PowerSeries.coeff n f) *
        coefficientFunctional (fun m => B (n + m)) g := by
  let F : ℕ × ℕ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (PowerSeries.coeff p.1 f) * ENNReal.ofReal (PowerSeries.coeff p.2 g) * B (p.1 + p.2)
  have he (n : ℕ) : ENNReal.ofReal (PowerSeries.coeff n (f * g)) * B n =
      ∑ p ∈ Finset.antidiagonal n, F p := by
    rw [PowerSeries.coeff_mul, ENNReal.ofReal_sum_of_nonneg
      (fun p _ => mul_nonneg (hf p.1) (hg p.2)), Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    rw [ENNReal.ofReal_mul (hf p.1)]
    dsimp only [F]
    rw [(Finset.mem_antidiagonal.mp hp)]
  unfold coefficientFunctional
  simp_rw [he]
  rw [tsum_antidiagonal_ennreal, ENNReal.tsum_prod']
  apply tsum_congr
  intro n
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro m
  exact mul_assoc _ _ _

end GMCExplicitDelta.Insertion
