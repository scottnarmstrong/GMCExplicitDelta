module

public import GMCExplicitDelta.Insertion.FreshCoefficientFunctional

/-! # Coefficients of finite products under a positive moment functional -/

@[expose] public section

open scoped ENNReal

namespace GMCExplicitDelta.Insertion

/-- A finite product preserves coefficientwise nonnegativity. -/
theorem coeff_fin_product_nonneg (k : ℕ) (f : Fin k → PowerSeries ℝ)
    (hf : ∀ i n, 0 ≤ PowerSeries.coeff n (f i)) (n : ℕ) :
    0 ≤ PowerSeries.coeff n (∏ i : Fin k, f i) := by
  induction k generalizing n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty, PowerSeries.coeff_one]
    split_ifs <;> norm_num
  | succ k ih =>
    rw [Fin.prod_univ_succ]
    exact Source.coeff_mul_nonneg (hf 0) (fun m => ih (fun i => f i.succ) (fun i => hf i.succ) m) n

/-- The coefficient functional of a finite product is a single sum over all
Taylor multi-indices, weighted by total degree. -/
theorem coefficientFunctional_fin_product (B : ℕ → ℝ≥0∞) (k : ℕ)
    (f : Fin k → PowerSeries ℝ) (hf : ∀ i n, 0 ≤ PowerSeries.coeff n (f i)) :
    coefficientFunctional B (∏ i : Fin k, f i) =
      ∑' n : Fin k → ℕ, (∏ i : Fin k, ENNReal.ofReal (PowerSeries.coeff (n i) (f i))) *
        B (∑ i : Fin k, n i) := by
  induction k generalizing B with
  | zero => simp [coefficientFunctional, PowerSeries.coeff_one, apply_ite]
  | succ k ih =>
    rw [Fin.prod_univ_succ, coefficientFunctional_mul B (hf 0)
      (coeff_fin_product_nonneg k (fun i => f i.succ) (fun i => hf i.succ))]
    have hi (n : ℕ) := ih (fun m => B (n + m)) (fun i => f i.succ) (fun i => hf i.succ)
    simp_rw [hi]
    rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => ℕ)).tsum_eq]
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.sum_univ_succ,
      Fin.cons_zero, Fin.cons_succ]
    rw [ENNReal.tsum_prod']
    apply tsum_congr
    intro n
    rw [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro m
    exact (mul_assoc _ _ _).symm

end GMCExplicitDelta.Insertion
