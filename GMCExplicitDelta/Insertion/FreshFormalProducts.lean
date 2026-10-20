module

public import GMCExplicitDelta.Insertion.FreshFormalPositive
public import GMCExplicitDelta.Insertion.FreshCoefficientProducts

/-! # Sparse hyperbolic products under a positive monomial functional -/

@[expose] public section

open scoped ENNReal

namespace GMCExplicitDelta.Insertion

/-- Insert one odd sine or one even cosh increment into a Taylor product. -/
theorem coefficientFunctional_hyperbolic_mul (B : ℕ → ℝ≥0∞) {g : PowerSeries ℝ}
    (hg : ∀ n, 0 ≤ PowerSeries.coeff n g) {p : ℕ} (hp : p = 1 ∨ p = 2) :
    coefficientFunctional B ((if p = 1 then formalSinh else formalCosh - 1) * g) =
      ∑' n : ℕ, ENNReal.ofReal (((2 * n + p).factorial : ℝ)⁻¹) *
        coefficientFunctional (fun m => B (2 * n + p + m)) g := by
  rcases hp with rfl | rfl
  · rw [ite_eq_left rfl, coefficientFunctional_mul B formalSinh_coeff_nonneg hg]
    change coefficientFunctional (fun n => coefficientFunctional (fun m => B (n + m)) g)
      formalSinh = _
    exact coefficientFunctional_formalSinh _
  · rw [ite_eq_right (by decide : (2 : ℕ) ≠ 1),
      coefficientFunctional_mul B formalCosh_sub_one_coeff_nonneg hg]
    change coefficientFunctional (fun n => coefficientFunctional (fun m => B (n + m)) g)
      (formalCosh - 1) = _
    simpa only [Nat.mul_add, Nat.mul_one] using coefficientFunctional_formalCosh_sub_one
      (fun n => coefficientFunctional (fun m => B (n + m)) g)

/-- The sparse multi-index formula matches exactly the spatial hyperbolic product bound. -/
theorem coefficientFunctional_fin_hyperbolic (B : ℕ → ℝ≥0∞) (k : ℕ)
    (p : Fin k → ℕ) (hp : ∀ i, p i = 1 ∨ p i = 2) :
    coefficientFunctional B (∏ i : Fin k, if p i = 1 then formalSinh else formalCosh - 1) =
      ∑' n : Fin k → ℕ,
        (∏ i : Fin k, ENNReal.ofReal (((2 * n i + p i).factorial : ℝ)⁻¹)) *
          B (∑ i : Fin k, (2 * n i + p i)) := by
  induction k generalizing B with
  | zero => simp [coefficientFunctional, PowerSeries.coeff_one, apply_ite]
  | succ k ih =>
    have htail (i : Fin k) (n : ℕ) :
        0 ≤ PowerSeries.coeff n (if p i.succ = 1 then formalSinh else formalCosh - 1) := by
      split
      · exact formalSinh_coeff_nonneg n
      · exact formalCosh_sub_one_coeff_nonneg n
    rw [Fin.prod_univ_succ, coefficientFunctional_hyperbolic_mul B
      (coeff_fin_product_nonneg k _ htail) (hp 0)]
    have hi (n : ℕ) := ih (fun m => B (2 * n + p 0 + m))
      (fun i => p i.succ) (fun i => hp i.succ)
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
