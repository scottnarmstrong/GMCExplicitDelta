module

public import GMCExplicitDelta.Insertion.FreshBandProducts
public import GMCExplicitDelta.Insertion.FreshCoshSeries

/-! # Hyperbolic spatial products controlled by S9 -/

@[expose] public section

open MeasureTheory Homogenization SubdiffusiveProcess.Model
open scoped ENNReal

namespace GMCExplicitDelta.Insertion

/-- Simultaneous hyperbolic factors at arbitrary spatial points are controlled
by the even band-moment functional. The parity condition is exactly the even
number of odd factors surviving whole-field sign symmetry. -/
theorem layer_sum_hyperbolic_product_moment_le {d : ℕ} (M : GMCModel d)
    (I : Finset ℕ) (k : ℕ) (x : Fin k → Vec d) (p : Fin k → ℕ)
    (hp : ∀ i, p i = 1 ∨ p i = 2) (heven : Even (∑ i : Fin k, p i)) :
    (∫⁻ ω : PotentialSample d, ∏ i : Fin k,
      ENNReal.ofReal (if p i = 1 then |Real.sinh (∑ j ∈ I, ω j (x i))|
        else Real.cosh (∑ j ∈ I, ω j (x i)) - 1) ∂M.P.toMeasure) ≤
      ∑' n : Fin k → ℕ,
        (∏ i : Fin k, ENNReal.ofReal (((2 * n i + p i).factorial : ℝ)⁻¹)) *
          bandMomentFunctional M.delta I.card (∑ i : Fin k, (2 * n i + p i)) := by
  have hr (i : Fin k) (t : ℝ) :
      ENNReal.ofReal (if p i = 1 then |Real.sinh t| else Real.cosh t - 1) =
      ∑' n : ℕ, ENNReal.ofReal (((2 * n + p i).factorial : ℝ)⁻¹) *
        ENNReal.ofReal |t| ^ (2 * n + p i) := by
    rcases hp i with hi | hi
    · rw [hi, ite_eq_left rfl]
      exact ofReal_abs_sinh_eq_tsum t
    · rw [hi, ite_eq_right (by decide : (2 : ℕ) ≠ 1)]
      simpa only [Nat.mul_add, Nat.mul_one] using ofReal_cosh_sub_one_eq_tsum t
  have hdeg (n : Fin k → ℕ) : Even (∑ i : Fin k, (2 * n i + p i)) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    exact (even_two_mul _).add heven
  have hb := layer_sum_product_series_moment_le M I k x
    (fun i n => ENNReal.ofReal (((2 * n + p i).factorial : ℝ)⁻¹))
    (fun i n => 2 * n + p i) hdeg
  refine le_trans (le_of_eq (lintegral_congr fun ω => ?_)) hb
  apply Finset.prod_congr rfl
  intro i _
  exact hr i _

end GMCExplicitDelta.Insertion
