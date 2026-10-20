module

public import GMCExplicitDelta.Coarse.CompetitorsScalar
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # The pointwise Cauchy–Schwarz bound for the odd competitor weight -/

@[expose] public section

open Homogenization Matrix

namespace GMCExplicitDelta.Insertion

/-- The difference of the two energy densities is bounded by the geometric mean
of the sum and difference gradient energies. -/
theorem abs_energy_difference_le {d : ℕ} (v u : Vec d) {a : ℝ} (ha : 0 ≤ a) :
    |a * (vecNormSq v - vecNormSq u) / 2| ≤
      Real.sqrt (a * vecNormSq (v + u) / 2) *
        Real.sqrt (a * vecNormSq (v - u) / 2) := by
  have hcs : vecDot (v + u) (v - u) ^ 2 ≤
      vecNormSq (v + u) * vecNormSq (v - u) := by
    simpa only [vecDot, vecNormSq, pow_two] using
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (v + u) (v - u)
  have hd : vecDot (v + u) (v - u) = vecNormSq v - vecNormSq u := by
    change (v + u) ⬝ᵥ (v - u) = v ⬝ᵥ v - u ⬝ᵥ u
    rw [add_dotProduct, dotProduct_sub, dotProduct_sub, dotProduct_comm u v]
    ring
  rw [hd] at hcs
  rw [← Real.sqrt_mul (div_nonneg (mul_nonneg ha (vecNormSq_nonneg _)) (by norm_num))]
  apply Real.le_sqrt_of_sq_le
  rw [sq_abs]
  calc
    _ = (a / 2) ^ 2 * (vecNormSq v - vecNormSq u) ^ 2 := by ring
    _ ≤ (a / 2) ^ 2 * (vecNormSq (v + u) * vecNormSq (v - u)) :=
      mul_le_mul_of_nonneg_left hcs (sq_nonneg (a / 2))
    _ = _ := by ring

end GMCExplicitDelta.Insertion
