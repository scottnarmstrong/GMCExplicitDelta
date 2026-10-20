module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-! Orthogonal low-mode patterns on the nine children of a planar cube. -/

@[expose] public section

namespace GMCExplicitDelta.Localization

/-- The centered first sine pattern. -/
def planarBlock_axisOdd (i : Fin 3) : ℝ := if i = 1 then 2 else -1

/-- The second sine pattern, also the first cosine pattern. -/
def planarBlock_axisEven (i : Fin 3) : ℝ := if i = 0 then 1 else if i = 1 then 0 else -1

/-- The first sine pattern before centering. -/
def planarBlock_sinePattern (i : Fin 3) : ℝ := if i = 1 then 2 else 1

/-- Finite Bessel inequality for the three mutually orthogonal low-mode patterns. -/
theorem planarBlock_nine_cell_bessel (h : Fin 3 → Fin 3 → ℝ) :
    (∑ i, ∑ j, h i j * planarBlock_axisOdd i) ^ 2 / 18 +
      (∑ i, ∑ j, h i j * planarBlock_axisEven i) ^ 2 / 6 +
      (∑ i, ∑ j, h i j * (planarBlock_sinePattern i * planarBlock_axisEven j)) ^ 2 / 12 ≤
      ∑ i, ∑ j, (h i j) ^ 2 := by
  let A := ∑ i, ∑ j, h i j * planarBlock_axisOdd i
  let B := ∑ i, ∑ j, h i j * planarBlock_axisEven i
  let C := ∑ i, ∑ j, h i j * (planarBlock_sinePattern i * planarBlock_axisEven j)
  have hpos : 0 ≤ ∑ i, ∑ j,
      (h i j - A / 18 * planarBlock_axisOdd i - B / 6 * planarBlock_axisEven i -
        C / 12 * (planarBlock_sinePattern i * planarBlock_axisEven j)) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have heq : (∑ i, ∑ j,
      (h i j - A / 18 * planarBlock_axisOdd i - B / 6 * planarBlock_axisEven i -
        C / 12 * (planarBlock_sinePattern i * planarBlock_axisEven j)) ^ 2) =
      (∑ i, ∑ j, (h i j) ^ 2) - A ^ 2 / 18 - B ^ 2 / 6 - C ^ 2 / 12 := by
    dsimp [A, B, C]
    simp only [Fin.sum_univ_succ, Fin.isValue,
      planarBlock_axisOdd, planarBlock_axisEven, planarBlock_sinePattern]
    norm_num
    ring
  rw [heq] at hpos
  change A ^ 2 / 18 + B ^ 2 / 6 + C ^ 2 / 12 ≤ _
  linarith only [hpos]

/-- The exceptional spectral weights are controlled by the mixed-mode weight. -/
theorem planarBlock_weighted_bessel {A B C S r : ℝ}
    (hB : A ^ 2 / 18 + B ^ 2 / 6 + C ^ 2 / 12 ≤ S) (hr : r ≤ 16) :
    2 / 405 * r * A ^ 2 + 1 / 160 * r * B ^ 2 + 9 / 40 * C ^ 2 ≤
      27 / 10 * S := by
  have hA : 2 / 405 * r * A ^ 2 ≤ 3 / 20 * A ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg A)
    linarith only [hr]
  have hV : 1 / 160 * r * B ^ 2 ≤ 9 / 20 * B ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg B)
    linarith only [hr]
  linarith only [hA, hV, hB]

end GMCExplicitDelta.Localization
