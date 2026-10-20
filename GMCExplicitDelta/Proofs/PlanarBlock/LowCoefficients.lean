module

public import GMCExplicitDelta.Proofs.PlanarBlock.NineCell
public import Mathlib.Analysis.Real.Pi.Bounds

/-! The finite weighted low-mode bound for a mean-zero nine-cell scalar field. -/

@[expose] public section

open Real

namespace GMCExplicitDelta.Localization

/-- Mean zero centers the first sine pattern. -/
theorem planarBlock_center_sinePattern (h : Fin 3 → Fin 3 → ℝ)
    (hm : (∑ i, ∑ j, h i j) = 0) :
    (∑ i, ∑ j, h i j * planarBlock_sinePattern i) =
      (∑ i, ∑ j, h i j * planarBlock_axisOdd i) / 3 := by
  have hid : (∑ i, ∑ j, h i j * planarBlock_sinePattern i) =
      (∑ i, ∑ j, h i j * planarBlock_axisOdd i) / 3 +
        4 / 3 * (∑ i, ∑ j, h i j) := by
    simp only [Fin.sum_univ_succ, Fin.isValue, planarBlock_sinePattern, planarBlock_axisOdd]
    norm_num
    ring
  rw [hid, hm, mul_zero, add_zero]

/-- All exceptional-mode corrections fit under the mixed-mode constant. -/
theorem planarBlock_low_coefficient_bound (h : Fin 3 → Fin 3 → ℝ)
    (hm : (∑ i, ∑ j, h i j) = 0) :
    8 / (5 * π ^ 2) *
        ((∑ i, ∑ j, h i j * planarBlock_sinePattern i) / (6 * π)) ^ 2 +
      1 / (10 * π ^ 2) *
        ((∑ i, ∑ j, h i j * planarBlock_axisEven i) / (4 * π)) ^ 2 +
      6 / (5 * π ^ 2) *
        (√3 / (4 * π ^ 2) *
          (∑ i, ∑ j, h i j * (planarBlock_sinePattern i * planarBlock_axisEven j))) ^ 2 ≤
      243 / (10 * π ^ 6) * (1 / 9 * ∑ i, ∑ j, h i j ^ 2) := by
  rw [planarBlock_center_sinePattern h hm]
  let A := ∑ i, ∑ j, h i j * planarBlock_axisOdd i
  let B := ∑ i, ∑ j, h i j * planarBlock_axisEven i
  let C := ∑ i, ∑ j, h i j * (planarBlock_sinePattern i * planarBlock_axisEven j)
  let S := ∑ i, ∑ j, h i j ^ 2
  have hpi : π ^ 2 ≤ 16 := by nlinarith only [Real.pi_pos, Real.pi_lt_four]
  have hbound := planarBlock_weighted_bessel (planarBlock_nine_cell_bessel h) hpi
  change 8 / (5 * π ^ 2) * (A / 3 / (6 * π)) ^ 2 +
    1 / (10 * π ^ 2) * (B / (4 * π)) ^ 2 +
    6 / (5 * π ^ 2) * (√3 / (4 * π ^ 2) * C) ^ 2 ≤
    243 / (10 * π ^ 6) * (1 / 9 * S)
  change 2 / 405 * π ^ 2 * A ^ 2 + 1 / 160 * π ^ 2 * B ^ 2 + 9 / 40 * C ^ 2 ≤
    27 / 10 * S at hbound
  clear_value A B C S
  apply (mul_le_mul_iff_right₀ (pow_pos Real.pi_pos 6)).mp
  have hsqrt : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [mul_pow, div_pow, hsqrt]
  convert hbound using 1 <;> field_simp [Real.pi_ne_zero] <;> ring

end GMCExplicitDelta.Localization
