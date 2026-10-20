module

public import GMCExplicitDelta.Proofs.PlanarBlock.CellIntegrals
public import GMCExplicitDelta.Proofs.PlanarBlock.NineCell

/-! Exact normalized third-interval averages, in the integer-pattern notation. -/

@[expose] public section

noncomputable section

open Real

namespace GMCExplicitDelta.Localization

def planarBlock_thirdSin (n : ℤ) (i : Fin 3) : ℝ :=
  3 * ∫ t in (i : ℝ) / 3..((i : ℝ) + 1) / 3, sin (π * n * t)

def planarBlock_thirdCos (n : ℤ) (i : Fin 3) : ℝ :=
  3 * ∫ t in (i : ℝ) / 3..((i : ℝ) + 1) / 3, cos (π * n * t)

theorem planarBlock_thirdCos_zero (i : Fin 3) : planarBlock_thirdCos 0 i = 1 := by
  simp only [planarBlock_thirdCos, Int.cast_zero, mul_zero, zero_mul, cos_zero,
    intervalIntegral.integral_const, smul_eq_mul, mul_one]
  ring

theorem planarBlock_thirdSin_one (i : Fin 3) :
    planarBlock_thirdSin 1 i = 3 / (2 * π) * planarBlock_sinePattern i := by
  simp only [planarBlock_thirdSin, Int.cast_one, mul_one, planarBlock_sin_third, planarBlock_sinePattern]
  split_ifs <;> ring

theorem planarBlock_thirdSin_two (i : Fin 3) :
    planarBlock_thirdSin 2 i = 9 / (4 * π) * planarBlock_axisEven i := by
  have heq : (fun t : ℝ => sin (π * (2 : ℤ) * t)) = fun t => sin (2 * π * t) := by
    funext t
    congr 1
    push_cast
    ring
  rw [planarBlock_thirdSin, heq, planarBlock_sin_two_third]
  unfold planarBlock_axisEven
  split_ifs <;> ring

theorem planarBlock_thirdCos_one (i : Fin 3) :
    planarBlock_thirdCos 1 i = 3 * √3 / (2 * π) * planarBlock_axisEven i := by
  simp only [planarBlock_thirdCos, Int.cast_one, mul_one, planarBlock_cos_third, planarBlock_axisEven]
  split_ifs <;> ring

end GMCExplicitDelta.Localization
