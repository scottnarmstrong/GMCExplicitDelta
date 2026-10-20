module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-! Exact first-mode averages on the three equal subintervals of the unit interval. -/

@[expose] public section

open Real intervalIntegral

namespace GMCExplicitDelta.Localization

/-- The sine average on a third of the interval. -/
theorem planarBlock_sin_third (i : Fin 3) :
    3 * (∫ t in (i : ℝ) / 3..((i : ℝ) + 1) / 3, sin (π * t)) =
      (if i = 1 then 3 / π else 3 / (2 * π)) := by
  rw [integral_comp_mul_left _ Real.pi_ne_zero, integral_sin]
  have hcos : cos (π * 2 / 3) = -(1 / 2 : ℝ) := by
    rw [show π * 2 / 3 = π - π / 3 by ring, cos_pi_sub, cos_pi_div_three]
  fin_cases i <;>
    norm_num [← mul_div_assoc, Real.cos_pi_div_three, hcos] <;> ring

/-- The cosine average on a third of the interval. -/
theorem planarBlock_cos_third (i : Fin 3) :
    3 * (∫ t in (i : ℝ) / 3..((i : ℝ) + 1) / 3, cos (π * t)) =
      (if i = 0 then 3 * √3 / (2 * π)
       else if i = 1 then 0 else -(3 * √3 / (2 * π))) := by
  rw [integral_comp_mul_left _ Real.pi_ne_zero, integral_cos]
  have hsin : sin (π * 2 / 3) = √3 / 2 := by
    rw [show π * 2 / 3 = π - π / 3 by ring, sin_pi_sub, sin_pi_div_three]
  fin_cases i <;>
    norm_num [← mul_div_assoc, Real.sin_pi_div_three, hsin] <;> ring

/-- The second sine average on a third of the interval. -/
theorem planarBlock_sin_two_third (i : Fin 3) :
    3 * (∫ t in (i : ℝ) / 3..((i : ℝ) + 1) / 3, sin (2 * π * t)) =
      (if i = 0 then 9 / (4 * π)
       else if i = 1 then 0 else -(9 / (4 * π))) := by
  rw [integral_comp_mul_left _ (mul_ne_zero (by norm_num) Real.pi_ne_zero), integral_sin]
  have hc2 : cos (π * (2 / 3)) = -(1 / 2 : ℝ) := by
    rw [show π * (2 / 3) = π - π / 3 by ring, cos_pi_sub, cos_pi_div_three]
  have hc4 : cos (π * (4 / 3)) = -(1 / 2 : ℝ) := by
    rw [show π * (4 / 3) = π / 3 + π by ring, cos_add_pi, cos_pi_div_three]
  fin_cases i <;> norm_num [← mul_div_assoc, hc2, hc4] <;>
    ring_nf <;> simp only [hc2, hc4] <;> ring

end GMCExplicitDelta.Localization
