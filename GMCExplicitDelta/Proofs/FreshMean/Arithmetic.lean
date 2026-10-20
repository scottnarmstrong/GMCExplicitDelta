module

public import GMCExplicitDelta.Contract.DerivedFresh
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! # The scalar fresh-mean estimate from two annealed energies -/

@[expose] public section

namespace GMCExplicitDelta.Assembly

/-- The two energies above one give the sharp nonplanar fresh-mean return. -/
theorem freshRet_fresh_pair_le {α β c γ F : ℝ} (hα : 1 ≤ α) (hβ : 1 ≤ β)
    (hc : |c| ≤ γ) (hf : (α + β) / 2 - 1 ≤ F) :
    Real.exp γ * (Real.exp (-c) * α + Real.exp c * β) / 2 - 1 ≤
      Real.exp (2 * γ) * F + (Real.exp (2 * γ) - 1) / 2 := by
  have hγ : 0 ≤ γ := (abs_nonneg c).trans hc
  have hminus : Real.exp (-c) ≤ Real.exp γ :=
    Real.exp_le_exp.mpr ((neg_le_abs c).trans hc)
  have hplus : Real.exp c ≤ Real.exp γ :=
    Real.exp_le_exp.mpr ((le_abs_self c).trans hc)
  have hcosh : Real.cosh c ≤ Real.cosh γ :=
    Real.cosh_le_cosh.mpr (by simpa only [abs_of_nonneg hγ] using hc)
  have hsum : Real.exp (-c) + Real.exp c ≤ Real.exp (-γ) + Real.exp γ := by
    rw [Real.cosh_eq, Real.cosh_eq] at hcosh
    linarith only [hcosh]
  have hp : Real.exp (-c) * α + Real.exp c * β ≤
      Real.exp γ * (α + β - 2) + Real.exp (-γ) + Real.exp γ := by
    have h1 := mul_le_mul_of_nonneg_right hminus (sub_nonneg.mpr hα)
    have h2 := mul_le_mul_of_nonneg_right hplus (sub_nonneg.mpr hβ)
    nlinarith only [h1, h2, hsum]
  have hmul := mul_le_mul_of_nonneg_left hp (Real.exp_pos γ).le
  have hF := mul_le_mul_of_nonneg_left hf (Real.exp_pos (2 * γ)).le
  have heq : Real.exp (2 * γ) = Real.exp γ * Real.exp γ := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hcancel : Real.exp γ * Real.exp (-γ) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [heq] at hF ⊢
  nlinarith only [hmul, hF, hcancel]

/-- Without deterministic drift, only the sum of the two old energies is needed. -/
theorem freshRet_fresh_pair_zero_le {α β γ F : ℝ} (hf : (α + β) / 2 - 1 ≤ F) :
    Real.exp γ * (Real.exp (-0) * α + Real.exp 0 * β) / 2 - 1 ≤
      Real.exp γ * (1 + F) - 1 := by
  simp only [neg_zero, Real.exp_zero, one_mul]
  have h := mul_le_mul_of_nonneg_left hf (Real.exp_pos γ).le
  linarith only [h]

end GMCExplicitDelta.Assembly
