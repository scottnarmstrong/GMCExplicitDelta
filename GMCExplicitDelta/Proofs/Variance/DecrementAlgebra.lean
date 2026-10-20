module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

/-! # Scalar closure of the centered decrement argument -/

@[expose] public section

namespace GMCExplicitDelta.Assembly

/-- The scalar Young step in V2. -/
theorem frozenVar_centered_decrement_algebra {a Δ v w t : ℝ}
    (ha : 0 ≤ a) (hΔ : 0 ≤ Δ) (hv : 0 ≤ v) (ht : 0 < t)
    (hw : w ^ 2 ≤ Δ + 2 * w * Real.sqrt a)
    (htri : Real.sqrt v ≤ Real.sqrt a + w) :
    v ≤ (5 + 2 * (t + t⁻¹)) * a + (1 + 2 / t) * Δ := by
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt (add_nonneg ha hΔ)
  have hsav := Real.sqrt_nonneg a
  have hsbv := Real.sqrt_nonneg (a + Δ)
  have hwsub : (w - Real.sqrt a) ^ 2 ≤ a + Δ := by nlinarith only [hw, hsa]
  have hwroot := Real.le_sqrt_of_sq_le hwsub
  have htri' : Real.sqrt v ≤ 2 * Real.sqrt a + Real.sqrt (a + Δ) := by
    linarith only [htri, hwroot]
  have hsquare := (sq_le_sq₀ (Real.sqrt_nonneg v) (by positivity :
    0 ≤ 2 * Real.sqrt a + Real.sqrt (a + Δ))).2 htri'
  rw [Real.sq_sqrt hv] at hsquare
  have hyoung : 4 * Real.sqrt a * Real.sqrt (a + Δ) ≤ 2 * t * a + 2 / t * (a + Δ) := by
    apply (mul_le_mul_iff_right₀ ht).mp
    field_simp
    nlinarith only [sq_nonneg (t * Real.sqrt a - Real.sqrt (a + Δ)), hsa, hsb]
  have hfinal : v ≤ (5 + 2 * (t + t⁻¹)) * a + (1 + 2 / t) * Δ := by
    simp only [div_eq_mul_inv] at hyoung ⊢
    nlinarith only [hsquare, hyoung, hsa, hsb]
  exact hfinal

end GMCExplicitDelta.Assembly
