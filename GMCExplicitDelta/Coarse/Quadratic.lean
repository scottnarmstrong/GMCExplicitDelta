module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Quadratic-form lemmas for positive definite real matrices

Elementary facts (no spectral theorem) used for C4 and C6: operator antitonicity of the
inverse and the Cauchy-Schwarz bound `|z|^4 ≤ (z·S z)(z·S⁻¹ z)`, stated for quadratic forms
`qf S z = z ⬝ᵥ S *ᵥ z`.
-/

@[expose] public section

open Matrix

namespace GMCExplicitDelta.Coarse

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The quadratic form of a matrix. -/
def qf (S : Matrix n n ℝ) (z : n → ℝ) : ℝ := z ⬝ᵥ S *ᵥ z

omit [Fintype n] [DecidableEq n] in
theorem posDef_symm {S : Matrix n n ℝ} (hS : S.PosDef) : Sᵀ = S := by
  have h := hS.isHermitian.eq
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

omit [DecidableEq n] in
theorem posDef_qf_nonneg {S : Matrix n n ℝ} (hS : S.PosDef) (z : n → ℝ) : 0 ≤ qf S z := by
  simpa [qf] using hS.posSemidef.dotProduct_mulVec_nonneg z

omit [DecidableEq n] in
theorem posDef_qf_pos {S : Matrix n n ℝ} (hS : S.PosDef) {z : n → ℝ} (hz : z ≠ 0) :
    0 < qf S z := by
  simpa [qf] using hS.dotProduct_mulVec_pos hz

theorem posDef_mulVec_inv {S : Matrix n n ℝ} (hS : S.PosDef) (z : n → ℝ) :
    S *ᵥ (S⁻¹ *ᵥ z) = z := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (by
    simpa [Matrix.isUnit_iff_isUnit_det] using hS.isUnit), Matrix.one_mulVec]

theorem posDef_inv_mulVec {S : Matrix n n ℝ} (hS : S.PosDef) (z : n → ℝ) :
    S⁻¹ *ᵥ (S *ᵥ z) = z := by
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (by
    simpa [Matrix.isUnit_iff_isUnit_det] using hS.isUnit), Matrix.one_mulVec]

omit [DecidableEq n] in
theorem posDef_vecMul {S : Matrix n n ℝ} (hS : S.PosDef) (u : n → ℝ) :
    u ᵥ* S = S *ᵥ u := by
  conv_lhs => rw [← posDef_symm hS]
  exact Matrix.vecMul_transpose S u

omit [DecidableEq n] in
/-- Symmetry of the bilinear form of a positive definite matrix. -/
theorem posDef_dot_mulVec_comm {S : Matrix n n ℝ} (hS : S.PosDef) (u v : n → ℝ) :
    u ⬝ᵥ S *ᵥ v = v ⬝ᵥ S *ᵥ u := by
  rw [Matrix.dotProduct_mulVec, posDef_vecMul hS, dotProduct_comm]

omit [DecidableEq n] in
theorem posDef_qf_smul (S : Matrix n n ℝ) (t : ℝ) (z : n → ℝ) :
    qf S (t • z) = t ^ 2 * qf S z := by
  simp only [qf, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

/-- Variational lower bound for the inverse quadratic form. -/
theorem posDef_var_le {S : Matrix n n ℝ} (hS : S.PosDef) (z w : n → ℝ) :
    2 * (z ⬝ᵥ w) - qf S w ≤ qf S⁻¹ z := by
  have hSv : S *ᵥ (S⁻¹ *ᵥ z) = z := posDef_mulVec_inv hS z
  have h0 := posDef_qf_nonneg hS (w - S⁻¹ *ᵥ z)
  have e1 : qf S (w - S⁻¹ *ᵥ z) =
      qf S w - 2 * (z ⬝ᵥ w) + (S⁻¹ *ᵥ z) ⬝ᵥ z := by
    unfold qf
    rw [Matrix.mulVec_sub, hSv, sub_dotProduct, dotProduct_sub, dotProduct_sub,
      posDef_dot_mulVec_comm hS (S⁻¹ *ᵥ z) w, hSv, dotProduct_comm z w]
    ring
  have e2 : qf S⁻¹ z = (S⁻¹ *ᵥ z) ⬝ᵥ z := by
    unfold qf; exact dotProduct_comm _ _
  rw [e1] at h0
  rw [e2]
  linarith

/-- The variational bound is attained at `w = S⁻¹ z`. -/
theorem posDef_var_eq {S : Matrix n n ℝ} (hS : S.PosDef) (z : n → ℝ) :
    2 * (z ⬝ᵥ (S⁻¹ *ᵥ z)) - qf S (S⁻¹ *ᵥ z) = qf S⁻¹ z := by
  have hSv : S *ᵥ (S⁻¹ *ᵥ z) = z := posDef_mulVec_inv hS z
  have e2 : qf S⁻¹ z = z ⬝ᵥ (S⁻¹ *ᵥ z) := rfl
  have e3 : qf S (S⁻¹ *ᵥ z) = z ⬝ᵥ (S⁻¹ *ᵥ z) := by
    unfold qf
    rw [hSv, dotProduct_comm]
  rw [e2, e3]; ring

/-- Operator antitonicity of the inverse, in quadratic-form language. -/
theorem posDef_inv_antitone {S T : Matrix n n ℝ} (hS : S.PosDef) (hT : T.PosDef)
    (h : ∀ w, qf S w ≤ qf T w) (z : n → ℝ) : qf T⁻¹ z ≤ qf S⁻¹ z := by
  rw [← posDef_var_eq hT z]
  have := h (T⁻¹ *ᵥ z)
  have := posDef_var_le hS z (T⁻¹ *ᵥ z)
  linarith

/-- Cauchy-Schwarz: `(z·z)^2 ≤ (z·S z)(z·S⁻¹ z)`. -/
theorem posDef_sq_dot_le {S : Matrix n n ℝ} (hS : S.PosDef) (z : n → ℝ) :
    (z ⬝ᵥ z) ^ 2 ≤ qf S z * qf S⁻¹ z := by
  by_cases hz : z = 0
  · subst hz
    simp [qf]
  · have hq := posDef_qf_pos hS hz
    have h1 := posDef_var_le hS z ((z ⬝ᵥ z / qf S z) • z)
    rw [posDef_qf_smul, dotProduct_smul, smul_eq_mul] at h1
    have h2 : (z ⬝ᵥ z) ^ 2 / qf S z ≤ qf S⁻¹ z := by
      have e : 2 * (z ⬝ᵥ z / qf S z * (z ⬝ᵥ z)) - (z ⬝ᵥ z / qf S z) ^ 2 * qf S z =
          (z ⬝ᵥ z) ^ 2 / qf S z := by
        field_simp
        ring
      linarith
    rw [div_le_iff₀ hq] at h2
    linarith

end GMCExplicitDelta.Coarse
