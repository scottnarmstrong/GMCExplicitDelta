module

public import GMCExplicitDelta.Coarse.Symmetric
public import GMCExplicitDelta.Coarse.Phi

/-!
# C4 (order bounds), C6 (spectral bound by the defect), C7 (rescaled pairs), deterministic part

For a coefficient `a` that is symmetric almost everywhere (in particular every scalar
coefficient), with `X = XU U a`, `Y = YU U a`, `𝓙 = defectMat U a`:
`Y⁻¹ ≤ X`, `X⁻¹ ≤ Y`, `0 ≤ 𝓙` (Loewner), `J(U,p,q;a) ≥ 0`, the `𝗑`-bounds under `𝓙 ≤ θ I`,
and `J(U, e^{c/2} e, e^{-c/2} e; a) ≤ Φ_{|c|}(J(U,e,e;a))`.
-/

@[expose] public section

open Homogenization.Book.Ch02
open Homogenization (Vec Mat vecDot vecNormSq matVecMul matTranspose symmPart MatLoewnerLE
  scalarMatrix volumeMeasureOn MemVectorL2 GradMemL2On H1Function restrictCoeffField
  vecNormSq_nonneg vecNormSq_eq_zero)
open Matrix

namespace GMCExplicitDelta.Coarse

variable {d : ℕ}

theorem matLoewnerLE_iff_qf {A B : Mat d} : MatLoewnerLE A B ↔ ∀ x, qf A x ≤ qf B x := by
  unfold MatLoewnerLE
  constructor
  · intro h x
    have := h x
    simp only [vecDot_matVecMul_eq] at this
    linarith
  · intro h x
    have := h x
    simp only [vecDot_matVecMul_eq]
    linarith

theorem qf_smul_one (c : ℝ) (x : Vec d) : qf (c • (1 : Mat d)) x = c * (x ⬝ᵥ x) := by
  simp [qf, Matrix.smul_mulVec, dotProduct_smul]

theorem qf_zero_mat (x : Vec d) : qf (0 : Mat d) x = 0 := by simp [qf]

theorem two_mul_le_of_sq_le {A B N : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (_hN : 0 ≤ N)
    (h : N ^ 2 ≤ A * B) : 2 * N ≤ A + B := by
  by_contra hlt
  rw [not_le] at hlt
  nlinarith [sq_nonneg (A - B)]

/-- The scalar core of C6. -/
theorem bounds_of_sum_le {N A B θ : ℝ} (hθ : 0 ≤ θ) (hN : 0 < N) (hA : 0 < A) (_hB : 0 ≤ B)
    (hAB : N ^ 2 ≤ A * B) (hsum : A + B ≤ (2 + 2 * θ) * N) :
    (xfun θ)⁻¹ * N ≤ A ∧ A ≤ xfun θ * N := by
  have hs : 0 < A / N := div_pos hA hN
  have hinv : (A / N)⁻¹ ≤ B / N := by
    rw [inv_div, div_le_div_iff₀ hA hN]
    nlinarith
  have hle : A / N + (A / N)⁻¹ ≤ 2 + 2 * θ := by
    have h1 : A / N + B / N ≤ 2 + 2 * θ := by
      rw [← add_div, div_le_iff₀ hN]; linarith
    linarith
  obtain ⟨h1, h2⟩ := xfun_bounds hθ hs hle
  constructor
  · rw [le_div_iff₀ hN] at h1; exact h1
  · rw [div_le_iff₀ hN] at h2; exact h2

section Symmetric

variable {U : Domain d} {a : CoeffOn U} (ha : CoeffOn.IsSymmetric a)
include ha

theorem YU_inv : (YU U a)⁻¹ = aStarCoarse U a := by
  have hu : IsUnit (aStarCoarse U a).det := by
    rw [← Matrix.isUnit_iff_isUnit_det]; exact (aStar_posDef ha).isUnit
  exact Matrix.nonsing_inv_nonsing_inv _ hu

/-- C4: `X ≥ Y⁻¹` (that is, `A_* ≤ A`). -/
theorem YU_inv_le_XU : MatLoewnerLE (YU U a)⁻¹ (XU U a) := by
  rw [matLoewnerLE_iff_qf, YU_inv ha]
  exact qf_aStar_le_XU ha

/-- C4: `Y ≥ X⁻¹`. -/
theorem XU_inv_le_YU : MatLoewnerLE (XU U a)⁻¹ (YU U a) := by
  rw [matLoewnerLE_iff_qf]
  exact posDef_inv_antitone (aStar_posDef ha) (XU_posDef ha) (qf_aStar_le_XU ha)

theorem sq_dot_le_XU (x : Vec d) :
    (x ⬝ᵥ x) ^ 2 ≤ qf (XU U a) x * qf (YU U a) x := by
  have h1 := posDef_sq_dot_le (XU_posDef ha) x
  have h2 := (matLoewnerLE_iff_qf.mp (XU_inv_le_YU ha)) x
  have h3 := posDef_qf_nonneg (XU_posDef ha) x
  exact h1.trans (mul_le_mul_of_nonneg_left h2 h3)

/-- C4: the defect matrix is nonnegative. -/
theorem defectMat_nonneg : MatLoewnerLE (0 : Mat d) (defectMat U a) := by
  rw [matLoewnerLE_iff_qf]
  intro x
  rw [qf_zero_mat, qf_defectMat]
  have h1 := posDef_sq_dot_le (XU_posDef ha) x
  have h2 := (matLoewnerLE_iff_qf.mp (XU_inv_le_YU ha)) x
  have hA := posDef_qf_nonneg (XU_posDef ha) x
  have hB := posDef_qf_nonneg (XU_posDef ha).inv x
  have hN : 0 ≤ x ⬝ᵥ x := vecNormSq_nonneg x
  have := two_mul_le_of_sq_le hA hB hN h1
  linarith

/-- `J(U,e,e;a) = e·𝓙 e` for a unit vector. -/
theorem responseJ_self_eq_defect {e : Vec d} (he : e ⬝ᵥ e = 1) :
    responseJ U a e e = qf (defectMat U a) e := by
  rw [responseJ_eq_XY ha, qf_defectMat, he]; ring

/-- C6: `𝓙 ≤ θ I` implies `𝗑(θ)⁻¹ I ≤ X ≤ 𝗑(θ) I`. -/
theorem XU_bounds {θ : ℝ} (hθ : 0 ≤ θ) (h : MatLoewnerLE (defectMat U a) (θ • (1 : Mat d))) :
    MatLoewnerLE ((xfun θ)⁻¹ • (1 : Mat d)) (XU U a) ∧
      MatLoewnerLE (XU U a) (xfun θ • (1 : Mat d)) := by
  rw [matLoewnerLE_iff_qf] at h
  simp only [matLoewnerLE_iff_qf, qf_smul_one]
  have key : ∀ x : Vec d, (xfun θ)⁻¹ * (x ⬝ᵥ x) ≤ qf (XU U a) x ∧
      qf (XU U a) x ≤ xfun θ * (x ⬝ᵥ x) := by
    intro x
    by_cases hx : x = 0
    · subst hx; simp [qf]
    · have hN : 0 < x ⬝ᵥ x := by
        rcases (vecNormSq_nonneg x).lt_or_eq with h' | h'
        · exact h'
        · exact absurd (vecNormSq_eq_zero h'.symm) hx
      have hA := posDef_qf_pos (XU_posDef ha) hx
      have hB := posDef_qf_nonneg (XU_posDef ha).inv x
      have h2 := (matLoewnerLE_iff_qf.mp (XU_inv_le_YU ha)) x
      have h3 := h x
      rw [qf_defectMat, qf_smul_one] at h3
      exact bounds_of_sum_le hθ hN hA hB (posDef_sq_dot_le (XU_posDef ha) x) (by linarith)
  exact ⟨fun x => (key x).1, fun x => (key x).2⟩

/-- C6 for `Y`. -/
theorem YU_bounds {θ : ℝ} (hθ : 0 ≤ θ) (h : MatLoewnerLE (defectMat U a) (θ • (1 : Mat d))) :
    MatLoewnerLE ((xfun θ)⁻¹ • (1 : Mat d)) (YU U a) ∧
      MatLoewnerLE (YU U a) (xfun θ • (1 : Mat d)) := by
  rw [matLoewnerLE_iff_qf] at h
  simp only [matLoewnerLE_iff_qf, qf_smul_one]
  have key : ∀ x : Vec d, (xfun θ)⁻¹ * (x ⬝ᵥ x) ≤ qf (YU U a) x ∧
      qf (YU U a) x ≤ xfun θ * (x ⬝ᵥ x) := by
    intro x
    by_cases hx : x = 0
    · subst hx; simp [qf]
    · have hN : 0 < x ⬝ᵥ x := by
        rcases (vecNormSq_nonneg x).lt_or_eq with h' | h'
        · exact h'
        · exact absurd (vecNormSq_eq_zero h'.symm) hx
      have hA := posDef_qf_pos (YU_posDef ha) hx
      have hB : 0 ≤ qf (YU U a)⁻¹ x := posDef_qf_nonneg (YU_posDef ha).inv x
      have h2 := qf_aStar_le_XU ha x
      have h3 := h x
      rw [qf_defectMat, qf_smul_one] at h3
      have h4 : qf (YU U a)⁻¹ x = qf (aStarCoarse U a) x := by rw [YU_inv ha]
      refine bounds_of_sum_le hθ hN hA hB (posDef_sq_dot_le (YU_posDef ha) x) ?_
      rw [h4]; linarith
  exact ⟨fun x => (key x).1, fun x => (key x).2⟩

/-- C7 (deterministic part): `J(U, e^{c/2} e, e^{-c/2} e; a) ≤ Φ_{|c|}(J(U,e,e;a))`. -/
theorem responseJ_rescaled_le_phi {e : Vec d} (he : e ⬝ᵥ e = 1) (c : ℝ) :
    responseJ U a (Real.exp (c / 2) • e) (Real.exp (-c / 2) • e) ≤
      phi |c| (responseJ U a e e) := by
  have he0 : e ≠ 0 := by rintro rfl; simp at he
  have hα := posDef_qf_pos (XU_posDef ha) he0
  have h1 := posDef_sq_dot_le (XU_posDef ha) e
  have h2 := (matLoewnerLE_iff_qf.mp (XU_inv_le_YU ha)) e
  have hαβ : 1 ≤ qf (XU U a) e * qf (YU U a) e := by
    rw [he] at h1
    nlinarith
  have hJ : responseJ U a e e = (qf (XU U a) e + qf (YU U a) e) / 2 - 1 := by
    rw [responseJ_eq_XY ha, he]; ring
  have hR : responseJ U a (Real.exp (c / 2) • e) (Real.exp (-c / 2) • e) =
      (1 / 2) * (Real.exp c * qf (XU U a) e + Real.exp (-c) * qf (YU U a) e) - 1 := by
    rw [responseJ_eq_XY ha, posDef_qf_smul, posDef_qf_smul, smul_dotProduct, dotProduct_smul,
      he, smul_eq_mul, smul_eq_mul]
    have e1 : Real.exp (c / 2) ^ 2 = Real.exp c := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have e2 : Real.exp (-c / 2) ^ 2 = Real.exp (-c) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have e3 : Real.exp (c / 2) * Real.exp (-c / 2) = 1 := by
      have h0 : c / 2 + -c / 2 = 0 := by ring
      rw [← Real.exp_add, h0, Real.exp_zero]
    rw [e1, e2]
    nlinarith [e3]
  rw [hR, hJ]
  exact half_exp_le_phi hαβ c

/-- C7: the same bound with any upper bound `M` for `J(U,e,e;a)` (for instance `J^max`). -/
theorem responseJ_rescaled_le_phi_of_le {e : Vec d} (he : e ⬝ᵥ e = 1) (c : ℝ) {M : ℝ}
    (hM : responseJ U a e e ≤ M) :
    responseJ U a (Real.exp (c / 2) • e) (Real.exp (-c / 2) • e) ≤ phi |c| M := by
  refine (responseJ_rescaled_le_phi ha he c).trans ?_
  exact phi_mono_j (abs_nonneg c) (Set.mem_Ici.mpr (responseJ_nonneg U a e e))
    (Set.mem_Ici.mpr ((responseJ_nonneg U a e e).trans hM)) hM

end Symmetric

end GMCExplicitDelta.Coarse
