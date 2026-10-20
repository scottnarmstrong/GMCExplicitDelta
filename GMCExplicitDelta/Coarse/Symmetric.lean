module

public import Homogenization.Book.Ch02.Theorems
public import GMCExplicitDelta.Coarse.Quadratic

/-!
# The pair `X_U, Y_U` for a symmetric coefficient (C1 consequences, C4 order bounds)

Vocabulary: `XU U a = A_U(a)` (`aCoarse`), `YU U a = (A_{*,U}(a))⁻¹`,
`defectMat U a = ½ (X_U + Y_U) - I` (the matrix `𝓙` of the proof map).

Reused from CoarseGraining (`Homogenization.Book.Ch02`):
`responseSymmetricDirichletNeumannTheory` (fields `derived_matrices`, `kappa_eq_zero`,
`dirichlet_neumann_bracketing`), `responseBasicVariationalIdentitiesTheory`
(`matrix_identities.full_response`), `sigmaStarCoarse_posDef`, `sigmaStarCoarse_le_sigmaCoarse`,
`sigmaCoarse_isSymm`, `sigmaStarCoarse_isSymm`, `responseJ_nonneg`.
-/

@[expose] public section

open Homogenization.Book.Ch02
open Homogenization (Vec Mat vecDot vecNormSq matVecMul matTranspose symmPart MatLoewnerLE
  scalarMatrix volumeMeasureOn MemVectorL2 GradMemL2On H1Function restrictCoeffField
  vecNormSq_nonneg vecNormSq_eq_zero)
open Matrix

namespace GMCExplicitDelta.Coarse

variable {d : ℕ}

theorem vecDot_matVecMul_eq (A : Mat d) (x : Vec d) : vecDot x (matVecMul A x) = qf A x := rfl

theorem vecDot_eq_dotProduct (x y : Vec d) : vecDot x y = x ⬝ᵥ y := rfl

theorem matVecMul_eq_mulVec (A : Mat d) (x : Vec d) : matVecMul A x = A *ᵥ x := rfl

/-- `X_U = A_U`. -/
noncomputable abbrev XU (U : Domain d) (a : CoeffOn U) : Mat d := aCoarse U a

/-- `Y_U = (A_{*,U})⁻¹`. -/
noncomputable abbrev YU (U : Domain d) (a : CoeffOn U) : Mat d := (aStarCoarse U a)⁻¹

/-- The defect matrix `𝓙 = ½ (X_U + Y_U) - I`. -/
noncomputable def defectMat (U : Domain d) (a : CoeffOn U) : Mat d :=
  (1 / 2 : ℝ) • (XU U a + YU U a) - 1

theorem qf_defectMat (U : Domain d) (a : CoeffOn U) (x : Vec d) :
    qf (defectMat U a) x = (1 / 2) * (qf (XU U a) x + qf (YU U a) x) - x ⬝ᵥ x := by
  unfold defectMat qf
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, dotProduct_add, smul_eq_mul]

section Symmetric

variable {U : Domain d} {a : CoeffOn U} (ha : CoeffOn.IsSymmetric a)
include ha

theorem XU_eq_sigma : XU U a = sigmaCoarse U a :=
  (responseSymmetricDirichletNeumannTheory U a ha).derived_matrices.1

theorem aStar_eq_sigmaStar : aStarCoarse U a = sigmaStarCoarse U a :=
  (responseSymmetricDirichletNeumannTheory U a ha).derived_matrices.2.1

theorem kappa_eq_zero : kappaCoarse U a = 0 :=
  (responseSymmetricDirichletNeumannTheory U a ha).kappa_eq_zero

theorem YU_eq_sigmaStarInv : YU U a = sigmaStarInvCoarse U a := by
  show (aStarCoarse U a)⁻¹ = sigmaStarInvCoarse U a
  rw [aStar_eq_sigmaStar ha]
  exact Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_sigmaStarInvCoarse U a)

theorem aStar_posDef : (aStarCoarse U a).PosDef := by
  rw [aStar_eq_sigmaStar ha]; exact sigmaStarCoarse_posDef U a

theorem YU_posDef : (YU U a).PosDef := (aStar_posDef ha).inv

/-- Quadratic-form order `A_* ≤ A`. -/
theorem qf_aStar_le_XU (x : Vec d) : qf (aStarCoarse U a) x ≤ qf (XU U a) x := by
  rw [aStar_eq_sigmaStar ha, XU_eq_sigma ha]
  have h := sigmaStarCoarse_le_sigmaCoarse U a x
  simp only [vecDot_matVecMul_eq] at h
  linarith

theorem XU_posDef : (XU U a).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · have h := sigmaCoarse_isSymm U a
    rw [XU_eq_sigma ha]
    exact (Matrix.conjTranspose_eq_transpose_of_trivial _).trans h
  · intro x hx
    have h1 := posDef_qf_pos (aStar_posDef ha) hx
    have h2 := qf_aStar_le_XU ha x
    simpa [qf] using lt_of_lt_of_le h1 h2

/-- `J(U,p,q;a) = ½ p·X p + ½ q·Y q - p·q` for a symmetric coefficient. -/
theorem responseJ_eq_XY (p q : Vec d) :
    responseJ U a p q =
      (1 / 2) * qf (XU U a) p + (1 / 2) * qf (YU U a) q - p ⬝ᵥ q := by
  have hM := (responseBasicVariationalIdentitiesTheory U a).matrix_identities
  have h := hM.full_response p q
  have hk : matVecMul (coarseMatrices U a).kappa p = 0 := by
    have : (coarseMatrices U a).kappa = 0 := kappa_eq_zero ha
    rw [this]; ext i; simp [matVecMul]
  rw [hk, add_zero] at h
  rw [h, XU_eq_sigma ha, YU_eq_sigmaStarInv ha]
  try rfl

end Symmetric

end GMCExplicitDelta.Coarse
