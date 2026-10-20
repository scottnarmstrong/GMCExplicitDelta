module

public import GMCExplicitDelta.Coarse.Symmetric

/-!
# C3: homogeneity and scaling of the pair

`responseJ_scale`: `J(U,p,q;a) = J(U, λ^{-1/2} p, λ^{1/2} q; λ a)`;
`responseJ_smul'`: `J(U, μp, μq; a) = μ² J(U,p,q;a)`;
`XU_scale`, `YU_scale`: `X_U(λa) = λ X_U(a)`, `Y_U(λa) = λ⁻¹ Y_U(a)`.

Reused from CoarseGraining: `responseSubadditivityAndScalingTheory`
(`responseJ_homogeneous`, `sigma_homogeneous`, `sigmaStar_homogeneous`, `kappa_homogeneous`),
`responseBasicVariationalIdentitiesTheory` (`full_response`).
-/

@[expose] public section

open Homogenization.Book.Ch02
open Homogenization (Vec Mat vecDot vecNormSq matVecMul matTranspose symmPart MatLoewnerLE
  scalarMatrix volumeMeasureOn MemVectorL2 GradMemL2On H1Function restrictCoeffField
  vecNormSq_nonneg vecNormSq_eq_zero)
open Matrix

namespace GMCExplicitDelta.Coarse

variable {d : ℕ} {U : Domain d} {a : CoeffOn U}

/-- C3: `J(U,p,q;a) = J(U, λ^{-1/2} p, λ^{1/2} q; b)` when `b = λ a` a.e. -/
theorem responseJ_scale {lam : ℝ} (hlam : 0 < lam) {b : CoeffOn U}
    (hb : CoeffOn.AEScaled lam a b) (p q : Vec d) :
    responseJ U a p q = responseJ U b ((Real.sqrt lam)⁻¹ • p) (Real.sqrt lam • q) := by
  have hs : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have h := (responseSubadditivityAndScalingTheory U a).responseJ_homogeneous hlam hb
    ((Real.sqrt lam)⁻¹ • p) (Real.sqrt lam • q)
  rw [h, smul_smul, smul_smul, mul_inv_cancel₀ hs.ne', inv_mul_cancel₀ hs.ne', one_smul,
    one_smul]

/-- C3: quadratic homogeneity `J(U, μp, μq; a) = μ² J(U,p,q;a)`; this is CoarseGraining's
`Homogenization.Book.Ch02.responseJ_smul`. -/
theorem responseJ_smul' (μ : ℝ) (p q : Vec d) :
    responseJ U a (μ • p) (μ • q) = μ ^ 2 * responseJ U a p q :=
  responseJ_smul μ p q

private theorem aCoarse_eq_sub (b : CoeffOn U) :
    aCoarse U b = sigmaCoarse U b - matTranspose (kappaCoarse U b) := rfl

private theorem aStarCoarse_eq_sub (b : CoeffOn U) :
    aStarCoarse U b = sigmaStarCoarse U b - matTranspose (kappaCoarse U b) := rfl

/-- C3: `A_U(λ a) = λ A_U(a)`. -/
theorem XU_scale {lam : ℝ} (hlam : 0 < lam) {b : CoeffOn U}
    (hb : CoeffOn.AEScaled lam a b) : XU U b = lam • XU U a := by
  have T := responseSubadditivityAndScalingTheory U a
  show aCoarse U b = lam • aCoarse U a
  rw [aCoarse_eq_sub, aCoarse_eq_sub, T.sigma_homogeneous hlam hb, T.kappa_homogeneous hlam hb]
  simp [matTranspose, Matrix.transpose_smul, smul_sub]

/-- C3: `A_{*,U}(λ a) = λ A_{*,U}(a)`. -/
theorem aStar_scale {lam : ℝ} (hlam : 0 < lam) {b : CoeffOn U}
    (hb : CoeffOn.AEScaled lam a b) : aStarCoarse U b = lam • aStarCoarse U a := by
  have T := responseSubadditivityAndScalingTheory U a
  rw [aStarCoarse_eq_sub, aStarCoarse_eq_sub, T.sigmaStar_homogeneous hlam hb,
    T.kappa_homogeneous hlam hb]
  simp [matTranspose, Matrix.transpose_smul, smul_sub]

/-- C3: `Y_U(λ a) = λ⁻¹ Y_U(a)` (for `a` symmetric, so that `A_{*,U}(a)` is invertible). -/
theorem YU_scale (ha : CoeffOn.IsSymmetric a) {lam : ℝ} (hlam : 0 < lam) {b : CoeffOn U}
    (hb : CoeffOn.AEScaled lam a b) : YU U b = lam⁻¹ • YU U a := by
  show (aStarCoarse U b)⁻¹ = lam⁻¹ • (aStarCoarse U a)⁻¹
  have hu : IsUnit (aStarCoarse U a).det := by
    rw [← Matrix.isUnit_iff_isUnit_det]; exact (aStar_posDef ha).isUnit
  rw [aStar_scale hlam hb]
  have h := Matrix.inv_smul' (A := aStarCoarse U a) (Units.mk0 lam hlam.ne') hu
  simpa [Units.smul_def] using h

end GMCExplicitDelta.Coarse
