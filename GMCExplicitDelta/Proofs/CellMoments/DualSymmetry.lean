module

public import GMCExplicitDelta.Proofs.CellMoments.Isotropy

/-! # Coordinate symmetries of the centered frozen dual matrix -/

@[expose] public section

open MeasureTheory Homogenization Homogenization.Book SubdiffusiveProcess.CoarseGrainingVocab
open scoped Matrix.Norms.Elementwise

namespace GMCExplicitDelta.Localization

open Assembly

variable {d : ℕ}

/-- The raw cutoff inverse-star matrix is the lower-right coarse block. -/
theorem cellMoment_dual_eq_block (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) (Q : Homogenization.TriadicCube d) :
    (randomAStarMatrix M L (Ch02.cubeDomain Q) ω)⁻¹ =
      (coarseBlockMatrix (openCubeSet Q)
        (scalarCoeffField (SubdiffusiveProcess.Model.aCutoff M L ω))).lowerRight := by
  have heq := eq_coarseBlockMatrix_of_isCoarseBlockMatrix
    (isCoarseBlockMatrix_ch02_aCutoff M L ω Q)
  rw [← heq, Ch02.coarseBlockMatrix_lowerRight]
  let hdata := aCutoffCoeffOnData M L ω (Ch02.cubeDomain Q)
  have hTheory := Ch02.responseSymmetricDirichletNeumannTheory
    (Ch02.cubeDomain Q) hdata.toCoeffOn hdata.isSymmetric
  change (Ch02.aStarCoarse (Ch02.cubeDomain Q) hdata.toCoeffOn)⁻¹ = _
  rw [hTheory.derived_matrices.2.1]
  unfold Ch02.sigmaStarCoarse
  exact Matrix.nonsing_inv_nonsing_inv _
    (Ch02.isUnit_det_sigmaStarInvCoarse (Ch02.cubeDomain Q) hdata.toCoeffOn)

/-- Rotating a sample rotates its scalar coefficient field. -/
theorem cellMoment_scalar_field_rotate (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (R : Homogenization.Mat d) (hR : IsSignedPermutationMatrix R)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    scalarCoeffField (SubdiffusiveProcess.Model.aCutoff M L (rotatePotentialSample R hR ω)) =
      rotateCoeffField R (scalarCoeffField (SubdiffusiveProcess.Model.aCutoff M L ω)) := by
  funext x
  change scalarMatrix (SubdiffusiveProcess.Model.aCutoff M L (rotatePotentialSample R hR ω) x) =
    matTranspose R * scalarMatrix (SubdiffusiveProcess.Model.aCutoff M L ω (matVecMul R x)) * R
  rw [aCutoff_rotatePotentialSample]
  simp [scalarMatrix, hR.transpose_mul_self]

/-- Coordinate sign flips conjugate the raw dual matrix. -/
theorem cellMoment_dual_flip (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    (i : Fin d) (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    (randomAStarMatrix M L (Ch02.cubeDomain (originCube d (n : ℤ)))
      (rotatePotentialSample (signFlipMatrix i) (isSignedPermutationMatrix_signFlipMatrix i) ω))⁻¹ =
      signFlipMatrix i *
        (randomAStarMatrix M L (Ch02.cubeDomain (originCube d (n : ℤ))) ω)⁻¹ * signFlipMatrix i := by
  simp only [cellMoment_dual_eq_block, cellMoment_scalar_field_rotate]
  exact coarseBlockMatrix_lowerRight_signFlip_openCubeSet_originCube_of_exists
    ⟨_, isCoarseBlockMatrix_ch02_aCutoff M L ω _⟩ i

/-- Coordinate swaps conjugate the raw dual matrix. -/
theorem cellMoment_dual_swap (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    (i j : Fin d) (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    (randomAStarMatrix M L (Ch02.cubeDomain (originCube d (n : ℤ)))
      (rotatePotentialSample (Matrix.swap ℝ i j) (isSignedPermutationMatrix_swap i j) ω))⁻¹ =
      Matrix.swap ℝ i j *
        (randomAStarMatrix M L (Ch02.cubeDomain (originCube d (n : ℤ))) ω)⁻¹ * Matrix.swap ℝ i j := by
  simp only [cellMoment_dual_eq_block, cellMoment_scalar_field_rotate]
  exact coarseBlockMatrix_lowerRight_swap_openCubeSet_originCube_of_exists
    ⟨_, isCoarseBlockMatrix_ch02_aCutoff M L ω _⟩ i j

/-- Centering by a scalar commutes with involutive conjugation. -/
theorem cellMoment_center_conj (A R : Homogenization.Mat d) (a b : ℝ) (hRR : R * R = 1) :
    a • (R * A * R) - b • 1 = R * (a • A - b • 1) * R := by
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, hRR]

/-- Every centered entry retains its second moment. -/
theorem cellMoment_centeredY_memLp (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (U : Ch02.Domain d) (b : ℝ) (i j : Fin d) :
    MemLp (fun ω => (frozenY M L U ω - b • (1 : Homogenization.Mat d)) i j) 2 M.P.toMeasure :=
  (cellMoment_frozenY_entry_memLp M L U i j).sub (memLp_const _)

/-- The expected Gram matrix of the centered dual coefficient is isotropic. -/
theorem cellMoment_centeredY_gram_scalar (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) (b : ℝ) :
    IsScalarMatrix (∫ ω,
      (frozenY M L (cubeAt 0 n) ω - b • (1 : Homogenization.Mat d)).transpose *
        (frozenY M L (cubeAt 0 n) ω - b • (1 : Homogenization.Mat d)) ∂M.P.toMeasure) := by
  let : NeZero d := neZero_of_gmcModel M
  let A := fun ω => frozenY M L (cubeAt 0 n) ω - b • (1 : Homogenization.Mat d)
  have hG := cellMoment_integrable_gram (cellMoment_centeredY_memLp M L (cubeAt 0 n) b)
  apply isScalarMatrix_of_isSignFlipInvariant_of_isSwapInvariant
  · intro i
    apply cellMoment_integral_invariant hG
      (measurable_rotatePotentialSample (signFlipMatrix i) (isSignedPermutationMatrix_signFlipMatrix i))
      (potentialSequenceLaw_rotation M (signFlipMatrix i) (isSignedPermutationMatrix_signFlipMatrix i))
    intro ω
    have hA : A (rotatePotentialSample (signFlipMatrix i) (isSignedPermutationMatrix_signFlipMatrix i) ω) =
        signFlipMatrix i * A ω * signFlipMatrix i := by
      dsimp [A, frozenY]
      rw [freshRet_cubeAt_zero]
      change ahom M L • (randomAStarMatrix M L (Ch02.cubeDomain (originCube d (n : ℤ))) _)⁻¹ - b • 1 =
        (signFlipMatrix i) *
          (ahom M L • (randomAStarMatrix M L (Ch02.cubeDomain (originCube d (n : ℤ))) ω)⁻¹ - b • 1) *
          (signFlipMatrix i)
      rw [cellMoment_dual_flip]
      exact cellMoment_center_conj _ _ _ _ (signFlipMatrix_sq i)
    change (A _).transpose * A _ = _
    rw [hA]
    exact cellMoment_gram_conj _ _ (Matrix.diagonal_transpose _) (signFlipMatrix_sq i)
  · intro i j
    apply cellMoment_integral_invariant hG
      (measurable_rotatePotentialSample (Matrix.swap ℝ i j) (isSignedPermutationMatrix_swap i j))
      (potentialSequenceLaw_rotation M (Matrix.swap ℝ i j) (isSignedPermutationMatrix_swap i j))
    intro ω
    have hA : A (rotatePotentialSample (Matrix.swap ℝ i j) (isSignedPermutationMatrix_swap i j) ω) =
        Matrix.swap ℝ i j * A ω * Matrix.swap ℝ i j := by
      dsimp [A, frozenY]
      rw [freshRet_cubeAt_zero]
      change ahom M L • (randomAStarMatrix M L (Ch02.cubeDomain (originCube d (n : ℤ))) _)⁻¹ - b • 1 =
        (Matrix.swap ℝ i j) *
          (ahom M L • (randomAStarMatrix M L (Ch02.cubeDomain (originCube d (n : ℤ))) ω)⁻¹ - b • 1) *
          (Matrix.swap ℝ i j)
      rw [cellMoment_dual_swap]
      exact cellMoment_center_conj _ _ _ _ (Matrix.swap_mul_self (R := ℝ) i j)
    change (A _).transpose * A _ = _
    rw [hA]
    exact cellMoment_gram_conj _ _ (Matrix.transpose_swap i j) (Matrix.swap_mul_self (R := ℝ) i j)

end GMCExplicitDelta.Localization
