module

public import GMCExplicitDelta.Proofs.CellMoments.Integrable

/-! # Annealed quadratic response on a triadic cell -/

@[expose] public section

open MeasureTheory Homogenization Homogenization.Book SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion
open scoped Matrix.Norms.Elementwise

namespace GMCExplicitDelta.Localization

open Assembly Contract

variable {d : ℕ}

/-- The identity matrix acts identically in the vocabulary's matrix action. -/
theorem cellMoment_matVecMul_one (q : Homogenization.Vec d) :
    matVecMul (1 : Homogenization.Mat d) q = q := Matrix.one_mulVec q

/-- The squared Euclidean norm is the self-dot-product. -/
theorem cellMoment_vecDot_self (q : Homogenization.Vec d) : vecDot q q = vecNormSq q := rfl

/-- The zero translate of a cell is its Chapter 2 cube domain. -/
theorem cellMoment_cellAt_zero (R : Homogenization.TriadicCube d) : cellAt 0 R = Ch02.cubeDomain R := by
  unfold cellAt SubdiffusiveProcess.LambdaStability.translatedDomain Ch02.cubeDomain
  congr 1
  exact translateSet_zero _

/-- Stationarity transports the primal annealed matrix to the centered cube. -/
theorem cellMoment_abar_cell (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    (R : Homogenization.TriadicCube d) (hR : R.scale = (n : ℤ)) :
    abar M L (cellAt 0 R) = abarScalarReadout M L n • (1 : Homogenization.Mat d) := by
  rw [cellMoment_cellAt_zero, ← abar_eq_abarScalarReadout_smul_one M L n]
  ext i j
  unfold abar
  rw [integral_matrix_apply (integrable_randomAMatrix M L (Ch02.cubeDomain R)) i j,
    integral_matrix_apply (integrable_randomAMatrix M L (Ch02.cubeDomain (originCube d (n : ℤ)))) i j,
    integral_randomAMatrix_entry_cube_eq_originCube, hR]

/-- The dual annealed matrix is scalar on the centered cube. -/
theorem cellMoment_abarStarInv_scalar (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) :
    abarStarInv M L (Ch02.cubeDomain (originCube d (n : ℤ))) =
      @annealedDualScalar d (neZero_of_gmcModel M) M L n • (1 : Homogenization.Mat d) := by
  let : NeZero d := neZero_of_gmcModel M
  rw [← aux_dedup_d136_annealedSigmaStarInvAtScale_eq_abarStarInv M L n]
  exact (Ch04.Internal.annealedPrimitiveScalarizationData_of_isotropic_adjoint
    (aCutoffRestrictionLaw_lawCarrier M L) (aCutoffRestrictionLaw_isotropic M L)
    (aCutoffRestrictionLaw_adjoint_invariant M L) (n : ℤ)).sigmaStarInv_eq

/-- Stationarity transports the dual annealed matrix to the centered cube. -/
theorem cellMoment_abarStarInv_cell (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    (R : Homogenization.TriadicCube d) (hR : R.scale = (n : ℤ)) :
    abarStarInv M L (cellAt 0 R) =
      @annealedDualScalar d (neZero_of_gmcModel M) M L n • (1 : Homogenization.Mat d) := by
  let : NeZero d := neZero_of_gmcModel M
  rw [cellMoment_cellAt_zero, ← cellMoment_abarStarInv_scalar M L n]
  ext i j
  unfold abarStarInv
  rw [integral_matrix_apply (integrable_randomAStarMatrix_inv M L (Ch02.cubeDomain R)) i j,
    integral_matrix_apply (integrable_randomAStarMatrix_inv M L (Ch02.cubeDomain (originCube d (n : ℤ)))) i j,
    integral_randomAStarInv_entry_cube_eq_originCube, hR]

/-- The dual scalar readout agrees with the normalization used by the assembly. -/
theorem cellMoment_beta_scalar (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) :
    betaMean M L n = ahom M L * @annealedDualScalar d (neZero_of_gmcModel M) M L n := by
  let : NeZero d := neZero_of_gmcModel M
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
  rw [freshRet_beta_eq, cellMoment_abarStarInv_scalar]
  simp only [Matrix.trace_smul, Matrix.trace_one, smul_eq_mul, Fintype.card_fin]
  field_simp

/-- A quadratic form of an integrable random matrix is integrable. -/
theorem cellMoment_integrable_quadratic {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {A : Ω → Homogenization.Mat d} (hA : Integrable A μ) (q : Homogenization.Vec d) :
    Integrable (fun ω => (1 / 2 : ℝ) * vecDot q (matVecMul (A ω) q)) μ := by
  apply Integrable.const_mul
  unfold vecDot matVecMul
  exact integrable_finsetSum Finset.univ fun i _ =>
    (integrable_finsetSum Finset.univ fun j _ =>
      ((hA.eval i).eval j).mul_const (q j)).const_mul (q i)

/-- The annealed response on a cell has the isotropic quadratic formula at every scale. -/
theorem cellMoment_integral_frozenJ (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    (R : Homogenization.TriadicCube d) (hR : R.scale = (n : ℤ)) (p q : Homogenization.Vec d) :
    ∫ ω, frozenJ M L (cellAt 0 R) p q ω ∂M.P.toMeasure = meanJ M L n p q := by
  let : NeZero d := neZero_of_gmcModel M
  have ha := driftSeed_ahom_pos M L
  have hs := Real.sq_sqrt ha.le
  have hs0 : Real.sqrt (ahom M L) ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  let p' := (Real.sqrt (ahom M L))⁻¹ • p
  let q' := Real.sqrt (ahom M L) • q
  have hfun : frozenJ M L (cellAt 0 R) p q = fun ω =>
      (1 / 2 : ℝ) * vecDot p' (matVecMul (randomAMatrix M L (cellAt 0 R) ω) p') +
      (1 / 2 : ℝ) * vecDot q' (matVecMul ((randomAStarMatrix M L (cellAt 0 R) ω)⁻¹) q') -
      vecDot p' q' := by
    funext ω
    exact cutoffResponseJ_eq_randomMatrixQuadratics M L (cellAt 0 R) p' q' ω
  have hp := integrable_randomAMatrix_quadratic M L (cellAt 0 R) p'
  have hq := cellMoment_integrable_quadratic (integrable_randomAStarMatrix_inv M L (cellAt 0 R)) q'
  have hsub := integral_sub (hp.add hq) (integrable_const (vecDot p' q'))
  simp only [Pi.add_apply] at hsub
  rw [hfun, hsub, integral_add hp hq,
    integral_randomAMatrix_quadratic, integral_randomAStarMatrix_inv_quadratic,
    integral_const, cellMoment_abar_cell M L n R hR, cellMoment_abarStarInv_cell M L n R hR]
  simp only [probReal_univ, one_smul, smul_matVecMul, cellMoment_matVecMul_one,
    vecDot_smul_right, cellMoment_vecDot_self]
  unfold p' q'
  rw [vecNormSq_smul, vecNormSq_smul, vecDot_smul_left, vecDot_smul_right]
  unfold meanJ
  rw [cellMoment_beta_scalar, freshRet_alpha_eq]
  simp only [inv_pow, hs]
  field_simp [hs0, ha.ne']

/-- C8 with the exact localization statement. -/
theorem integral_frozenJ_cell_proof (M : SubdiffusiveProcess.Model.GMCModel d) {D F : ℝ} (L : ℕ)
    (hP : InductionP M L D F) (n : ℕ) (hn : L ≤ n) (R : Homogenization.TriadicCube d)
    (hR : R.scale = (n : ℤ)) (p q : Homogenization.Vec d) :
    ∫ ω, frozenJ M L (cellAt 0 R) p q ω ∂M.P.toMeasure = meanJ M L n p q := by
  have _hP := hP
  have _hn := hn
  exact cellMoment_integral_frozenJ M L n R hR p q

end GMCExplicitDelta.Localization
