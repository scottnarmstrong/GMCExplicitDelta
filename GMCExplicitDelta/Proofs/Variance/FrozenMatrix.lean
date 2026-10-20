module

public import GMCExplicitDelta.Proofs.Variance.Matrix
public import GMCExplicitDelta.Proofs.Variance.Isotropy
public import GMCExplicitDelta.Coarse.Order

/-! # Matrix representation of normalized frozen probes -/

@[expose] public section

open MeasureTheory Matrix Homogenization Homogenization.Book SubdiffusiveProcess.CoarseGrainingVocab
open scoped MatrixOrder

namespace GMCExplicitDelta.Assembly

variable {d : ℕ}

/-- Normalization preserves positivity of both coarse matrices. -/
theorem frozenVar_frozen_posDef (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (U : Ch02.Domain d) (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    (frozenX M L U ω).PosDef ∧ (frozenY M L U ω).PosDef := by
  have ha := (aCutoffCoeffOnData M L ω U).isSymmetric
  exact ⟨(Coarse.XU_posDef ha).smul (inv_pos.mpr (driftSeed_ahom_pos M L)),
    (Coarse.YU_posDef ha).smul (driftSeed_ahom_pos M L)⟩

/-- Every self-probe is exactly the quadratic form of the defect matrix. -/
theorem frozenVar_frozenJ_eq_qf (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (U : Ch02.Domain d) (ω : SubdiffusiveProcess.Model.PotentialSample d) (e : Homogenization.Vec d) :
    frozenJ M L U e e ω = Coarse.qf (frozenDefect M L U ω) e := by
  have hs := Real.sq_sqrt (driftSeed_ahom_pos M L).le
  have hs0 := (Real.sqrt_pos.mpr (driftSeed_ahom_pos M L)).ne'
  rw [frozenJ, cutoffResponseJ_eq_randomMatrixQuadratics]
  simp only [matVecMul_smul, vecDot_smul_left, vecDot_smul_right]
  change _ = _
  unfold frozenDefect Coarse.qf frozenX frozenY
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, dotProduct_add]
  have hsq : (Real.sqrt (ahom M L))⁻¹ ^ 2 = (ahom M L)⁻¹ := by rw [inv_pow, hs]
  have hcancel := inv_mul_cancel₀ hs0
  change _ = (1 / 2 : ℝ) * ((ahom M L)⁻¹ * Coarse.qf (randomAMatrix M L U ω) e +
    ahom M L * Coarse.qf (randomAStarMatrix M L U ω)⁻¹ e) - vecNormSq e
  calc
    _ = (1 / 2 : ℝ) * ((Real.sqrt (ahom M L))⁻¹ ^ 2 * Coarse.qf (randomAMatrix M L U ω) e +
      Real.sqrt (ahom M L) ^ 2 * Coarse.qf (randomAStarMatrix M L U ω)⁻¹ e) -
      ((Real.sqrt (ahom M L))⁻¹ * Real.sqrt (ahom M L)) * vecNormSq e := by
        simp only [Coarse.vecDot_matVecMul_eq, Localization.cellMoment_vecDot_self]
        ring
    _ = _ := by rw [hsq, hs, hcancel, one_mul]

/-- The frozen defect is positive semidefinite. -/
theorem frozenVar_frozenDefect_posSemidef (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (U : Ch02.Domain d) (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    (frozenDefect M L U ω).PosSemidef := by
  have hpos := frozenVar_frozen_posDef M L U ω
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    ((hpos.1.isHermitian.add hpos.2.isHermitian).smul (by norm_num : star (1 / 2 : ℝ) = 1 / 2)
      |>.sub Matrix.isHermitian_one) ?_
  intro e
  simp only [star_trivial]
  change 0 ≤ Coarse.qf (frozenDefect M L U ω) e
  rw [← frozenVar_frozenJ_eq_qf]
  exact (Ch02.responseJ_nonneg U (aCutoffCoeffOnData M L ω U).toCoeffOn
      ((Real.sqrt (ahom M L))⁻¹ • e) (Real.sqrt (ahom M L) • e))

/-- The scalar probe supremum is the operator norm of the positive defect. -/
theorem frozenVar_defect_eq_opNorm (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (U : Ch02.Domain d) (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    normalizedDefect M L U ω = ENNReal.ofReal (Ch02.matrixOperatorNorm (frozenDefect M L U ω)) := by
  let : NeZero d := ⟨by have := M.shellPrefix.dimension; omega⟩
  exact paperScalarProbeMaxOn_eq_ofReal_matrixOperatorNorm U
    (aCutoffCoeffOnData M L ω U).toCoeffOn (ahom M L) (frozenDefect M L U ω)
    (frozenVar_frozenDefect_posSemidef M L U ω) (frozenVar_frozenJ_eq_qf M L U ω)

/-- The squared defect is controlled by the square of its scalar maximum. -/
theorem frozenVar_defect_frobSq_le (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (U : Ch02.Domain d) (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    frobSq (frozenDefect M L U ω) ≤ (d : ℝ) * (normalizedDefect M L U ω).toReal ^ 2 := by
  rw [frozenVar_defect_eq_opNorm, ENNReal.toReal_ofReal (Ch02.matrixOperatorNorm_nonneg _)]
  exact frozenVar_frobSq_le_dim_opNorm_sq _

/-- The normalized matrices retain the inverse-order trace bound. -/
theorem frozenVar_dimension_le_frozen_trace_mul (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (U : Ch02.Domain d) (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    (d : ℝ) ≤ Matrix.trace (frozenX M L U ω * frozenY M L U ω) := by
  let a := (aCutoffCoeffOnData M L ω U).toCoeffOn
  have ha : Ch02.CoeffOn.IsSymmetric a := (aCutoffCoeffOnData M L ω U).isSymmetric
  have hdiff : (Coarse.YU U a - (Coarse.XU U a)⁻¹).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      ((Coarse.YU_posDef ha).isHermitian.sub (Coarse.XU_posDef ha).inv.isHermitian)
    intro x
    have h := Coarse.matLoewnerLE_iff_qf.mp (Coarse.XU_inv_le_YU ha) x
    simpa only [star_trivial, Matrix.sub_mulVec, dotProduct_sub, sub_nonneg,
      Coarse.qf] using h
  have h := frozenVar_dimension_le_trace_mul (Coarse.XU_posDef ha) hdiff
  change (d : ℝ) ≤ Matrix.trace (((ahom M L)⁻¹ • Coarse.XU U a) *
    (ahom M L • Coarse.YU U a))
  simpa only [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    mul_inv_cancel₀ (driftSeed_ahom_pos M L).ne', one_smul] using h

end GMCExplicitDelta.Assembly
