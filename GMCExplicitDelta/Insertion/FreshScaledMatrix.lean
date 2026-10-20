module

public import GMCExplicitDelta.Proofs.Variance.FrozenMatrix
public import GMCExplicitDelta.Insertion.SpherePSD

/-! # The actual scaled defect matrix and its directional representation -/

@[expose] public section

open MeasureTheory Matrix Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal RealInnerProductSpace

namespace GMCExplicitDelta.Insertion

noncomputable def scaledMatrix {d : ℕ} (M : SubdiffusiveProcess.Model.GMCModel d)
    (m : ℕ) (U : Ch02.Domain d) (s : ℝ) (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    Matrix (Fin d) (Fin d) ℝ :=
  (1 / 2 : ℝ) • (s⁻¹ • randomAMatrix M m U ω + s • (randomAStarMatrix M m U ω)⁻¹) - 1

/-- The actual scaled self-probe is the quadratic form of the scaled matrix. -/
theorem scaled_response_eq_qf {d : ℕ} (M : SubdiffusiveProcess.Model.GMCModel d)
    (m : ℕ) (U : Ch02.Domain d) {s : ℝ} (hs : 0 < s)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) (e : Homogenization.Vec d) :
    Ch02.responseJ U (aCutoffCoeffOnData M m ω U).toCoeffOn
      ((Real.sqrt s)⁻¹ • e) (Real.sqrt s • e) = Coarse.qf (scaledMatrix M m U s ω) e := by
  have hsq := Real.sq_sqrt hs.le
  have hs0 := (Real.sqrt_pos.mpr hs).ne'
  change J U (aCutoffCoeffOnData M m ω U).toCoeffOn
    ((Real.sqrt s)⁻¹ • e) (Real.sqrt s • e) = _
  rw [cutoffResponseJ_eq_randomMatrixQuadratics]
  simp only [matVecMul_smul, vecDot_smul_left, vecDot_smul_right]
  unfold scaledMatrix Coarse.qf
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, dotProduct_add]
  have hsqInv : (Real.sqrt s)⁻¹ ^ 2 = s⁻¹ := by rw [inv_pow, hsq]
  have hcancel := inv_mul_cancel₀ hs0
  change _ = (1 / 2 : ℝ) * (s⁻¹ * Coarse.qf (randomAMatrix M m U ω) e +
    s * Coarse.qf (randomAStarMatrix M m U ω)⁻¹ e) - vecNormSq e
  calc
    _ = (1 / 2 : ℝ) * ((Real.sqrt s)⁻¹ ^ 2 * Coarse.qf (randomAMatrix M m U ω) e +
      Real.sqrt s ^ 2 * Coarse.qf (randomAStarMatrix M m U ω)⁻¹ e) -
      ((Real.sqrt s)⁻¹ * Real.sqrt s) * vecNormSq e := by
        simp only [Coarse.vecDot_matVecMul_eq, GMCExplicitDelta.Localization.cellMoment_vecDot_self]
        ring
    _ = _ := by rw [hsqInv, hsq, hcancel, one_mul]

/-- C4 applies to the actual scaled matrix. -/
theorem scaledMatrix_posSemidef {d : ℕ} (M : SubdiffusiveProcess.Model.GMCModel d)
    (m : ℕ) (U : Ch02.Domain d) {s : ℝ} (hs : 0 < s)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) : (scaledMatrix M m U s ω).PosSemidef := by
  have ha := (aCutoffCoeffOnData M m ω U).isSymmetric
  have hX := (Coarse.XU_posDef ha).smul (inv_pos.mpr hs)
  have hY := (Coarse.YU_posDef ha).smul hs
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    ((hX.isHermitian.add hY.isHermitian).smul (by norm_num : star (1 / 2 : ℝ) = 1 / 2)
      |>.sub Matrix.isHermitian_one) ?_
  intro e
  simp only [star_trivial]
  change 0 ≤ Coarse.qf (scaledMatrix M m U s ω) e
  rw [← scaled_response_eq_qf M m U hs]
  exact Ch02.responseJ_nonneg _ _ _ _

/-- Polarization makes matrix measurability follow from the existing probe construction. -/
theorem measurable_scaledMatrix {d : ℕ} [NeZero d] (M : SubdiffusiveProcess.Model.GMCModel d)
    (m : ℕ) (U : Ch02.Domain d) {s : ℝ} (hs : 0 < s) :
    Measurable (scaledMatrix M m U s) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  have hp (e : Homogenization.Vec d) : Measurable (fun ω =>
      Coarse.qf (scaledMatrix M m U s ω) e) := by
    simp_rw [← scaled_response_eq_qf M m U hs]
    exact measurable_cutoff_responseJ M m U _ _
  have heq (ω : SubdiffusiveProcess.Model.PotentialSample d) :
      scaledMatrix M m U s ω i j =
        (Coarse.qf (scaledMatrix M m U s ω) (Pi.single i 1 + Pi.single j 1) -
          Coarse.qf (scaledMatrix M m U s ω) (Pi.single i 1) -
          Coarse.qf (scaledMatrix M m U s ω) (Pi.single j 1)) / 2 := by
    have hA := (scaledMatrix_posSemidef M m U hs ω).isHermitian
    have hsym : scaledMatrix M m U s ω j i = scaledMatrix M m U s ω i j :=
      congrFun (congrFun (Matrix.isHermitian_iff_isSymm.mp hA) i) j
    simp only [Coarse.qf, Matrix.mulVec_add, dotProduct_add, add_dotProduct,
      Matrix.mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply]
    rw [hsym]
    ring
  simp_rw [heq]
  exact (((hp _).sub (hp _)).sub (hp _)).div_const 2

/-- The Euclidean and coordinate quadratic forms agree. -/
theorem sphereQuadratic_eq_qf {d : ℕ} (N : Matrix (Fin d) (Fin d) ℝ)
    (u : EuclideanSpace ℝ (Fin d)) : sphereQuadratic N u = Coarse.qf N (WithLp.ofLp u) := by
  simp only [sphereQuadratic, Matrix.inner_toEuclideanCLM, Coarse.qf]

/-- Euclidean unit vectors are exactly the unit probes in the coefficient vocabulary. -/
theorem vecNormSq_ofLp {d : ℕ} (u : EuclideanSpace ℝ (Fin d)) :
    vecNormSq (WithLp.ofLp u) = ‖u‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Real.norm_eq_abs, sq_abs]
  simp only [vecNormSq, vecDot, pow_two]

/-- The scalar maximum is bounded by the Rayleigh supremum of the actual matrix. -/
theorem scaledDefect_le_sphereTop {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) (U : Ch02.Domain d)
    {s : ℝ} (hs : 0 < s) (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    Assembly.scaledDefect M m U s ω ≤ ENNReal.ofReal (sphereTop (scaledMatrix M m U s ω)) := by
  apply iSup_le
  intro e
  apply ENNReal.ofReal_le_ofReal
  change Ch02.responseJ U (aCutoffCoeffOnData M m ω U).toCoeffOn
    ((Real.sqrt s)⁻¹ • e.1) (Real.sqrt s • e.1) ≤ _
  rw [scaled_response_eq_qf M m U hs]
  let u : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 e.1
  have hu : ‖u‖ = 1 := by
    have hsq : ‖u‖ ^ 2 = 1 := by rw [← vecNormSq_ofLp]; exact e.2
    nlinarith only [hsq, norm_nonneg u]
  change Coarse.qf (scaledMatrix M m U s ω) (WithLp.ofLp u) ≤ _
  rw [← sphereQuadratic_eq_qf]
  exact le_csSup (sphereTop_bddAbove (scaledMatrix M m U s ω))
    ⟨u, mem_sphere_zero_iff_norm.mpr hu, rfl⟩

end GMCExplicitDelta.Insertion
