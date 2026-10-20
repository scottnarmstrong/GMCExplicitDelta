module

public import GMCExplicitDelta.Assembly.ModelFrozen
public import SubdiffusiveProcess.Section5.HomogenizedCoefficientReciprocalLower
public import GMCExplicitDelta.Coarse.Symmetric
public import GMCExplicitDelta.Averaging.MatrixAverageCaps

/-! # The frozen defect as a positive semidefinite matrix -/

@[expose] public section

open MeasureTheory Matrix Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open GMCExplicitDelta.Insertion GMCExplicitDelta.Averaging
open scoped ENNReal BigOperators

namespace GMCExplicitDelta.Assembly

variable {d : ℕ}

/-- Quadratic probes of the frozen matrix are precisely the frozen response. -/
theorem frozenDefect_qf (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (U : Ch02.Domain d) (ω : SubdiffusiveProcess.Model.PotentialSample d) (e : Homogenization.Vec d) :
    Coarse.qf (frozenDefect M L U ω) e = frozenJ M L U e e ω := by
  have hhom : 0 < ahom M L := (Real.exp_pos _).trans_le
    (SubdiffusiveProcess.Section5.homogenized_coefficient_reciprocal_lower M L)
  have hs : Real.sqrt (ahom M L) ≠ 0 := (Real.sqrt_pos.mpr hhom).ne'
  have hs2 : (Real.sqrt (ahom M L)) ^ 2 = ahom M L := Real.sq_sqrt hhom.le
  unfold frozenJ J
  rw [Coarse.responseJ_eq_XY (aCutoffCoeffOnData M L ω U).isSymmetric,
    Coarse.posDef_qf_smul, Coarse.posDef_qf_smul]
  unfold frozenDefect frozenX frozenY Coarse.qf Coarse.XU Coarse.YU
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, dotProduct_add, smul_dotProduct, smul_eq_mul,
    inv_pow, hs2]
  field_simp

theorem sphereQuadratic_frozenDefect (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (U : Ch02.Domain d) (ω : SubdiffusiveProcess.Model.PotentialSample d)
    (e : EuclideanSpace ℝ (Fin d)) :
    sphereQuadratic (frozenDefect M L U ω) e = frozenJ M L U e.ofLp e.ofLp ω := by
  rw [← frozenDefect_qf M L]
  simp only [sphereQuadratic, Matrix.inner_toEuclideanCLM, Coarse.qf]

theorem frozenDefect_isHermitian (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (U : Ch02.Domain d) (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    (frozenDefect M L U ω).IsHermitian := by
  unfold frozenDefect frozenX frozenY
  apply Matrix.IsHermitian.sub _ Matrix.isHermitian_one
  apply Matrix.IsHermitian.smul _ (by rfl)
  apply Matrix.IsHermitian.add
  · exact (Coarse.XU_posDef (aCutoffCoeffOnData M L ω U).isSymmetric).isHermitian.smul (by rfl)
  · exact (Coarse.YU_posDef (aCutoffCoeffOnData M L ω U).isSymmetric).isHermitian.smul (by rfl)

theorem frozenDefect_posSemidef (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (U : Ch02.Domain d) (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    (frozenDefect M L U ω).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (frozenDefect_isHermitian M L U ω) ?_
  intro e
  simp only [star_trivial]
  change 0 ≤ Coarse.qf (frozenDefect M L U ω) e
  rw [frozenDefect_qf M L]
  exact Ch02.responseJ_nonneg _ _ _ _

/-- For PSD matrices, the top Rayleigh value is the Euclidean operator norm. -/
theorem sphereTop_eq_opNorm_of_posSemidef {A : Matrix (Fin d) (Fin d) ℝ} [NeZero d]
    (hA : A.PosSemidef) : sphereTop A = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ := by
  apply le_antisymm (sphereTop_le_opNorm A)
  have hh := psd_opNorm_le_constant_add (H := 0) hA (sphereTop_nonneg hA)
    (fun u hu => by
      have hq := le_csSup (sphereTop_bddAbove A)
        (show sphereQuadratic A u ∈ sphereQuadratic A '' Metric.sphere 0 1 from
          ⟨u, mem_sphere_zero_iff_norm.mpr hu, rfl⟩)
      change sphereQuadratic A u ≤ sphereTop A at hq
      simpa only [sphereQuadratic, map_zero, _root_.zero_apply,
        inner_zero_right, add_zero] using hq)
  simpa only [map_zero, norm_zero, add_zero] using hh

/-- Identification of the public ENNReal sphere supremum with the matrix operator norm. -/
theorem normalizedDefect_eq_ofReal_opNorm [NeZero d]
    (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    normalizedDefect M L U ω =
      ENNReal.ofReal (‖Matrix.toEuclideanCLM (𝕜 := ℝ) (frozenDefect M L U ω)‖) := by
  have hPSD := frozenDefect_posSemidef M L U ω
  obtain ⟨v, hv, he⟩ := exists_unit_top_eigenvector hPSD
  have hq : sphereQuadratic (frozenDefect M L U ω) v =
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (frozenDefect M L U ω)‖ := by
    rw [sphereQuadratic, he, inner_smul_right, real_inner_self_eq_norm_sq, hv, one_pow,
      mul_one, sphereTop_eq_opNorm_of_posSemidef hPSD]
  unfold normalizedDefect paperScalarProbeMaxOn
  apply le_antisymm
  · apply iSup_le
    intro e
    change ENNReal.ofReal (frozenJ M L U e.val e.val ω) ≤ _
    rw [← frozenDefect_qf M L]
    have hu : ‖WithLp.toLp 2 e.val‖ = 1 := by
      have hsq : ‖WithLp.toLp 2 e.val‖ ^ 2 = vecNormSq e.val := by
        exact Ch02.vecNorm_sq_eq_vecNormSq e.val
      rw [e.property] at hsq
      nlinarith only [hsq, norm_nonneg (WithLp.toLp 2 e.val)]
    have hb := abs_sphereQuadratic_le (frozenDefect M L U ω) (WithLp.toLp 2 e.val)
    rw [hu, one_pow, mul_one] at hb
    apply ENNReal.ofReal_le_ofReal
    simpa only [sphereQuadratic, Matrix.inner_toEuclideanCLM, PiLp.toLp_apply,
      star_trivial, Coarse.qf] using (le_abs_self _).trans hb
  · have heunit : vecNormSq v.ofLp = 1 := by
      have hh : vecNormSq v.ofLp = ‖v‖ ^ 2 := (Ch02.vecNorm_sq_eq_vecNormSq v.ofLp).symm
      rw [hh, hv, one_pow]
    apply le_iSup_of_le ⟨v.ofLp, heunit⟩
    change _ ≤ ENNReal.ofReal (frozenJ M L U v.ofLp v.ofLp ω)
    rw [← sphereQuadratic_frozenDefect M L U ω v, hq]

end GMCExplicitDelta.Assembly
