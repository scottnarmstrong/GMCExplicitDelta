module

public import GMCExplicitDelta.Proofs.CellMoments.DualSymmetry

/-! # Cell residual variance controlled by the frozen variance -/

@[expose] public section

open MeasureTheory Homogenization Homogenization.Book SubdiffusiveProcess.CoarseGrainingVocab
open scoped Matrix.Norms.Elementwise

namespace GMCExplicitDelta.Localization

open Assembly Contract

variable {d : ℕ}

/-- Entrywise second moments make the squared Frobenius norm integrable. -/
theorem cellMoment_integrable_frobSq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {A : Ω → Homogenization.Mat d} (hA : ∀ i j, MemLp (fun ω => A ω i j) 2 μ) :
    Integrable (fun ω => frobSq (A ω)) μ :=
  integrable_finsetSum Finset.univ fun i _ => integrable_finsetSum Finset.univ fun j _ =>
    (memLp_two_iff_integrable_sq (hA i j).aestronglyMeasurable).1 (hA i j)

/-- A centered dual flux has integrable squared norm on any domain. -/
theorem cellMoment_integrable_centered_flux (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (U : Ch02.Domain d) (q : Homogenization.Vec d) (b : ℝ) :
    Integrable (fun ω => vecNormSq ((frozenY M L U ω).mulVec q - b • q)) M.P.toMeasure := by
  simpa only [neg_zero, zero_add] using cellMoment_integrable_residual M L U 0 q (b • q)

/-- Stationarity transports centered dual flux second moments to the centered cube. -/
theorem cellMoment_cell_flux_stationary (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    (R : Homogenization.TriadicCube d) (hR : R.scale = (n : ℤ)) (q : Homogenization.Vec d) (b : ℝ) :
    ∫ ω, vecNormSq ((frozenY M L (cellAt 0 R) ω).mulVec q - b • q) ∂M.P.toMeasure =
      ∫ ω, vecNormSq ((frozenY M L (cubeAt 0 n) ω).mulVec q - b • q) ∂M.P.toMeasure := by
  have hY (ω : SubdiffusiveProcess.Model.PotentialSample d) :
      frozenY M L (cellAt 0 R) ω =
        frozenY M L (cubeAt 0 n) (translatePotentialSequence (triadicCubeShift R) ω) := by
    unfold frozenY
    rw [cellMoment_cellAt_zero, freshRet_cubeAt_zero]
    change ahom M L • (randomAStarMatrix M L (Ch02.cubeDomain R) ω)⁻¹ = _
    rw [randomAStarInv_cube_eq_originCube_translate, hR]
    rfl
  calc
    _ = ∫ ω, vecNormSq ((frozenY M L (cubeAt 0 n)
        (translatePotentialSequence (triadicCubeShift R) ω)).mulVec q - b • q) ∂M.P.toMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω =>
        congrArg (fun A : Homogenization.Mat d => vecNormSq (A.mulVec q - b • q)) (hY ω)
    _ = _ := integral_comp_eq_of_map_eq (measurable_translatePotentialSequence (triadicCubeShift R))
      (potentialSequenceLaw_stationary M (triadicCubeShift R)) _
      (cellMoment_integrable_centered_flux M L (cubeAt 0 n) q b).aestronglyMeasurable

/-- Isotropy identifies the directional variance with the normalized Frobenius variance. -/
theorem cellMoment_centered_flux_eq_trace (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    (q : Homogenization.Vec d) (b : ℝ) :
    ∫ ω, vecNormSq ((frozenY M L (cubeAt 0 n) ω).mulVec q - b • q) ∂M.P.toMeasure =
      vecNormSq q / d * ∫ ω,
        frobSq (frozenY M L (cubeAt 0 n) ω - b • (1 : Homogenization.Mat d)) ∂M.P.toMeasure := by
  let : NeZero d := neZero_of_gmcModel M
  have h := cellMoment_integral_normSq_of_scalar_gram (cellMoment_centeredY_memLp M L (cubeAt 0 n) b)
    (cellMoment_centeredY_gram_scalar M L n b) q
  simpa only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] using h

/-- The dual Frobenius term is bounded by the stacked variance with its dimension factor. -/
theorem cellMoment_dual_variance_le (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    (q : Homogenization.Vec d) :
    vecNormSq q / d * ∫ ω,
        frobSq (frozenY M L (cubeAt 0 n) ω - betaMean M L n • (1 : Homogenization.Mat d)) ∂M.P.toMeasure ≤
      varFactor d * vecNormSq q * varV M L n := by
  have hd : 0 < (d : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension
  have hY := cellMoment_integrable_frobSq (cellMoment_centeredY_memLp M L (cubeAt 0 n) (betaMean M L n))
  have hX : Integrable (fun ω =>
      frobSq (frozenX M L (cubeAt 0 n) ω - alphaMean M L n • (1 : Homogenization.Mat d))) M.P.toMeasure :=
    cellMoment_integrable_frobSq (A := fun ω =>
      frozenX M L (cubeAt 0 n) ω - alphaMean M L n • (1 : Homogenization.Mat d)) (fun i j =>
    (cellMoment_frozenX_entry_memLp M L (cubeAt 0 n) i j).sub
      (memLp_const ((alphaMean M L n • (1 : Homogenization.Mat d)) i j)))
  unfold varFactor varV
  split_ifs with hdim
  · have hd2 : (d : ℝ) = 2 := by exact_mod_cast hdim
    rw [hd2]
    apply le_of_eq
    ring
  · rw [integral_add hX hY]
    have hpos : 0 ≤ ∫ ω,
        frobSq (frozenX M L (cubeAt 0 n) ω - alphaMean M L n • (1 : Homogenization.Mat d)) ∂M.P.toMeasure :=
      integral_nonneg fun _ => frobSq_nonneg _
    have hmul := mul_nonneg (div_nonneg (vecNormSq_nonneg q) hd.le) hpos
    have heq (x y : ℝ) : 2 * vecNormSq q * (1 / (2 * (d : ℝ)) * (x + y)) =
        vecNormSq q / d * x + vecNormSq q / d * y := by
      field_simp [hd.ne']
    rw [heq]
    exact le_add_of_nonneg_left hmul

/-- C8 second moments with the exact localization statement. -/
theorem integral_cellRes_le_proof (M : SubdiffusiveProcess.Model.GMCModel d) {D F : ℝ} (L : ℕ)
    (hP : InductionP M L D F) (n : ℕ) (hn : L ≤ n) (R : Homogenization.TriadicCube d)
    (hR : R.scale = (n : ℤ)) (q : Homogenization.Vec d) :
    ∫ ω, vecNormSq ((frozenY M L (cellAt 0 R) ω).mulVec q - betaMean M L n • q) ∂M.P.toMeasure ≤
      varFactor d * vecNormSq q * varV M L n := by
  have _hP := hP
  have _hn := hn
  rw [cellMoment_cell_flux_stationary M L n R hR, cellMoment_centered_flux_eq_trace]
  exact cellMoment_dual_variance_le M L n q

end GMCExplicitDelta.Localization
