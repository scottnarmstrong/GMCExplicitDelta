module

public import GMCExplicitDelta.Proofs.Variance.Initial
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.FullBlockDilationReadout

/-! # Positively thickened local representatives of the frozen matrices -/

@[expose] public section

open MeasureTheory Matrix Homogenization Homogenization.Book SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion

namespace GMCExplicitDelta.Assembly

variable {d : ℕ}

theorem frozenVar_primal_eq_block (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) (R : Homogenization.TriadicCube d) :
    (coarseBlockMatrix (cubeSet R) (aCutoffRegCoeffField M L ω).toFun).upperLeft =
      randomAMatrix M L (Ch02.cubeDomain R) ω := by
  let : NeZero d := neZero_of_gmcModel M
  rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube]
  let U := Ch02.cubeDomain R
  let hdata := aCutoffCoeffOnData M L ω U
  have heq := eq_coarseBlockMatrix_of_isCoarseBlockMatrix (isCoarseBlockMatrix_ch02_aCutoff M L ω R)
  have ht := Ch02.responseSymmetricDirichletNeumannTheory U hdata.toCoeffOn hdata.isSymmetric
  change (coarseBlockMatrix (openCubeSet R)
    (scalarCoeffField (SubdiffusiveProcess.Model.aCutoff M L ω))).upperLeft = _
  rw [← heq, Ch02.coarseBlockMatrix_upperLeft]
  exact ht.derived_matrices.2.2.trans ht.derived_matrices.1.symm

theorem frozenVar_rawX_local (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (R : Homogenization.TriadicCube d) (i j : Fin d) :
    ∃ Y : SubdiffusiveProcess.Model.PotentialSample d → ℝ,
      @Measurable _ ℝ ((LocalSigmaR
        (Metric.thickening (responseRestrictionBridgeRadius d) (cubeSet R))).comap
        (aCutoffRegCoeffField M L)) _ Y ∧
      (fun ω => randomAMatrix M L (Ch02.cubeDomain R) ω i j) =ᵐ[M.P.toMeasure] Y := by
  let A := aCutoffRegCoeffField M L
  obtain ⟨Y0, hlocal, heq⟩ := (aCutoffRestrictionLaw_lawCarrier M L)
    |>.exists_isRestrictionLocalRandomVariable_ae_eq_coarseBlockMatrix_upperLeft_apply_cubeSet R i j
  refine ⟨Y0 ∘ A, ?_, ?_⟩
  · have hcomp : @Measurable _ ℝ
        ((RestrictionSigmaR (cubeSet R) (measurableSet_cubeSet R)).comap A) _ (Y0 ∘ A) :=
      hlocal.comp (Measurable.of_comap_le le_rfl)
    exact hcomp.mono (comap_restrictionSigmaR_le_comap_localSigmaR_thickening A
      (fun ω u v => continuous_aCutoffRegCoeffField_entry_for_response M L ω u v)
      (cubeSet R) (measurableSet_cubeSet R) (responseRestrictionBridgeRadius d)
      (responseRestrictionBridgeRadius_pos d)) le_rfl
  · have hpull := ae_eq_comp (measurable_aCutoffRegCoeffField M L).aemeasurable
      (by simpa only [aCutoffRestrictionLaw_eq_map] using heq)
    filter_upwards [hpull] with ω hω
    rw [← frozenVar_primal_eq_block M L ω R]
    exact hω

theorem frozenVar_frozenX_local (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (R : Homogenization.TriadicCube d) (i j : Fin d) :
    ∃ Y : SubdiffusiveProcess.Model.PotentialSample d → ℝ,
      @Measurable _ ℝ ((LocalSigmaR
        (Metric.thickening (responseRestrictionBridgeRadius d) (cubeSet R))).comap
        (aCutoffRegCoeffField M L)) _ Y ∧
      (fun ω => frozenX M L (cellAt 0 R) ω i j) =ᵐ[M.P.toMeasure] Y := by
  obtain ⟨Y, hY, heq⟩ := frozenVar_rawX_local M L R i j
  refine ⟨fun ω => (ahom M L)⁻¹ * Y ω, measurable_const.mul hY, ?_⟩
  filter_upwards [heq] with ω hω
  rw [frozenX, Localization.cellMoment_cellAt_zero R]
  change (ahom M L)⁻¹ * randomAMatrix M L (Ch02.cubeDomain R) ω i j = _
  rw [hω]

theorem frozenVar_frozenY_local (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (R : Homogenization.TriadicCube d) (i j : Fin d) :
    ∃ Y : SubdiffusiveProcess.Model.PotentialSample d → ℝ,
      @Measurable _ ℝ ((LocalSigmaR
        (Metric.thickening (responseRestrictionBridgeRadius d) (cubeSet R))).comap
        (aCutoffRegCoeffField M L)) _ Y ∧
      (fun ω => frozenY M L (cellAt 0 R) ω i j) =ᵐ[M.P.toMeasure] Y := by
  let : NeZero d := neZero_of_gmcModel M
  obtain ⟨Y, hY, heq⟩ := exists_randomAStarInv_entry_thickenedLocal_ae_eq M L R i j
  refine ⟨fun ω => ahom M L * Y ω, measurable_const.mul hY, ?_⟩
  filter_upwards [heq] with ω hω
  rw [frozenY, Localization.cellMoment_cellAt_zero R]
  change ahom M L * (randomAStarMatrix M L (Ch02.cubeDomain R) ω)⁻¹ i j = _
  rw [hω]

theorem frozenVar_frozenDefect_local (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (R : Homogenization.TriadicCube d) (i j : Fin d) :
    ∃ Y : SubdiffusiveProcess.Model.PotentialSample d → ℝ,
      @Measurable _ ℝ ((LocalSigmaR
        (Metric.thickening (responseRestrictionBridgeRadius d) (cubeSet R))).comap
        (aCutoffRegCoeffField M L)) _ Y ∧
      (fun ω => frozenDefect M L (cellAt 0 R) ω i j) =ᵐ[M.P.toMeasure] Y := by
  obtain ⟨X, hX, heqX⟩ := frozenVar_frozenX_local M L R i j
  obtain ⟨Y, hY, heqY⟩ := frozenVar_frozenY_local M L R i j
  refine ⟨fun ω => (1 / 2 : ℝ) * (X ω + Y ω) - (1 : Homogenization.Mat d) i j,
    (measurable_const.mul (hX.add hY)).sub measurable_const, ?_⟩
  filter_upwards [heqX, heqY] with ω hx hy
  change (1 / 2 : ℝ) * (frozenX M L (cellAt 0 R) ω i j + frozenY M L (cellAt 0 R) ω i j) - _ = _
  rw [hx, hy]

end GMCExplicitDelta.Assembly
