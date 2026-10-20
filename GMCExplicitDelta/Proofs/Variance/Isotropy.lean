module

public import GMCExplicitDelta.Proofs.CellMoments.Means

/-! # Stationary isotropic frozen mean on every translated cube -/

@[expose] public section

open MeasureTheory Homogenization Homogenization.Book SubdiffusiveProcess.CoarseGrainingVocab

namespace GMCExplicitDelta.Assembly

variable {d : ℕ}

theorem frozenJ_cube_translate (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    (z p q : Homogenization.Vec d) (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    frozenJ M L (cubeAt z n) p q ω =
      frozenJ M L (cubeAt 0 n) p q (translatePotentialSequence z ω) := by
  unfold frozenJ J
  rw [Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ,
    Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ]
  rw [freshRet_cubeAt_zero]
  change ResponseJ (translateSet z (openCubeSet (originCube d (n : ℤ)))) _ _ _ = _
  rw [ResponseJ_translateSet_eq_translateCoeffField]
  apply congrArg (ResponseJ (openCubeSet (originCube d (n : ℤ)))
    ((Real.sqrt (ahom M L))⁻¹ • p) (Real.sqrt (ahom M L) • q))
  funext x
  exact congrArg scalarMatrix (aCutoff_translatePotentialSequence M L z ω x).symm

theorem lintegral_frozenJ_eq_fMean_proof (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    (z e : Homogenization.Vec d) (he : vecNormSq e = 1) :
    ∫⁻ ω, ENNReal.ofReal (frozenJ M L (cubeAt z n) e e ω) ∂M.P.toMeasure =
      ENNReal.ofReal (fMean M L n) := by
  have hint : Integrable (frozenJ M L (cubeAt z n) e e) M.P.toMeasure := integrable_cutoffResponseJ
    M L (cubeAt z n) ((Real.sqrt (ahom M L))⁻¹ • e) (Real.sqrt (ahom M L) • e)
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun ω => Ch02.responseJ_nonneg _ _ _ _)]
  have hstat : (∫ ω, frozenJ M L (cubeAt z n) e e ω ∂M.P.toMeasure) =
      ∫ ω, frozenJ M L (cubeAt 0 n) e e ω ∂M.P.toMeasure := by
    simp_rw [frozenJ_cube_translate M L n z e e]
    exact integral_comp_eq_of_map_eq (measurable_translatePotentialSequence z)
      (potentialSequenceLaw_stationary M z) _
      (integrable_cutoffResponseJ
        M L (cubeAt 0 n) ((Real.sqrt (ahom M L))⁻¹ • e)
        (Real.sqrt (ahom M L) • e)).aestronglyMeasurable
  rw [hstat]
  have hmean := Localization.cellMoment_integral_frozenJ M L n (originCube d (n : ℤ)) rfl e e
  change ENNReal.ofReal _ = _
  rw [show cubeAt (0 : Homogenization.Vec d) n = cellAt 0 (originCube d (n : ℤ)) from rfl,
    hmean]
  unfold Localization.meanJ fMean
  rw [he, show vecDot e e = 1 from he]
  congr 1
  ring

end GMCExplicitDelta.Assembly
