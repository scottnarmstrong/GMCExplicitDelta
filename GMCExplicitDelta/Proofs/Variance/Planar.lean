module

public import GMCExplicitDelta.Proofs.Variance.VarianceTools
public import GMCExplicitDelta.Proofs.AnnealedMeans.Planar

/-! # Equality of the two planar Frobenius variances -/

@[expose] public section

open MeasureTheory Matrix Homogenization Homogenization.Book SubdiffusiveProcess.CoarseGrainingVocab
open scoped Matrix.Norms.Elementwise

namespace GMCExplicitDelta.Assembly

/-- Planar duality exchanges the normalized matrices samplewise. -/
theorem frozenVar_planar_X_dual (M : SubdiffusiveProcess.Model.GMCModel 2) (L n : ℕ)
    (ω : SubdiffusiveProcess.Model.PotentialSample 2) :
    frozenX M L (cubeAt 0 n)
      (planarDualPotentialSample planarQuarterTurn planarQuarterTurn_isSignedPermutation ω) =
    frozenY M L (cubeAt 0 n) ω := by
  have ha := driftSeed_ahom_pos M L
  have hn := ahom_eq_planarLambda_of_streamFunction M L
    planarZeroNormalStreamFunctionOn_openCubeSet_originCube ha
  change (ahom M L)⁻¹ • randomAMatrix M L (cubeAt 0 n)
    (planarDualPotentialSample planarQuarterTurn planarQuarterTurn_isSignedPermutation ω) =
    ahom M L • (randomAStarMatrix M L (cubeAt 0 n) ω)⁻¹
  rw [freshRet_cubeAt_zero, randomAMatrix_planarDualPotentialSample_of_streamFunction M L (n : ℤ)
    (planarZeroNormalStreamFunctionOn_openCubeSet_originCube (n : ℤ)), ← hn, smul_smul]
  congr 1
  field_simp

/-- The two centered planar matrices have equal mean Frobenius square. -/
theorem frozenVar_planar_variances_eq (M : SubdiffusiveProcess.Model.GMCModel 2) (L n : ℕ) :
    (∫ ω, frobSq (frozenX M L (cubeAt 0 n) ω - alphaMean M L n • (1 : Homogenization.Mat 2))
      ∂M.P.toMeasure) =
    ∫ ω, frobSq (frozenY M L (cubeAt 0 n) ω - betaMean M L n • (1 : Homogenization.Mat 2))
      ∂M.P.toMeasure := by
  have hF : Integrable (fun ω =>
      frobSq (frozenX M L (cubeAt 0 n) ω - alphaMean M L n • (1 : Homogenization.Mat 2)))
      M.P.toMeasure :=
    Localization.cellMoment_integrable_frobSq (fun i j =>
      (Localization.cellMoment_frozenX_entry_memLp M L (cubeAt 0 n) i j).sub (memLp_const _))
  have hstat := integral_comp_eq_of_map_eq
    (measurable_planarDualPotentialSample planarQuarterTurn planarQuarterTurn_isSignedPermutation)
    (potentialSequenceLaw_planarDual M planarQuarterTurn planarQuarterTurn_isSignedPermutation)
    _ hF.aestronglyMeasurable
  rw [← hstat]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω => by
    dsimp only
    rw [frozenVar_planar_X_dual M L n ω, annealedMean_alpha_eq_beta_planar M L n]

end GMCExplicitDelta.Assembly
