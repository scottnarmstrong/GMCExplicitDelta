module

public import GMCExplicitDelta.Proofs.FreshMean.Means

/-! # C10: equality of planar annealed normalized primal and dual means -/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book

namespace GMCExplicitDelta.Assembly

/-- Finite-volume planar duality and the Dykhne normalization equate the two trace means. -/
theorem annealedMean_alpha_eq_beta_planar (M : SubdiffusiveProcess.Model.GMCModel 2) (L n : ℕ) :
    alphaMean M L n = betaMean M L n := by
  have ha := driftSeed_ahom_pos M L
  have hnorm := ahom_eq_planarLambda_of_streamFunction M L
    planarZeroNormalStreamFunctionOn_openCubeSet_originCube ha
  have hmat := abar_eq_planarLambda_sq_smul_abarStarInv_of_streamFunction M L (n : ℤ)
    (planarZeroNormalStreamFunctionOn_openCubeSet_originCube (n : ℤ))
  rw [← hnorm] at hmat
  rw [freshRet_alpha_eq, freshRet_beta_eq]
  unfold abarScalarReadout
  rw [hmat, Matrix.trace_smul, smul_eq_mul]
  field_simp [ha.ne']

end GMCExplicitDelta.Assembly

namespace GMCExplicitDelta.Localization

open Assembly Contract

variable {d : ℕ}

/-- C10, with the exact localization statement. -/
theorem alpha_eq_beta_planar_proof (M : SubdiffusiveProcess.Model.GMCModel d) (hd : d = 2) {D F : ℝ}
    (L : ℕ) (hP : InductionP M L D F) (n : ℕ) (hn : L ≤ n) :
    alphaMean M L n = betaMean M L n := by
  have _hn := hn
  subst d
  exact annealedMean_alpha_eq_beta_planar M L n

end GMCExplicitDelta.Localization
