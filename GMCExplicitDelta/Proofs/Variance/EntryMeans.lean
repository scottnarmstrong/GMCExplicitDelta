module

public import GMCExplicitDelta.Proofs.Variance.CellMoments

/-! # Entrywise isotropic means of the frozen matrices on cells -/

@[expose] public section

open MeasureTheory Matrix Homogenization Homogenization.Book SubdiffusiveProcess.CoarseGrainingVocab
open scoped Matrix.Norms.Elementwise

namespace GMCExplicitDelta.Assembly

variable {d : ℕ}

theorem frozenVar_integral_X_entry (M : SubdiffusiveProcess.Model.GMCModel d) (L k : ℕ)
    (R : Homogenization.TriadicCube d) (hR : R.scale = (k : ℤ)) (i j : Fin d) :
    (∫ ω, frozenX M L (cellAt 0 R) ω i j ∂M.P.toMeasure) =
      (alphaMean M L k • (1 : Homogenization.Mat d)) i j := by
  change (∫ ω, (ahom M L)⁻¹ * randomAMatrix M L (cellAt 0 R) ω i j ∂M.P.toMeasure) = _
  rw [integral_const_mul, ← integral_matrix_apply (integrable_randomAMatrix M L (cellAt 0 R)) i j]
  change (ahom M L)⁻¹ * (abar M L (cellAt 0 R)) i j = _
  rw [Localization.cellMoment_abar_cell M L k R hR, freshRet_alpha_eq]
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

theorem frozenVar_integral_Y_entry (M : SubdiffusiveProcess.Model.GMCModel d) (L k : ℕ)
    (R : Homogenization.TriadicCube d) (hR : R.scale = (k : ℤ)) (i j : Fin d) :
    (∫ ω, frozenY M L (cellAt 0 R) ω i j ∂M.P.toMeasure) =
      (betaMean M L k • (1 : Homogenization.Mat d)) i j := by
  change (∫ ω, ahom M L * (randomAStarMatrix M L (cellAt 0 R) ω)⁻¹ i j ∂M.P.toMeasure) = _
  rw [integral_const_mul, ← integral_matrix_apply (integrable_randomAStarMatrix_inv M L (cellAt 0 R)) i j]
  change ahom M L * (abarStarInv M L (cellAt 0 R)) i j = _
  rw [Localization.cellMoment_abarStarInv_cell M L k R hR, Localization.cellMoment_beta_scalar]
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

theorem frozenVar_integral_defect_entry (M : SubdiffusiveProcess.Model.GMCModel d) (L k : ℕ)
    (R : Homogenization.TriadicCube d) (hR : R.scale = (k : ℤ)) (i j : Fin d) :
    (∫ ω, frozenDefect M L (cellAt 0 R) ω i j ∂M.P.toMeasure) =
      (fMean M L k • (1 : Homogenization.Mat d)) i j := by
  have hx : Integrable (fun ω => frozenX M L (cellAt 0 R) ω i j) M.P.toMeasure :=
    (Localization.cellMoment_frozenX_entry_memLp M L (cellAt 0 R) i j).integrable (by norm_num)
  have hy : Integrable (fun ω => frozenY M L (cellAt 0 R) ω i j) M.P.toMeasure :=
    (Localization.cellMoment_frozenY_entry_memLp M L (cellAt 0 R) i j).integrable (by norm_num)
  have hsum : Integrable (fun ω => frozenX M L (cellAt 0 R) ω i j +
      frozenY M L (cellAt 0 R) ω i j) M.P.toMeasure := hx.add hy
  change (∫ ω, (1 / 2 : ℝ) * (frozenX M L (cellAt 0 R) ω i j +
      frozenY M L (cellAt 0 R) ω i j) - (1 : Homogenization.Mat d) i j ∂M.P.toMeasure) = _
  rw [integral_sub (hsum.const_mul (1 / 2 : ℝ)) (integrable_const _), integral_const_mul,
    integral_add hx hy, integral_const, frozenVar_integral_X_entry M L k R hR i j,
    frozenVar_integral_Y_entry M L k R hR i j]
  simp only [probReal_univ, Matrix.smul_apply, smul_eq_mul, fMean]
  ring

theorem frozenVar_frozenDefect_cell_translate (M : SubdiffusiveProcess.Model.GMCModel d) (L k : ℕ)
    (R : Homogenization.TriadicCube d) (hR : R.scale = (k : ℤ))
    (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    frozenDefect M L (cellAt 0 R) ω =
      frozenDefect M L (cubeAt 0 k) (translatePotentialSequence (triadicCubeShift R) ω) := by
  unfold frozenDefect
  rw [frozenVar_frozenX_cell_translate M L k R hR, frozenVar_frozenY_cell_translate M L k R hR]

end GMCExplicitDelta.Assembly
