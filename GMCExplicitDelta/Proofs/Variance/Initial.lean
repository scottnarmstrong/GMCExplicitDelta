module

public import GMCExplicitDelta.Proofs.Variance.Planar

/-! # Initial frozen variance estimate -/

@[expose] public section

open MeasureTheory Matrix Homogenization Homogenization.Book SubdiffusiveProcess.CoarseGrainingVocab
open scoped Matrix.Norms.Elementwise

namespace GMCExplicitDelta.Assembly

variable {d : ℕ}

theorem frozenVar_integrable_traceX (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (U : Ch02.Domain d) :
    Integrable (fun ω => Matrix.trace (frozenX M L U ω)) M.P.toMeasure :=
  integrable_finsetSum Finset.univ fun i _ =>
    (((integrable_randomAMatrix M L U).eval i).eval i).const_mul (ahom M L)⁻¹

theorem frozenVar_integrable_traceY (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (U : Ch02.Domain d) :
    Integrable (fun ω => Matrix.trace (frozenY M L U ω)) M.P.toMeasure :=
  integrable_finsetSum Finset.univ fun i _ =>
    (((integrable_randomAStarMatrix_inv M L U).eval i).eval i).const_mul (ahom M L)

theorem frozenVar_integrable_traceDefect (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (U : Ch02.Domain d) :
    Integrable (fun ω => Matrix.trace (frozenDefect M L U ω)) M.P.toMeasure := by
  have h := (((frozenVar_integrable_traceX M L U).add (frozenVar_integrable_traceY M L U)).const_mul
    (1 / 2 : ℝ)).sub (integrable_const (d : ℝ))
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only [frozenDefect, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_add,
    Matrix.trace_one, Fintype.card_fin, smul_eq_mul, Pi.add_apply, Pi.sub_apply]

theorem frozenVar_defect_entry_memLp (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (U : Ch02.Domain d) (i j : Fin d) :
    MemLp (fun ω => frozenDefect M L U ω i j) 2 M.P.toMeasure :=
  (((Localization.cellMoment_frozenX_entry_memLp M L U i j).add
    (Localization.cellMoment_frozenY_entry_memLp M L U i j)).const_mul (1 / 2 : ℝ)).sub
    (memLp_const _)

theorem frozenVar_trace_defect_mean (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) :
    (∫ ω, Matrix.trace (frozenDefect M L (cubeAt 0 n) ω) ∂M.P.toMeasure) =
      (d : ℝ) * fMean M L n := by
  have hx := frozenVar_integrable_traceX M L (cubeAt 0 n)
  have hy := frozenVar_integrable_traceY M L (cubeAt 0 n)
  simp only [frozenDefect, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_add,
    Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  have hsum : Integrable (fun ω => Matrix.trace (frozenX M L (cubeAt 0 n) ω) +
      Matrix.trace (frozenY M L (cubeAt 0 n) ω)) M.P.toMeasure := hx.add hy
  rw [integral_sub (hsum.const_mul (1 / 2 : ℝ)) (integrable_const _),
    integral_const_mul, integral_add hx hy, integral_const, frozenVar_trace_X_mean, frozenVar_trace_Y_mean]
  simp only [probReal_univ, one_smul, fMean]
  ring

/-- Planar duality puts all dimensions into the same two-matrix variance formula. -/
theorem frozenVar_varV_eq_stacked (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) :
    varV M L n = (1 / (2 * (d : ℝ))) *
      ((∫ ω, frobSq (frozenX M L (cubeAt 0 n) ω - alphaMean M L n • (1 : Homogenization.Mat d))
          ∂M.P.toMeasure) +
       ∫ ω, frobSq (frozenY M L (cubeAt 0 n) ω - betaMean M L n • (1 : Homogenization.Mat d))
          ∂M.P.toMeasure) := by
  have hx := Localization.cellMoment_integrable_frobSq (fun i j =>
    (Localization.cellMoment_frozenX_entry_memLp M L (cubeAt 0 n) i j).sub
      (memLp_const ((alphaMean M L n • (1 : Homogenization.Mat d)) i j)))
  have hy := Localization.cellMoment_integrable_frobSq
    (Localization.cellMoment_centeredY_memLp M L (cubeAt 0 n) (betaMean M L n))
  change Integrable (fun ω => frobSq (frozenX M L (cubeAt 0 n) ω -
    alphaMean M L n • (1 : Homogenization.Mat d))) M.P.toMeasure at hx
  by_cases hd : d = 2
  · subst d
    rw [varV, ite_eq_left rfl, frozenVar_planar_variances_eq]
    norm_num
    ring
  · rw [varV, ite_eq_right hd, integral_add hx hy]

/-- V1 with its intermediate mean retained. -/
theorem frozenVar_varV_le_mean_add_second (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    {D : ℝ} (hD : 0 ≤ D)
    (hJ : paperENNRealLpNorm M.P.toMeasure 32 (normalizedDefect M L (cubeAt 0 n)) ≤
      ENNReal.ofReal D) :
    varV M L n ≤ 2 * fMean M L n + 2 * D ^ 2 := by
  have hd : 0 < (d : ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension
  let U := cubeAt (0 : Homogenization.Vec d) n
  have hx := frozenVar_integrable_traceX M L U
  have hy := frozenVar_integrable_traceY M L U
  have hfx := Localization.cellMoment_integrable_frobSq (Localization.cellMoment_frozenX_entry_memLp M L U)
  have hfy := Localization.cellMoment_integrable_frobSq (Localization.cellMoment_frozenY_entry_memLp M L U)
  have hfm := Localization.cellMoment_integrable_frobSq (frozenVar_defect_entry_memLp M L U)
  have htm := frozenVar_integrable_traceDefect M L U
  have hcx := Localization.cellMoment_integrable_frobSq (A := fun ω => frozenX M L U ω - 1) (fun i j =>
    (Localization.cellMoment_frozenX_entry_memLp M L U i j).sub
      (memLp_const ((1 : Homogenization.Mat d) i j)))
  have hcy := Localization.cellMoment_integrable_frobSq (A := fun ω => frozenY M L U ω - 1) (fun i j =>
    (Localization.cellMoment_frozenY_entry_memLp M L U i j).sub
      (memLp_const ((1 : Homogenization.Mat d) i j)))
  have hminx := frozenVar_center_min hx hfx (alphaMean M L n) (frozenVar_trace_X_mean M L n)
  have hminy := frozenVar_center_min hy hfy (betaMean M L n) (frozenVar_trace_Y_mean M L n)
  have hpoint (ω : SubdiffusiveProcess.Model.PotentialSample d) :
      frobSq (frozenX M L U ω - 1) + frobSq (frozenY M L U ω - 1) ≤
        4 * frobSq (frozenDefect M L U ω) + 4 * Matrix.trace (frozenDefect M L U ω) := by
    have hp := frozenVar_frozen_posDef M L U ω
    have h := frozenVar_pair_frobSq_le (Coarse.posDef_symm hp.1) (Coarse.posDef_symm hp.2)
      (frozenVar_dimension_le_frozen_trace_mul M L U ω)
    have hsym : (frozenDefect M L U ω)ᵀ = frozenDefect M L U ω := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        (frozenVar_frozenDefect_posSemidef M L U ω).isHermitian.eq
    have hsq : frobSq (frozenDefect M L U ω) =
        Matrix.trace (frozenDefect M L U ω * frozenDefect M L U ω) := by
      rw [frozenVar_frobSq_eq_trace, hsym]
    rw [hsq]
    exact h
  have hpair := integral_mono (hcx.add hcy) ((hfm.const_mul 4).add (htm.const_mul 4)) hpoint
  dsimp only [Pi.add_apply] at hpair
  rw [integral_add hcx hcy, integral_add (hfm.const_mul 4) (htm.const_mul 4),
    integral_const_mul, integral_const_mul, frozenVar_trace_defect_mean] at hpair
  have hm2 := frozenVar_defect_second_moment M L U hD hJ
  have hdef := integral_mono hfm ((hm2.1.integrable_sq).const_mul (d : ℝ))
    (frozenVar_defect_frobSq_le M L U)
  rw [integral_const_mul] at hdef
  have hbound := hdef.trans (mul_le_mul_of_nonneg_left hm2.2 hd.le)
  rw [frozenVar_varV_eq_stacked]
  apply (mul_le_mul_of_nonneg_left (add_le_add hminx hminy) (by positivity : (0 : ℝ) ≤ 1 / (2 * d))).trans
  apply (mul_le_mul_of_nonneg_left hpair (by positivity : (0 : ℝ) ≤ 1 / (2 * d))).trans
  apply le_of_le_of_eq (mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hbound (by norm_num : (0 : ℝ) ≤ 4)) (le_refl _))
    (by positivity : (0 : ℝ) ≤ 1 / (2 * d)))
  field_simp
  ring

/-- V1, with the exact statement. -/
theorem varV_le_initial_proof (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) (hLn : L ≤ n)
    {D F : ℝ} (hD : 0 ≤ D) (hF : 0 ≤ F)
    (hJ : paperENNRealLpNorm M.P.toMeasure 32 (normalizedDefect M L (cubeAt 0 n)) ≤
      ENNReal.ofReal D)
    (hf : fMean M L n ≤ F) :
    varV M L n ≤ 2 * F + 2 * D ^ 2 := by
  have _ := hLn
  have _ := hF
  exact (frozenVar_varV_le_mean_add_second M L n hD hJ).trans
    (add_le_add (mul_le_mul_of_nonneg_left hf (by norm_num : (0 : ℝ) ≤ 2)) (le_refl _))

end GMCExplicitDelta.Assembly
