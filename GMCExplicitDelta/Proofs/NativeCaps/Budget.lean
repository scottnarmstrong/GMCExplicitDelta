module

public import GMCExplicitDelta.Proofs.NativeCaps.MatrixLocal
public import GMCExplicitDelta.Proofs.NativeCaps.Subadd
public import GMCExplicitDelta.Averaging.MatrixAveragePaperNorm

/-! # The induction hypothesis supplies the matrix budgets of A5 -/

@[expose] public section

open Homogenization Homogenization.Book MeasureTheory Matrix
open SubdiffusiveProcess.CoarseGrainingVocab
open GMCExplicitDelta.Averaging GMCExplicitDelta.Insertion
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace GMCExplicitDelta.Assembly

noncomputable local instance {d : ℕ} : ContinuousENorm (Matrix (Fin d) (Fin d) ℝ) :=
  SeminormedAddGroup.toContinuousENorm

variable {d : ℕ}

theorem domain_eq_of_carrier_eq {U V : Ch02.Domain d}
    (h : (U : Set (Homogenization.Vec d)) = (V : Set (Homogenization.Vec d))) : U = V := by
  cases U
  cases V
  cases h
  rfl

theorem cubeDomain_eq_cubeAt {R : Homogenization.TriadicCube d} {n : ℕ}
    (hR : R.scale = (n : ℤ)) : Ch02.cubeDomain R = cubeAt (triadicCubeShift R) n := by
  apply domain_eq_of_carrier_eq
  change openCubeSet R = translateSet _ (openCubeSet (originCube d (n : ℤ)))
  rw [openCubeSet_eq_translateSet_originCube_of_triadicCube R, hR]

theorem cellAt_zero (R : Homogenization.TriadicCube d) : cellAt 0 R = Ch02.cubeDomain R := by
  apply domain_eq_of_carrier_eq
  exact translateSet_zero _

theorem vecNormSq_ofLp (u : EuclideanSpace ℝ (Fin d)) : vecNormSq u.ofLp = ‖u‖ ^ 2 :=
  (Ch02.vecNorm_sq_eq_vecNormSq u.ofLp).symm

/-- The model's induction statement is exactly sufficient for the means and moments of A5. -/
theorem inductionP_matrix_budget [NeZero d] (M : SubdiffusiveProcess.Model.GMCModel d)
    (L : ℕ) {D F : ℝ} (hD : 0 < D) (hF : 0 < F) (hP : InductionP M L D F)
    (n : ℕ) (hLn : L ≤ n) (z : Homogenization.Vec d) :
    MemLp (frozenDefect M L (cubeAt z n)) 32 M.P.toMeasure ∧
      lpNorm (frozenDefect M L (cubeAt z n)) 32 M.P.toMeasure ≤ D ∧
      (∫ ω, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (frozenDefect M L (cubeAt z n) ω)‖ ^ 32 ∂M.P.toMeasure) ≤ D ^ 32 ∧
      ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 →
        (∫ ω, sphereQuadratic (frozenDefect M L (cubeAt z n) ω) u ∂M.P.toMeasure) ≤ F := by
  let A := frozenDefect M L (cubeAt z n)
  have hA : Measurable A := measurable_frozenDefect M L _
  have heq : normalizedDefect M L (cubeAt z n) =
      fun ω => ENNReal.ofReal (‖Matrix.toEuclideanCLM (𝕜 := ℝ) (A ω)‖) :=
    funext (normalizedDefect_eq_ofReal_opNorm M L _)
  have hp := (hP n hLn z).2.1
  rw [heq, paperNorm_matrix_eq hA] at hp
  have hm : MemLp A 32 M.P.toMeasure := hp.trans_lt ENNReal.ofReal_lt_top
  have hn : lpNorm A 32 M.P.toMeasure ≤ D := by
    rw [← toReal_eLpNorm]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hp).trans_eq
      (ENNReal.toReal_ofReal hD.le)
  refine ⟨hm, hn, ?_, ?_⟩
  · simp only [← Matrix.cstar_norm_def]
    rw [integral_norm_pow_eq_lpNorm_pow hm]
    exact pow_le_pow_left₀ lpNorm_nonneg hn 32
  · intro u hu
    have he : vecNormSq u.ofLp = 1 := by rw [vecNormSq_ofLp, hu, one_pow]
    have hj := ((hP n hLn z).2.2 u.ofLp he).2
    have hi : Integrable (fun ω => sphereQuadratic (A ω) u) M.P.toMeasure := by
      simpa only [Function.comp_def, matrixProbe_apply] using
        ((matrixProbe u).comp_memLp' hm).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 32)
    apply (ENNReal.ofReal_le_ofReal_iff hF.le).mp
    rw [ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun ω => sphereQuadratic_nonneg (frozenDefect_posSemidef M L _ ω) u)]
    simpa only [sphereQuadratic_frozenDefect, A] using hj

/-- The same budgets apply to every deterministic scale-L cell. -/
theorem inductionP_cell_matrix_budget [NeZero d] (M : SubdiffusiveProcess.Model.GMCModel d)
    (L : ℕ) {D F : ℝ} (hD : 0 < D) (hF : 0 < F) (hP : InductionP M L D F)
    (R : Homogenization.TriadicCube d) (hR : R.scale = (L : ℤ)) :
    MemLp (frozenDefect M L (Ch02.cubeDomain R)) 32 M.P.toMeasure ∧
      lpNorm (frozenDefect M L (Ch02.cubeDomain R)) 32 M.P.toMeasure ≤ D ∧
      (∫ ω, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (frozenDefect M L (Ch02.cubeDomain R) ω)‖ ^ 32 ∂M.P.toMeasure) ≤ D ^ 32 ∧
      ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 →
        (∫ ω, sphereQuadratic (frozenDefect M L (Ch02.cubeDomain R) ω) u ∂M.P.toMeasure) ≤ F := by
  rw [cubeDomain_eq_cubeAt hR]
  exact inductionP_matrix_budget M L hD hF hP L le_rfl _

end GMCExplicitDelta.Assembly
