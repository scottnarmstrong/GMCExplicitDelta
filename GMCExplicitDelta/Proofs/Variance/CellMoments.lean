module

public import GMCExplicitDelta.Proofs.Variance.Cells

/-! # Stationary means and finite second moments of cell averages -/

@[expose] public section

open MeasureTheory Matrix Homogenization Homogenization.Book SubdiffusiveProcess.CoarseGrainingVocab

namespace GMCExplicitDelta.Assembly

variable {d : ℕ}

theorem frozenVar_cellAvg_entry_memLp (n k : ℕ)
    (A : Ch02.Domain d → SubdiffusiveProcess.Model.PotentialSample d → Homogenization.Mat d)
    (M : SubdiffusiveProcess.Model.GMCModel d)
    (hA : ∀ U i j, MemLp (fun ω => A U ω i j) 2 M.P.toMeasure) (i j : Fin d) :
    MemLp (fun ω => cellAvg n k (fun U => A U ω) i j) 2 M.P.toMeasure := by
  let s := descendantsAtScale (originCube d (n : ℤ)) (k : ℤ)
  have hsum : MemLp (fun ω => ∑ R ∈ s, A (cellAt 0 R) ω i j) 2 M.P.toMeasure :=
    memLp_finsetSum s fun R _ => hA (cellAt 0 R) i j
  have h := hsum.const_mul ((s.card : ℝ)⁻¹)
  change MemLp (fun ω => (s.card : ℝ)⁻¹ * (∑ R ∈ s, A (cellAt 0 R) ω) i j) 2 M.P.toMeasure
  simpa only [Matrix.sum_apply] using h

theorem frozenVar_frozenX_cell_translate (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    (R : Homogenization.TriadicCube d) (hR : R.scale = (n : ℤ))
    (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    frozenX M L (cellAt 0 R) ω =
      frozenX M L (cubeAt 0 n) (translatePotentialSequence (triadicCubeShift R) ω) := by
  unfold frozenX
  rw [Localization.cellMoment_cellAt_zero, freshRet_cubeAt_zero]
  change (ahom M L)⁻¹ • randomAMatrix M L (Ch02.cubeDomain R) ω = _
  rw [randomAMatrix_cube_eq_originCube_translate, hR]
  rfl

theorem frozenVar_frozenY_cell_translate (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    (R : Homogenization.TriadicCube d) (hR : R.scale = (n : ℤ))
    (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    frozenY M L (cellAt 0 R) ω =
      frozenY M L (cubeAt 0 n) (translatePotentialSequence (triadicCubeShift R) ω) := by
  unfold frozenY
  rw [Localization.cellMoment_cellAt_zero, freshRet_cubeAt_zero]
  change ahom M L • (randomAStarMatrix M L (Ch02.cubeDomain R) ω)⁻¹ = _
  rw [randomAStarInv_cube_eq_originCube_translate, hR]
  rfl

/-- Stationarity for the trace of either frozen matrix on a scale-k cell. -/
theorem frozenVar_integral_trace_cell (M : SubdiffusiveProcess.Model.GMCModel d) (L k : ℕ)
    (R : Homogenization.TriadicCube d) (hR : R.scale = (k : ℤ)) :
    (∫ ω, Matrix.trace (frozenX M L (cellAt 0 R) ω) ∂M.P.toMeasure) = (d : ℝ) * alphaMean M L k ∧
    (∫ ω, Matrix.trace (frozenY M L (cellAt 0 R) ω) ∂M.P.toMeasure) = (d : ℝ) * betaMean M L k := by
  constructor
  · simp_rw [frozenVar_frozenX_cell_translate M L k R hR]
    rw [integral_comp_eq_of_map_eq (measurable_translatePotentialSequence (triadicCubeShift R))
      (potentialSequenceLaw_stationary M (triadicCubeShift R)) _
      (frozenVar_integrable_traceX M L (cubeAt 0 k)).aestronglyMeasurable]
    exact frozenVar_trace_X_mean M L k
  · simp_rw [frozenVar_frozenY_cell_translate M L k R hR]
    rw [integral_comp_eq_of_map_eq (measurable_translatePotentialSequence (triadicCubeShift R))
      (potentialSequenceLaw_stationary M (triadicCubeShift R)) _
      (frozenVar_integrable_traceY M L (cubeAt 0 k)).aestronglyMeasurable]
    exact frozenVar_trace_Y_mean M L k

theorem frozenVar_trace_cellAvg (n k : ℕ) (A : Ch02.Domain d → Homogenization.Mat d) :
    Matrix.trace (cellAvg n k A) =
      ((descendantsAtScale (originCube d (n : ℤ)) (k : ℤ)).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtScale (originCube d (n : ℤ)) (k : ℤ), Matrix.trace (A (cellAt 0 R)) := by
  simp only [cellAvg, Matrix.trace_smul, Matrix.trace_sum, smul_eq_mul]

theorem frozenVar_integral_trace_cellAvg (M : SubdiffusiveProcess.Model.GMCModel d) (n k : ℕ)
    (hkn : k ≤ n)
    (A : Ch02.Domain d → SubdiffusiveProcess.Model.PotentialSample d → Homogenization.Mat d)
    (hA : ∀ U, Integrable (fun ω => Matrix.trace (A U ω)) M.P.toMeasure)
    (a : ℝ) (ha : ∀ R ∈ descendantsAtScale (originCube d (n : ℤ)) (k : ℤ),
      (∫ ω, Matrix.trace (A (cellAt 0 R) ω) ∂M.P.toMeasure) = a) :
    (∫ ω, Matrix.trace (cellAvg n k (fun U => A U ω)) ∂M.P.toMeasure) = a := by
  let s := descendantsAtScale (originCube d (n : ℤ)) (k : ℤ)
  have hc : (s.card : ℝ) ≠ 0 := by
    dsimp only [s]
    rw [frozenVar_cells_card n k hkn]
    positivity
  simp_rw [frozenVar_trace_cellAvg]
  rw [integral_const_mul, integral_finsetSum s (fun R _ => hA (cellAt 0 R))]
  change (s.card : ℝ)⁻¹ * (∑ R ∈ s, ∫ ω, Matrix.trace (A (cellAt 0 R) ω) ∂M.P.toMeasure) = a
  rw [Finset.sum_congr rfl ha, Finset.sum_const, nsmul_eq_mul, inv_mul_cancel_left₀ hc]

theorem frozenVar_cellAvg_trace_means (M : SubdiffusiveProcess.Model.GMCModel d) (L n k : ℕ)
    (hkn : k ≤ n) :
    (∫ ω, Matrix.trace (cellAvg n k (fun U => frozenX M L U ω)) ∂M.P.toMeasure) =
        (d : ℝ) * alphaMean M L k ∧
    (∫ ω, Matrix.trace (cellAvg n k (fun U => frozenY M L U ω)) ∂M.P.toMeasure) =
        (d : ℝ) * betaMean M L k := by
  constructor
  · exact frozenVar_integral_trace_cellAvg M n k hkn (fun U ω => frozenX M L U ω)
      (frozenVar_integrable_traceX M L) _ fun R hR =>
        (frozenVar_integral_trace_cell M L k R (scale_eq_of_mem_descendantsAtScale hR)).1
  · exact frozenVar_integral_trace_cellAvg M n k hkn (fun U ω => frozenY M L U ω)
      (frozenVar_integrable_traceY M L) _ fun R hR =>
        (frozenVar_integral_trace_cell M L k R (scale_eq_of_mem_descendantsAtScale hR)).2

end GMCExplicitDelta.Assembly
