module

public import GMCExplicitDelta.Proofs.Variance.CellMoments
public import GMCExplicitDelta.Proofs.AnnealedMeans.Planar
public import GMCExplicitDelta.Proofs.Observables.Mean

/-! # A uniform two-channel representation of the frozen variance -/

@[expose] public section

open MeasureTheory Matrix Homogenization Homogenization.Book SubdiffusiveProcess.CoarseGrainingVocab

namespace GMCExplicitDelta.Assembly

variable {d : ℕ}

noncomputable def frozenVar_stack (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (U : Ch02.Domain d) (r : Fin 2) (ω : SubdiffusiveProcess.Model.PotentialSample d) : Homogenization.Mat d :=
  if d = 2 then frozenY M L U ω else if r = 0 then frozenX M L U ω else frozenY M L U ω

noncomputable def frozenVar_stackMean (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) (r : Fin 2) : ℝ :=
  if d = 2 then betaMean M L n else if r = 0 then alphaMean M L n else betaMean M L n

theorem frozenVar_stack_entry_memLp (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (U : Ch02.Domain d) (r : Fin 2) (i j : Fin d) :
    MemLp (fun ω => frozenVar_stack M L U r ω i j) 2 M.P.toMeasure := by
  unfold frozenVar_stack
  split_ifs
  · exact Localization.cellMoment_frozenY_entry_memLp M L U i j
  · exact Localization.cellMoment_frozenX_entry_memLp M L U i j
  · exact Localization.cellMoment_frozenY_entry_memLp M L U i j

theorem frozenVar_stackMean_sum (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) :
    (∑ r, frozenVar_stackMean M L n r) = 2 * (fMean M L n + 1) := by
  by_cases hd : d = 2
  · subst d
    simp only [frozenVar_stackMean, ite_true, Fin.sum_univ_two]
    rw [fMean, annealedMean_alpha_eq_beta_planar]
    ring
  · simp only [frozenVar_stackMean, hd, ite_false, Fin.sum_univ_two, Fin.isValue,
      ite_true, show (1 : Fin 2) ≠ 0 by decide]
    unfold fMean
    ring

theorem frozenVar_stack_trace_mean (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) (r : Fin 2) :
    (∫ ω, Matrix.trace (frozenVar_stack M L (cubeAt 0 n) r ω) ∂M.P.toMeasure) =
      (d : ℝ) * frozenVar_stackMean M L n r := by
  unfold frozenVar_stack frozenVar_stackMean
  split_ifs
  · exact frozenVar_trace_Y_mean M L n
  · exact frozenVar_trace_X_mean M L n
  · exact frozenVar_trace_Y_mean M L n

theorem frozenVar_stack_cellAvg_mean (M : SubdiffusiveProcess.Model.GMCModel d) (L n k : ℕ)
    (hkn : k ≤ n) (r : Fin 2) :
    (∫ ω, Matrix.trace (cellAvg n k (fun U => frozenVar_stack M L U r ω)) ∂M.P.toMeasure) =
      (d : ℝ) * frozenVar_stackMean M L k r := by
  unfold frozenVar_stack frozenVar_stackMean
  split_ifs
  · exact (frozenVar_cellAvg_trace_means M L n k hkn).2
  · exact (frozenVar_cellAvg_trace_means M L n k hkn).1
  · exact (frozenVar_cellAvg_trace_means M L n k hkn).2

theorem frozenVar_stack_varV (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) :
    (∑ r, ∫ ω, frobSq (frozenVar_stack M L (cubeAt 0 n) r ω - frozenVar_stackMean M L n r • 1)
      ∂M.P.toMeasure) = (2 * (d : ℝ)) * varV M L n := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (neZero_of_gmcModel M).ne
  by_cases hd : d = 2
  · subst d
    simp only [frozenVar_stack, frozenVar_stackMean, ite_true, Fin.sum_univ_two, varV]
    norm_num
    ring
  · have hx := Localization.cellMoment_integrable_frobSq
      (A := fun ω => frozenX M L (cubeAt 0 n) ω - alphaMean M L n • 1)
      (fun i j => (Localization.cellMoment_frozenX_entry_memLp M L (cubeAt 0 n) i j).sub (memLp_const _))
    have hy := Localization.cellMoment_integrable_frobSq
      (Localization.cellMoment_centeredY_memLp M L (cubeAt 0 n) (betaMean M L n))
    simp only [frozenVar_stack, frozenVar_stackMean, hd, ite_false, Fin.sum_univ_two,
      ite_true, show (1 : Fin 2) ≠ 0 by decide, varV]
    rw [integral_add hx hy]
    field_simp

theorem frozenVar_stack_cellAvg_var (M : SubdiffusiveProcess.Model.GMCModel d) (L n k : ℕ) :
    (∑ r, ∫ ω, frobSq (cellAvg n k (fun U => frozenVar_stack M L U r ω) - frozenVar_stackMean M L k r • 1)
      ∂M.P.toMeasure) = (2 * (d : ℝ)) * cellAvgVar M L n k := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (neZero_of_gmcModel M).ne
  by_cases hd : d = 2
  · subst d
    simp only [frozenVar_stack, frozenVar_stackMean, ite_true, Fin.sum_univ_two, cellAvgVar]
    norm_num
    ring
  · have hx := Localization.cellMoment_integrable_frobSq
      (A := fun ω => cellAvg n k (fun U => frozenX M L U ω) - alphaMean M L k • 1)
      (fun i j => (frozenVar_cellAvg_entry_memLp n k (fun U ω => frozenX M L U ω) M
        (Localization.cellMoment_frozenX_entry_memLp M L) i j).sub (memLp_const _))
    have hy := Localization.cellMoment_integrable_frobSq
      (A := fun ω => cellAvg n k (fun U => frozenY M L U ω) - betaMean M L k • 1)
      (fun i j => (frozenVar_cellAvg_entry_memLp n k (fun U ω => frozenY M L U ω) M
        (Localization.cellMoment_frozenY_entry_memLp M L) i j).sub (memLp_const _))
    simp only [frozenVar_stack, frozenVar_stackMean, hd, ite_false, Fin.sum_univ_two,
      ite_true, show (1 : Fin 2) ≠ 0 by decide, cellAvgVar]
    rw [integral_add hx hy]
    field_simp

end GMCExplicitDelta.Assembly
