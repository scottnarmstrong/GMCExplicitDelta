module

public import GMCExplicitDelta.Proofs.Variance.Stack

/-! # Trace means of centered cell averages -/

@[expose] public section

open MeasureTheory Matrix Homogenization Homogenization.Book SubdiffusiveProcess.CoarseGrainingVocab

namespace GMCExplicitDelta.Assembly

variable {d : ℕ}

theorem frozenVar_integrable_trace_memLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {A : Ω → Homogenization.Mat d}
    (hA : ∀ i j, MemLp (fun ω => A ω i j) 2 μ) :
    Integrable (fun ω => Matrix.trace (A ω)) μ :=
  integrable_finsetSum Finset.univ fun i _ => (hA i i).integrable (by norm_num)

theorem frozenVar_cellAvgDefect_entry_memLp (M : SubdiffusiveProcess.Model.GMCModel d) (L n k : ℕ)
    (i j : Fin d) :
    MemLp (fun ω => cellAvg n k (fun U => frozenDefect M L U ω) i j) 2 M.P.toMeasure :=
  frozenVar_cellAvg_entry_memLp n k (fun U ω => frozenDefect M L U ω) M (frozenVar_defect_entry_memLp M L) i j

theorem frozenVar_trace_cellAvgDefect_mean (M : SubdiffusiveProcess.Model.GMCModel d) (L n k : ℕ)
    (hkn : k ≤ n) :
    (∫ ω, Matrix.trace (cellAvg n k (fun U => frozenDefect M L U ω)) ∂M.P.toMeasure) =
      (d : ℝ) * fMean M L k := by
  have hx := frozenVar_integrable_trace_memLp (A := fun ω => cellAvg n k (fun U => frozenX M L U ω))
    (frozenVar_cellAvg_entry_memLp n k (fun U ω => frozenX M L U ω) M
      (Localization.cellMoment_frozenX_entry_memLp M L))
  have hy := frozenVar_integrable_trace_memLp (A := fun ω => cellAvg n k (fun U => frozenY M L U ω))
    (frozenVar_cellAvg_entry_memLp n k (fun U ω => frozenY M L U ω) M
      (Localization.cellMoment_frozenY_entry_memLp M L))
  have hsum : Integrable (fun ω =>
      Matrix.trace (cellAvg n k (fun U => frozenX M L U ω)) +
      Matrix.trace (cellAvg n k (fun U => frozenY M L U ω))) M.P.toMeasure := hx.add hy
  simp_rw [frozenVar_cellAvg_defect M L n k hkn]
  simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_one,
    Fintype.card_fin, smul_eq_mul]
  rw [integral_sub (hsum.const_mul (1 / 2 : ℝ)) (integrable_const _),
    integral_const_mul, integral_add hx hy, integral_const,
    (frozenVar_cellAvg_trace_means M L n k hkn).1, (frozenVar_cellAvg_trace_means M L n k hkn).2]
  simp only [probReal_univ, one_smul, fMean]
  ring

theorem frozenVar_trace_centered_cellAvgDefect_zero (M : SubdiffusiveProcess.Model.GMCModel d) (L n k : ℕ)
    (hkn : k ≤ n) :
    (∫ ω, Matrix.trace (cellAvg n k (fun U => frozenDefect M L U ω) - fMean M L k • 1)
      ∂M.P.toMeasure) = 0 := by
  have hm := frozenVar_integrable_trace_memLp (A := fun ω => cellAvg n k (fun U => frozenDefect M L U ω))
    (frozenVar_cellAvgDefect_entry_memLp M L n k)
  simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  rw [integral_sub hm (integrable_const _), integral_const, frozenVar_trace_cellAvgDefect_mean M L n k hkn]
  simp only [probReal_univ, one_smul]
  ring

end GMCExplicitDelta.Assembly
