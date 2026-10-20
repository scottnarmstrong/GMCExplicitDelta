module

public import GMCExplicitDelta.Proofs.Variance.AverageDefect
public import GMCExplicitDelta.Proofs.Variance.DefectVariance
public import GMCExplicitDelta.Proofs.Variance.DecrementMatrix
public import GMCExplicitDelta.Proofs.Variance.Recurrence

/-! # V2 for the frozen coefficient -/

@[expose] public section

open MeasureTheory Matrix Homogenization Homogenization.Book SubdiffusiveProcess.CoarseGrainingVocab

namespace GMCExplicitDelta.Assembly

variable {d : ℕ}

/-- V2, with the exact statement. -/
theorem varV_le_centeredDecrement_proof (M : SubdiffusiveProcess.Model.GMCModel d) (L k n : ℕ)
    (hLk : L ≤ k) (hkn : k < n) {κv t : ℝ} (ht : 0 < t) (hκ : 0 ≤ κv)
    (hX : cellAvgVar M L n k ≤ κv * varV M L k)
    (hJ : cellAvgDefectVar M L n k ≤ κv * varW M L k) :
    varV M L n ≤ (5 + 2 * (t + t⁻¹)) * κv * varV M L k +
      (1 + 2 / t) * (fMean M L k ^ 2 - fMean M L n ^ 2) := by
  have _ := hLk
  have hd : 0 < (d : ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension
  let X := fun r ω => frozenVar_stack M L (cubeAt 0 n) r ω
  let B := fun r ω => cellAvg n k (fun U => frozenVar_stack M L U r ω)
  let a := frozenVar_stackMean M L n
  let b := frozenVar_stackMean M L k
  let Z := fun ω => cellAvg n k (fun U => frozenDefect M L U ω) - fMean M L k • (1 : Homogenization.Mat d)
  have hXm (r : Fin 2) (i j : Fin d) : MemLp (fun ω => X r ω i j) 2 M.P.toMeasure :=
    frozenVar_stack_entry_memLp M L (cubeAt 0 n) r i j
  have hBm (r : Fin 2) (i j : Fin d) : MemLp (fun ω => B r ω i j) 2 M.P.toMeasure :=
    frozenVar_cellAvg_entry_memLp n k (fun U ω => frozenVar_stack M L U r ω) M
      (fun U i j => frozenVar_stack_entry_memLp M L U r i j) i j
  have hZm (i j : Fin d) : MemLp (fun ω => Z ω i j) 2 M.P.toMeasure :=
    (frozenVar_cellAvgDefect_entry_memLp M L n k i j).sub (memLp_const _)
  have hTD (r : Fin 2) : Integrable (fun ω => Matrix.trace (B r ω - X r ω)) M.P.toMeasure :=
    frozenVar_integrable_trace_memLp (A := fun ω => B r ω - X r ω) (fun i j => (hBm r i j).sub (hXm r i j))
  have hTZ : Integrable (fun ω => Matrix.trace (Z ω)) M.P.toMeasure :=
    frozenVar_integrable_trace_memLp (A := Z) hZm
  have hmeanD (r : Fin 2) :
      (∫ ω, Matrix.trace (B r ω - X r ω) ∂M.P.toMeasure) = (d : ℝ) * (b r - a r) := by
    have hb := frozenVar_integrable_trace_memLp (A := B r) (hBm r)
    have hx := frozenVar_integrable_trace_memLp (A := X r) (hXm r)
    simp only [Matrix.trace_sub]
    rw [integral_sub hb hx]
    change (∫ ω, Matrix.trace (cellAvg n k (fun U => frozenVar_stack M L U r ω)) ∂M.P.toMeasure) -
      (∫ ω, Matrix.trace (frozenVar_stack M L (cubeAt 0 n) r ω) ∂M.P.toMeasure) = _
    rw [frozenVar_stack_cellAvg_mean M L n k hkn.le r, frozenVar_stack_trace_mean M L n r]
    dsimp only [a, b]
    ring
  have hcenters : (∑ r, (b r - a r)) = 2 * (fMean M L k - fMean M L n) := by
    simp only [Finset.sum_sub_distrib, a, b, frozenVar_stackMean_sum]
    ring
  have hzadd (ω : SubdiffusiveProcess.Model.PotentialSample d) :
      Z ω + fMean M L k • 1 = cellAvg n k (fun U => frozenDefect M L U ω) := by
    dsimp only [Z]
    exact sub_add_cancel _ _
  have hp (r : Fin 2) (ω : SubdiffusiveProcess.Model.PotentialSample d) :
      frobSq (B r ω - X r ω) ≤
      2 * frozenVar_matrixPair (B r ω - X r ω) (Z ω + fMean M L k • 1) := by
    have hpos := frozenVar_frozen_decrements_pos M L n k hkn.le ω
    have hup := frozenVar_frozen_decrements_upper M L n k hkn.le ω
    rw [hzadd]
    dsimp only [B, X, frozenVar_stack]
    split_ifs
    · exact frozenVar_decrement_trace_bound hpos.2 hup.2
    · exact frozenVar_decrement_trace_bound hpos.1 hup.1
    · exact frozenVar_decrement_trace_bound hpos.2 hup.2
  have hcapB : (∑ r, ∫ ω, frobSq (B r ω - b r • 1) ∂M.P.toMeasure) ≤
      (2 * (d : ℝ)) * (κv * varV M L k) := by
    rw [show (∑ r, ∫ ω, frobSq (B r ω - b r • 1) ∂M.P.toMeasure) =
      (2 * (d : ℝ)) * cellAvgVar M L n k from frozenVar_stack_cellAvg_var M L n k]
    exact mul_le_mul_of_nonneg_left hX (by positivity)
  have hcapZ : 2 * (∫ ω, frobSq (Z ω) ∂M.P.toMeasure) ≤
      (2 * (d : ℝ)) * (κv * varV M L k) := by
    have hj := hJ.trans (mul_le_mul_of_nonneg_left (frozenVar_varW_le_varV M L k) hκ)
    change (d : ℝ)⁻¹ * (∫ ω, frobSq (Z ω) ∂M.P.toMeasure) ≤ κv * varV M L k at hj
    have hmul := mul_le_mul_of_nonneg_left hj (by positivity : (0 : ℝ) ≤ 2 * d)
    convert hmul using 1
    field_simp
  have hfn := fMean_nonneg_antitone_proof M L
  have hgap : 0 ≤ fMean M L k ^ 2 - fMean M L n ^ 2 :=
    sub_nonneg.mpr ((sq_le_sq₀ (hfn.1 n) (hfn.1 k)).2 (hfn.2 k n hkn.le))
  have hrec := frozenVar_two_channel_recurrence X B a b Z (fMean M L n) (fMean M L k)
    ((2 * (d : ℝ)) * (κv * varV M L k)) t hXm hBm hZm hTD hTZ hmeanD
    (frozenVar_trace_centered_cellAvgDefect_zero M L n k hkn.le) hcenters hp hcapB hcapZ
    (mul_nonneg (by positivity) (mul_nonneg hκ (varV_nonneg M L k))) hgap ht
  rw [show (∑ r, ∫ ω, frobSq (X r ω - a r • 1) ∂M.P.toMeasure) =
    (2 * (d : ℝ)) * varV M L n from frozenVar_stack_varV M L n] at hrec
  apply (mul_le_mul_iff_right₀ (show 0 < 2 * (d : ℝ) by positivity)).mp
  convert hrec using 1
  ring

end GMCExplicitDelta.Assembly
