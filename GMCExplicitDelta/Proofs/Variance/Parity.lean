module

public import GMCExplicitDelta.Proofs.Variance.ParityMatrix
public import GMCExplicitDelta.Proofs.Variance.EntryMeans
public import GMCExplicitDelta.Proofs.Variance.LocalMatrices
public import GMCExplicitDelta.Proofs.Variance.AverageDefect

/-! # V3: parity gain for the stacked and defect cell-average variances -/

@[expose] public section

open MeasureTheory Matrix Homogenization Homogenization.Book SubdiffusiveProcess.CoarseGrainingVocab

namespace GMCExplicitDelta.Assembly

variable {d : ℕ}

theorem frozenVar_parity_X (hd : d ∈ ({2, 3, 4} : Finset ℕ))
    (M : SubdiffusiveProcess.Model.GMCModel d) (L k n : ℕ) (hk : L + 1 ≤ k) (hkn : k ≤ n) :
    (∫ ω, frobSq (cellAvg n k (fun U => frozenX M L U ω) - alphaMean M L k • 1) ∂M.P.toMeasure) ≤
      (2 : ℝ) ^ d / (3 : ℝ) ^ (d * (n - k)) *
        ∫ ω, frobSq (frozenX M L (cubeAt 0 k) ω - alphaMean M L k • 1) ∂M.P.toMeasure := by
  exact frozenVar_parity_matrix hd M L k n hk hkn (fun U ω => frozenX M L U ω)
    (alphaMean M L k • (1 : Homogenization.Mat d))
    (Localization.cellMoment_frozenX_entry_memLp M L) (frozenVar_frozenX_local M L) (frozenVar_integral_X_entry M L k) (frozenVar_frozenX_cell_translate M L k)

theorem frozenVar_parity_Y (hd : d ∈ ({2, 3, 4} : Finset ℕ))
    (M : SubdiffusiveProcess.Model.GMCModel d) (L k n : ℕ) (hk : L + 1 ≤ k) (hkn : k ≤ n) :
    (∫ ω, frobSq (cellAvg n k (fun U => frozenY M L U ω) - betaMean M L k • 1) ∂M.P.toMeasure) ≤
      (2 : ℝ) ^ d / (3 : ℝ) ^ (d * (n - k)) *
        ∫ ω, frobSq (frozenY M L (cubeAt 0 k) ω - betaMean M L k • 1) ∂M.P.toMeasure := by
  exact frozenVar_parity_matrix hd M L k n hk hkn (fun U ω => frozenY M L U ω)
    (betaMean M L k • (1 : Homogenization.Mat d))
    (Localization.cellMoment_frozenY_entry_memLp M L) (frozenVar_frozenY_local M L) (frozenVar_integral_Y_entry M L k) (frozenVar_frozenY_cell_translate M L k)

theorem frozenVar_parity_defect (hd : d ∈ ({2, 3, 4} : Finset ℕ))
    (M : SubdiffusiveProcess.Model.GMCModel d) (L k n : ℕ) (hk : L + 1 ≤ k) (hkn : k ≤ n) :
    (∫ ω, frobSq (cellAvg n k (fun U => frozenDefect M L U ω) - fMean M L k • 1) ∂M.P.toMeasure) ≤
      (2 : ℝ) ^ d / (3 : ℝ) ^ (d * (n - k)) *
        ∫ ω, frobSq (frozenDefect M L (cubeAt 0 k) ω - fMean M L k • 1) ∂M.P.toMeasure := by
  exact frozenVar_parity_matrix hd M L k n hk hkn (fun U ω => frozenDefect M L U ω)
    (fMean M L k • (1 : Homogenization.Mat d))
    (frozenVar_defect_entry_memLp M L) (frozenVar_frozenDefect_local M L) (frozenVar_integral_defect_entry M L k) (frozenVar_frozenDefect_cell_translate M L k)

theorem cellAvgVar_le_parity_proof (hd : d ∈ ({2, 3, 4} : Finset ℕ))
    (M : SubdiffusiveProcess.Model.GMCModel d) (L k n : ℕ) (hk : L + 1 ≤ k) (hkn : k ≤ n) :
    cellAvgVar M L n k ≤ (2 : ℝ) ^ d / (3 : ℝ) ^ (d * (n - k)) * varV M L k ∧
      cellAvgDefectVar M L n k ≤ (2 : ℝ) ^ d / (3 : ℝ) ^ (d * (n - k)) * varW M L k := by
  have hx := frozenVar_parity_X hd M L k n hk hkn
  have hy := frozenVar_parity_Y hd M L k n hk hkn
  have hj := frozenVar_parity_defect hd M L k n hk hkn
  constructor
  · have hstack :
        (∑ r, ∫ ω, frobSq (cellAvg n k (fun U => frozenVar_stack M L U r ω) - frozenVar_stackMean M L k r • 1)
          ∂M.P.toMeasure) ≤
        ((2 : ℝ) ^ d / (3 : ℝ) ^ (d * (n - k))) *
          (∑ r, ∫ ω, frobSq (frozenVar_stack M L (cubeAt 0 k) r ω - frozenVar_stackMean M L k r • 1)
            ∂M.P.toMeasure) := by
      by_cases hd2 : d = 2
      · simp only [frozenVar_stack, frozenVar_stackMean, ite_eq_left hd2, Fin.sum_univ_two]
        convert add_le_add hy hy using 1
        ring
      · simp only [frozenVar_stack, frozenVar_stackMean, ite_eq_right hd2, Fin.sum_univ_two,
          ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false]
        convert add_le_add hx hy using 1
        ring
    rw [frozenVar_stack_cellAvg_var, frozenVar_stack_varV] at hstack
    have hdpos : 0 < 2 * (d : ℝ) := by
      have hd0 := M.shellPrefix.dimension
      have hd1 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
      positivity
    apply (mul_le_mul_iff_right₀ hdpos).mp
    convert hstack using 1
    ring
  · unfold cellAvgDefectVar varW
    have h := mul_le_mul_of_nonneg_left hj (inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) d))
    convert h using 1
    ring

end GMCExplicitDelta.Assembly
