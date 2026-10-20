module

public import GMCExplicitDelta.Proofs.Variance.Initial

/-! # Defect variance is bounded by the stacked variance -/

@[expose] public section

open MeasureTheory Matrix Homogenization Homogenization.Book SubdiffusiveProcess.CoarseGrainingVocab

namespace GMCExplicitDelta.Assembly

variable {d : ℕ}

theorem frozenVar_frobSq_half_add_le (A B : Homogenization.Mat d) :
    frobSq ((1 / 2 : ℝ) • (A + B)) ≤ (frobSq A + frobSq B) / 2 := by
  calc
    _ ≤ ∑ i, ∑ j, (A i j ^ 2 + B i j ^ 2) / 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      change ((1 / 2 : ℝ) * (A i j + B i j)) ^ 2 ≤ _
      nlinarith only [sq_nonneg (A i j - B i j)]
    _ = _ := by
      simp only [add_div, Finset.sum_add_distrib, ← Finset.sum_div, frobSq]

theorem frozenVar_centeredDefect_eq (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    frozenDefect M L (cubeAt 0 n) ω - fMean M L n • 1 =
      (1 / 2 : ℝ) • ((frozenX M L (cubeAt 0 n) ω - alphaMean M L n • 1) +
        (frozenY M L (cubeAt 0 n) ω - betaMean M L n • 1)) := by
  unfold frozenDefect fMean
  module

theorem frozenVar_varW_le_varV (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) :
    varW M L n ≤ varV M L n := by
  have hx := Localization.cellMoment_integrable_frobSq
    (A := fun ω => frozenX M L (cubeAt 0 n) ω - alphaMean M L n • 1)
    (fun i j => (Localization.cellMoment_frozenX_entry_memLp M L (cubeAt 0 n) i j).sub (memLp_const _))
  have hy := Localization.cellMoment_integrable_frobSq
    (Localization.cellMoment_centeredY_memLp M L (cubeAt 0 n) (betaMean M L n))
  have hm := Localization.cellMoment_integrable_frobSq
    (A := fun ω => frozenDefect M L (cubeAt 0 n) ω - fMean M L n • 1)
    (fun i j => (frozenVar_defect_entry_memLp M L (cubeAt 0 n) i j).sub (memLp_const _))
  have hsum : Integrable (fun ω =>
      frobSq (frozenX M L (cubeAt 0 n) ω - alphaMean M L n • 1) +
      frobSq (frozenY M L (cubeAt 0 n) ω - betaMean M L n • 1)) M.P.toMeasure := hx.add hy
  have hi := integral_mono hm (hsum.div_const 2) (fun ω => by
    rw [frozenVar_centeredDefect_eq]
    exact frozenVar_frobSq_half_add_le _ _)
  rw [integral_div, integral_add hx hy] at hi
  rw [varW, frozenVar_varV_eq_stacked]
  have h := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) d))
  convert h using 1
  ring

end GMCExplicitDelta.Assembly
