module

public import GMCExplicitDelta.Proofs.PlanarBlock.HaarArray
public import GMCExplicitDelta.Proofs.PlanarBlock.ChildLowModes
public import GMCExplicitDelta.Proofs.PlanarBlock.LowCoefficients

/-! The exceptional coefficients of a first Haar increment. -/

@[expose] public section

noncomputable section

open Homogenization Real MeasureTheory

namespace GMCExplicitDelta.Localization

theorem planarBlock_haar_low_zero (Q : TriadicCube 2) (f : Vec 2 → ℝ) :
    planarBlock_sinCoeff Q 0 ![1, 0] (cubeIncrement Q 1 f) =
      (∑ i, ∑ j, planarBlock_haarArray Q f i j * planarBlock_sinePattern i) / (6 * π) ∧
    planarBlock_sinCoeff Q 0 ![2, 0] (cubeIncrement Q 1 f) =
      (∑ i, ∑ j, planarBlock_haarArray Q f i j * planarBlock_axisEven i) / (4 * π) ∧
    planarBlock_sinCoeff Q 0 ![1, 1] (cubeIncrement Q 1 f) =
      √3 / (4 * π ^ 2) *
        (∑ i, ∑ j, planarBlock_haarArray Q f i j * (planarBlock_sinePattern i * planarBlock_axisEven j)) := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [planarBlock_haarArray_coeff] <;>
    simp_rw [planarBlock_child_sin_zero] <;>
    simp [planarBlock_thirdSin_one, planarBlock_thirdSin_two, planarBlock_thirdCos_zero, planarBlock_thirdCos_one,
      Fin.sum_univ_succ, planarBlock_sinePattern, planarBlock_axisEven] <;> ring

theorem planarBlock_haar_low_one (Q : TriadicCube 2) (f : Vec 2 → ℝ) :
    planarBlock_sinCoeff Q 1 ![0, 1] (cubeIncrement Q 1 f) =
      (∑ i, ∑ j, planarBlock_haarArray Q f i j * planarBlock_sinePattern j) / (6 * π) ∧
    planarBlock_sinCoeff Q 1 ![0, 2] (cubeIncrement Q 1 f) =
      (∑ i, ∑ j, planarBlock_haarArray Q f i j * planarBlock_axisEven j) / (4 * π) ∧
    planarBlock_sinCoeff Q 1 ![1, 1] (cubeIncrement Q 1 f) =
      √3 / (4 * π ^ 2) *
        (∑ i, ∑ j, planarBlock_haarArray Q f i j * (planarBlock_axisEven i * planarBlock_sinePattern j)) := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [planarBlock_haarArray_coeff] <;>
    simp_rw [planarBlock_child_sin_one] <;>
    simp [planarBlock_thirdSin_one, planarBlock_thirdSin_two, planarBlock_thirdCos_zero, planarBlock_thirdCos_one,
      Fin.sum_univ_succ, planarBlock_sinePattern, planarBlock_axisEven] <;> ring

theorem planarBlock_haar_low_bound_zero (Q : TriadicCube 2) {f : Vec 2 → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    8 / (5 * π ^ 2) * planarBlock_sinCoeff Q 0 ![1, 0] (cubeIncrement Q 1 f) ^ 2 +
      1 / (10 * π ^ 2) * planarBlock_sinCoeff Q 0 ![2, 0] (cubeIncrement Q 1 f) ^ 2 +
      6 / (5 * π ^ 2) * planarBlock_sinCoeff Q 0 ![1, 1] (cubeIncrement Q 1 f) ^ 2 ≤
      243 / (10 * π ^ 6) * Haar.energy Q (cubeIncrement Q 1 f) := by
  obtain ⟨h1, h2, hm⟩ := planarBlock_haar_low_zero Q f
  rw [h1, h2, hm, planarBlock_haarArray_energy]
  exact planarBlock_low_coefficient_bound (planarBlock_haarArray Q f) (planarBlock_haarArray_mean Q hf)

theorem planarBlock_haar_low_bound_one (Q : TriadicCube 2) {f : Vec 2 → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    8 / (5 * π ^ 2) * planarBlock_sinCoeff Q 1 ![0, 1] (cubeIncrement Q 1 f) ^ 2 +
      1 / (10 * π ^ 2) * planarBlock_sinCoeff Q 1 ![0, 2] (cubeIncrement Q 1 f) ^ 2 +
      6 / (5 * π ^ 2) * planarBlock_sinCoeff Q 1 ![1, 1] (cubeIncrement Q 1 f) ^ 2 ≤
      243 / (10 * π ^ 6) * Haar.energy Q (cubeIncrement Q 1 f) := by
  obtain ⟨h1, h2, hm⟩ := planarBlock_haar_low_one Q f
  rw [h1, h2, hm, planarBlock_haarArray_energy]
  have hmean : (∑ i, ∑ j, planarBlock_haarArray Q f j i) = 0 := by
    rw [Finset.sum_comm]
    exact planarBlock_haarArray_mean Q hf
  have h := planarBlock_low_coefficient_bound (fun i j => planarBlock_haarArray Q f j i) hmean
  have hA : (∑ i, ∑ j, planarBlock_haarArray Q f j i * planarBlock_sinePattern i) =
      ∑ i, ∑ j, planarBlock_haarArray Q f i j * planarBlock_sinePattern j := Finset.sum_comm
  have hB : (∑ i, ∑ j, planarBlock_haarArray Q f j i * planarBlock_axisEven i) =
      ∑ i, ∑ j, planarBlock_haarArray Q f i j * planarBlock_axisEven j := Finset.sum_comm
  have hC : (∑ i, ∑ j, planarBlock_haarArray Q f j i * (planarBlock_sinePattern i * planarBlock_axisEven j)) =
      ∑ i, ∑ j, planarBlock_haarArray Q f i j * (planarBlock_axisEven i * planarBlock_sinePattern j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hS : (∑ i, ∑ j, planarBlock_haarArray Q f j i ^ 2) =
      ∑ i, ∑ j, planarBlock_haarArray Q f i j ^ 2 := Finset.sum_comm
  rw [hA, hB, hC, hS] at h
  exact h

end GMCExplicitDelta.Localization
