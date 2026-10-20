module

public import GMCExplicitDelta.Localization.HaarDefs
public import GMCExplicitDelta.Haar.TriadicDualNorms
public import GMCExplicitDelta.Localization.Basic

/-! # G1(c): Vector projection energy as an average of squared cell means. -/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open scoped ENNReal

namespace GMCExplicitDelta.Localization.FluxBound

variable {d : ℕ}

theorem energy_projection_eq_avg (Q : Homogenization.TriadicCube d) (k : ℕ) {f : Homogenization.Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    Haar.energy Q (cubeProjection Q k f) =
      descendantsAverage Q k (fun R => cubeAverage R f * cubeAverage R f) := by
  rw [← Haar.pairing_projection_energy Q k hf]
  exact Haar.pairing_projection_right Q k f hf

theorem vecNormSq_cubeAverageVec_eq (R : Homogenization.TriadicCube d)
    (G : Homogenization.Vec d → Homogenization.Vec d) :
    vecNormSq (cubeAverageVec R G) = ∑ i, cubeAverage R (fun x => G x i) *
      cubeAverage R (fun x => G x i) := rfl

theorem descendantsAverage_sum (Q : Homogenization.TriadicCube d) (k : ℕ) {ι : Type*}
    (s : Finset ι) (F : ι → Homogenization.TriadicCube d → ℝ) :
    ∑ i ∈ s, descendantsAverage Q k (F i) = descendantsAverage Q k (fun R => ∑ i ∈ s, F i R) := by
  simp only [descendantsAverage_eq]
  rw [← Finset.mul_sum, Finset.sum_comm]

theorem sum_energy_projection (Q : Homogenization.TriadicCube d) (k : ℕ)
    {G : Homogenization.Vec d → Homogenization.Vec d}
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q)) :
    ∑ i, Haar.energy Q (cubeProjection Q k fun x => G x i) =
      descendantsAverage Q k (fun R => vecNormSq (cubeAverageVec R G)) := by
  simp_rw [energy_projection_eq_avg Q k (hG _), vecNormSq_cubeAverageVec_eq]
  exact descendantsAverage_sum Q k Finset.univ _

end GMCExplicitDelta.Localization.FluxBound
