module

public import GMCExplicitDelta.Proofs.PlanarBlock.Exceptional
public import GMCExplicitDelta.Proofs.PlanarBlock.HaarLowModes

/-! H6: the planar first Haar block, via a cutoff-five spectral split. -/

@[expose] public section

noncomputable section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open scoped ENNReal

namespace GMCExplicitDelta.Localization

theorem planarBlock_exceptional_increment_bound (Q : Homogenization.TriadicCube 2) {f : Homogenization.Vec 2 → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) (j : Fin 2) :
    (∑ p ∈ planarBlock_lowModes, planarBlock_lowWeight ((Real.pi / cubeScaleFactor Q) ^ 2) p *
      planarBlock_sinCoeff Q j p (cubeIncrement Q 1 f) ^ 2) ≤
      cubeScaleFactor Q ^ 2 * (243 / (10 * Real.pi ^ 6)) *
        Haar.energy Q (cubeIncrement Q 1 f) := by
  have hℓ := Haar.cubeScaleFactor_pos' Q
  fin_cases j
  · have h := mul_le_mul_of_nonneg_left (planarBlock_haar_low_bound_zero Q hf)
      (sq_nonneg (cubeScaleFactor Q))
    calc
      _ = _ := planarBlock_exceptional_zero Q ((Real.pi / cubeScaleFactor Q) ^ 2) (cubeIncrement Q 1 f)
      _ ≤ _ := by
        convert h using 1 <;> field_simp [hℓ.ne', Real.pi_ne_zero]
  · have h := mul_le_mul_of_nonneg_left (planarBlock_haar_low_bound_one Q hf)
      (sq_nonneg (cubeScaleFactor Q))
    calc
      _ = _ := planarBlock_exceptional_one Q ((Real.pi / cubeScaleFactor Q) ^ 2) (cubeIncrement Q 1 f)
      _ ≤ _ := by
        convert h using 1 <;> field_simp [hℓ.ne', Real.pi_ne_zero]

theorem planar_first_block_proof (Q : Homogenization.TriadicCube 2)
    (F : Homogenization.Vec 2 → Homogenization.Vec 2)
    (hF : ∀ i, MeasureTheory.MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (w : H1Function (openCubeSet Q))
    (hw : IsNeumannPrimitive Q (vecIncrement Q 1 F) w) :
    Haar.energy Q w.toFun ≤
      (1 / (5 * Real.pi ^ 2) + 243 / (10 * Real.pi ^ 6)) * cubeScaleFactor Q ^ 2 *
        vecEnergy Q (vecIncrement Q 1 F) := by
  let G := vecIncrement Q 1 F
  let r := (Real.pi / cubeScaleFactor Q) ^ 2
  have hℓ := Haar.cubeScaleFactor_pos' Q
  have hr : 0 < r := sq_pos_of_pos (div_pos Real.pi_pos hℓ)
  have hG : ∀ j, MemLp (fun x => G x j) 2 (normalizedCubeMeasure Q) :=
    fun j => Haar.increment_memLp Q 1 (fun x => F x j)
  have heig : ∀ p : Fin 2 → ℤ, Haar.cubeEig Q p = r * (planarBlock_modeSize p : ℝ) := by
    intro p
    rw [planarBlock_cubeEig_two]
    simp only [planarBlock_modeSize, Int.cast_add, Int.cast_pow]
    rfl
  have hs := planarBlock_neumann_finite_correction Q hG hw planarBlock_lowModes (planarBlock_lowWeight r)
    (show 0 ≤ 1 / (5 * r) by positivity)
    (fun p _ => planarBlock_lowWeight_nonneg hr p)
    (fun p hp => by rw [heig]; exact planarBlock_lowWeight_gap hr p hp)
  have hcorr : (∑ p ∈ planarBlock_lowModes, planarBlock_lowWeight r p * ∑ j,
      (∫ x, Haar.cubeSin Q j p x * G x j ∂normalizedCubeMeasure Q) ^ 2) ≤
      cubeScaleFactor Q ^ 2 * (243 / (10 * Real.pi ^ 6)) * vecEnergy Q G := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm, vecEnergy, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    exact planarBlock_exceptional_increment_bound Q (hF j) j
  have heq : 1 / (5 * r) * vecEnergy Q G +
      cubeScaleFactor Q ^ 2 * (243 / (10 * Real.pi ^ 6)) * vecEnergy Q G =
      (1 / (5 * Real.pi ^ 2) + 243 / (10 * Real.pi ^ 6)) * cubeScaleFactor Q ^ 2 *
        vecEnergy Q G := by
    dsimp [r]
    field_simp [hℓ.ne', Real.pi_ne_zero]
  exact hs.trans ((add_le_add le_rfl hcorr).trans (le_of_eq heq))

end GMCExplicitDelta.Localization
