module

public import GMCExplicitDelta.Proofs.Multiplier.Energy
public import GMCExplicitDelta.Proofs.Multiplier.Series
public import GMCExplicitDelta.Proofs.Contraction.Haar

/-! Assembly of H7, cell Poincaré, and vector Abel summation for H9. -/
@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace GMCExplicitDelta.Localization.Multiplier

open Haar Contract
variable {d : ℕ}

/-- H9 with only the exact cell-Poincaré input exposed. -/
theorem haar_multiplier_of_cell_poincare
    (hcell : ∀ (Q : TriadicCube d) (j : ℕ) (h : H1Function (openCubeSet Q)),
      Haar.energy Q (fun x => h.toFun x - cubeProjection Q j h.toFun x) ≤
        cubeScaleFactor Q ^ 2 / (9 ^ j * Real.pi ^ 2) * vecEnergy Q h.grad)
    (row : Row d) (hO : row.Obligations)
    (n : ℕ) (w : H1Function (openCubeSet (originCube d (n : ℤ)))) {Λ m : ℝ} (hΛ : 0 ≤ Λ)
    (hw : Haar.energy (originCube d (n : ℤ))
        (fun x => w.toFun x - cubeAverage (originCube d (n : ℤ)) w.toFun) ≤
      Λ / row.kappaOmega ^ 2 * ((3 : ℝ) ^ n) ^ 2 * m ^ 2)
    (hgw : vecEnergy (originCube d (n : ℤ)) w.grad ≤ m ^ 2) :
    haarPrimal (originCube d (n : ℤ)) row.qs (fun x =>
        (w.toFun x - cubeAverage (originCube d (n : ℤ)) w.toFun) • cubeCutoffGrad row n x) ≤
      ENNReal.ofReal (multSq row Λ * m ^ 2) := by
  let Q := originCube d (n : ℤ)
  let S := (3 : ℝ) ^ n
  let u := centeredH1 Q w
  let G := fun x => u.toFun x • cubeCutoffGrad row n x
  have hS : S ≠ 0 := by dsimp only [S]; positivity
  obtain ⟨hω0, hω1⟩ := LocWeights.omega_bounds row hO
  have hk : row.kappaOmega ≠ 0 := ne_of_gt (div_pos Real.pi_pos (mul_pos (by norm_num) hω0))
  have hwu : Haar.energy Q u.toFun ≤ Λ / row.kappaOmega ^ 2 * S ^ 2 * m ^ 2 := by
    simpa only [u, centeredH1_toFun] using hw
  have hq := (Assembly.haar_majorants row hO).1
  obtain ⟨H, hH, hDH⟩ := exists_cutoffGradientH1 row hω0 hω1 n u
  have hG (i : Fin d) : MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q) := by
    change MemLp (fun x => u.toFun x * cubeCutoffGrad row n x i) 2 _
    rw [← hH i]
    exact (H i).memL2_normalizedCubeMeasure
  have he : vecEnergy Q G ≤ Λ * m ^ 2 := by
    have he0 := cutoff_energy_le row hω0 hω1 n u H hH
    calc
      _ ≤ row.kappaOmega ^ 2 / S ^ 2 * Haar.energy Q u.toFun := he0
      _ ≤ row.kappaOmega ^ 2 / S ^ 2 * (Λ / row.kappaOmega ^ 2 * S ^ 2 * m ^ 2) :=
        mul_le_mul_of_nonneg_left hwu (div_nonneg (sq_nonneg _) (sq_nonneg _))
      _ = _ := by field_simp [hk, hS]
  have hgrad : (∑ i, vecEnergy Q (H i).grad) ≤
      row.kappaOmega ^ 2 / S ^ 2 * (1 + (d : ℝ) * Λ) * m ^ 2 := by
    have hu_grad : u.grad = w.grad := centeredH1_grad Q w
    rw [hu_grad] at hDH
    calc
      _ ≤ row.kappaOmega ^ 2 / S ^ 2 * vecEnergy Q w.grad +
          (d : ℝ) * row.kappaOmega ^ 4 / S ^ 4 * Haar.energy Q u.toFun := hDH
      _ ≤ row.kappaOmega ^ 2 / S ^ 2 * m ^ 2 +
          (d : ℝ) * row.kappaOmega ^ 4 / S ^ 4 * (Λ / row.kappaOmega ^ 2 * S ^ 2 * m ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hgw (by positivity))
          (mul_le_mul_of_nonneg_left hwu (by positivity))
      _ = _ := by field_simp [hk, hS]
  have hr (j : ℕ) : LocWeights.residualEnergy Q j G ≤
      min (Λ * m ^ 2) ((row.etaOmega * (1 + (d : ℝ) * Λ) * m ^ 2) / 9 ^ j) := by
    apply le_min
    · apply le_trans _ he
      unfold LocWeights.residualEnergy vecEnergy
      apply Finset.sum_le_sum
      intro i _
      rw [energy_residual Q j (hG i)]
      exact sub_le_self _ (energy_nonneg _ _)
    · have hsc : cubeScaleFactor Q = S := by simp only [Q, S, cubeScaleFactor, originCube, zpow_natCast]
      have hb : LocWeights.residualEnergy Q j G ≤
          S ^ 2 / (9 ^ j * Real.pi ^ 2) * ∑ i, vecEnergy Q (H i).grad := by
        unfold LocWeights.residualEnergy
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i _
        have hi := hcell Q j (H i)
        rw [hsc, hH i] at hi
        exact hi
      calc
        _ ≤ S ^ 2 / (9 ^ j * Real.pi ^ 2) * ∑ i, vecEnergy Q (H i).grad := hb
        _ ≤ S ^ 2 / (9 ^ j * Real.pi ^ 2) *
            (row.kappaOmega ^ 2 / S ^ 2 * (1 + (d : ℝ) * Λ) * m ^ 2) :=
          mul_le_mul_of_nonneg_left hgrad (by positivity)
        _ = _ := by
          unfold Row.kappaOmega Row.etaOmega
          field_simp [hS, Real.pi_ne_zero, hω0.ne', (by positivity : (9 : ℝ) ^ j ≠ 0)]
          ring
  have hη : 0 ≤ row.etaOmega := by unfold Row.etaOmega; positivity
  have hb := LocWeights.haarPrimal_le_minSeries Q hq.1 hq.2.1
    (mul_nonneg hΛ (sq_nonneg m)) (mul_nonneg (mul_nonneg hη (by positivity)) (sq_nonneg m)) G hG he hr
  rw [minSeries_mul_nonneg _ _ _ _ (sq_nonneg m)] at hb
  have hcoeff : Λ * m ^ 2 + (row.qs - 1) *
      (minSeries row.qs Λ (row.etaOmega * (1 + (d : ℝ) * Λ)) * m ^ 2) = multSq row Λ * m ^ 2 := by
    unfold multSq
    ring
  rw [hcoeff] at hb
  simpa only [G, u, centeredH1_toFun] using hb

end GMCExplicitDelta.Localization.Multiplier
