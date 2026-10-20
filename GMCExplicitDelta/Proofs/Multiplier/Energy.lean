module

public import GMCExplicitDelta.Proofs.Multiplier.Centered

/-! The L² multiplier bound paired with the Sobolev bound H7. -/
@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace GMCExplicitDelta.Localization.Multiplier

open Haar
variable {d : ℕ}

theorem cutoffGradient_sq_sum_le (row : Contract.Row d) (hω0 : 0 < row.omegaEff)
    (hω1 : row.omegaEff ≤ 1 / 2) (n : ℕ) {x : Vec d}
    (hx : x ∈ cubeSet (originCube d (n : ℤ))) :
    (∑ i, cubeCutoffGrad row n x i ^ 2) ≤ row.kappaOmega ^ 2 / ((3 : ℝ) ^ n) ^ 2 := by
  unfold cubeCutoffGrad
  simp_rw [div_pow]
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right
    (Haar.cutoffGradient_sq_sum_le_kappaOmega row hω0 hω1 _ (originCube_coord_bound n hx)) (sq_nonneg _)

theorem cutoff_energy_le (row : Contract.Row d) (hω0 : 0 < row.omegaEff)
    (hω1 : row.omegaEff ≤ 1 / 2) (n : ℕ)
    (u : H1Function (openCubeSet (originCube d (n : ℤ)) ))
    (H : Fin d → H1Function (openCubeSet (originCube d (n : ℤ)) ))
    (hH : ∀ i, (H i).toFun = fun x => u.toFun x * cubeCutoffGrad row n x i) :
    vecEnergy (originCube d (n : ℤ)) (fun x i => u.toFun x * cubeCutoffGrad row n x i) ≤
      row.kappaOmega ^ 2 / ((3 : ℝ) ^ n) ^ 2 * Haar.energy (originCube d (n : ℤ)) u.toFun := by
  let Q := originCube d (n : ℤ)
  let μ := normalizedCubeMeasure Q
  let G := fun x i => u.toFun x * cubeCutoffGrad row n x i
  have hG (i : Fin d) : MemLp (fun x => G x i) 2 μ := by
    rw [← hH i]
    exact (H i).memL2_normalizedCubeMeasure
  have hi : Integrable (fun x => ∑ i, G x i ^ 2) μ :=
    integrable_finsetSum _ (fun i _ => (hG i).integrable_sq)
  rw [vecEnergy_eq_integral Q G hG]
  calc
    _ ≤ ∫ x, row.kappaOmega ^ 2 / ((3 : ℝ) ^ n) ^ 2 * u.toFun x ^ 2 ∂μ := by
      apply integral_mono_ae hi (u.memL2_normalizedCubeMeasure.integrable_sq.const_mul _)
      filter_upwards [normalizedCubeMeasure_ae_mem Q] with x hx
      change (∑ i, (u.toFun x * cubeCutoffGrad row n x i) ^ 2) ≤ _
      simp_rw [mul_pow]
      rw [← Finset.mul_sum]
      exact (mul_le_mul_of_nonneg_left (cutoffGradient_sq_sum_le row hω0 hω1 n hx)
        (sq_nonneg _)).trans_eq (mul_comm _ _)
    _ = _ := by
      rw [integral_const_mul]
      simp only [Haar.energy, Haar.pairing, cubeAverage_eq_integral_normalizedCubeMeasure, pow_two]
      rfl

end GMCExplicitDelta.Localization.Multiplier
