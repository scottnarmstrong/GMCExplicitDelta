module

public import GMCExplicitDelta.Localization.HaarDefs
public import GMCExplicitDelta.Haar.TriadicDualNorms
public import GMCExplicitDelta.Haar.TailsMinimumSeries

/-! Vector Abel summation and the minimum-series estimate used in H9. -/
@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace GMCExplicitDelta.Localization.LocWeights

open Contract Haar
variable {d : ℕ}

/-- Sum of the scalar projection residual energies. -/
noncomputable def residualEnergy (Q : TriadicCube d) (j : ℕ)
    (G : Homogenization.Vec d → Homogenization.Vec d) : ℝ :=
  ∑ i, Haar.energy Q (fun x => G x i - cubeProjection Q j (fun y => G y i) x)

/-- The analytic multiplier step reduces to an L² bound and a sharp residual bound. -/
theorem haarPrimal_le_minSeries (Q : TriadicCube d) {q A H : ℝ}
    (hq1 : 1 < q) (hq9 : q < 9) (hA : 0 ≤ A) (hH : 0 ≤ H)
    (G : Homogenization.Vec d → Homogenization.Vec d)
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q))
    (he : vecEnergy Q G ≤ A)
    (hr : ∀ j, residualEnergy Q j G ≤ min A (H / 9 ^ j)) :
    haarPrimal Q q G ≤ ENNReal.ofReal (A + (q - 1) * minSeries q A H) := by
  have hq0 : 0 ≤ q := zero_le_one.trans hq1.le
  have hmajor := minSeries_summable hq0 hq9 hA hH
  have hr0 (j : ℕ) : 0 ≤ residualEnergy Q j G := Finset.sum_nonneg (fun _ _ => energy_nonneg _ _)
  have hri (i : Fin d) (j : ℕ) :
      Haar.energy Q (fun x => G x i - cubeProjection Q j (fun y => G y i) x) ≤ residualEnergy Q j G := by
    unfold residualEnergy
    exact Finset.single_le_sum (fun l _ => energy_nonneg Q
      (fun x => G x l - cubeProjection Q j (fun y => G y l) x)) (Finset.mem_univ i)
  have hs (i : Fin d) : Summable (fun j => q ^ j *
      Haar.energy Q (fun x => G x i - cubeProjection Q j (fun y => G y i) x)) :=
    hmajor.of_nonneg_of_le (fun _ => mul_nonneg (pow_nonneg hq0 _) (energy_nonneg _ _))
      (fun j => mul_le_mul_of_nonneg_left ((hri i j).trans (hr j)) (pow_nonneg hq0 j))
  have hsR : Summable (fun j => q ^ j * residualEnergy Q j G) :=
    hmajor.of_nonneg_of_le (fun j => mul_nonneg (pow_nonneg hq0 j) (hr0 j))
      (fun j => mul_le_mul_of_nonneg_left (hr j) (pow_nonneg hq0 j))
  have hsi (i : Fin d) : Summable (fun k => q ^ k * Haar.energy Q (cubeIncrement Q k (fun x => G x i))) :=
    (summable_nat_add_iff 1).1 (summable_primal_increments_of_residuals Q q (hG i) (hs i))
  have htotal : Summable (fun k => q ^ k * ∑ i, Haar.energy Q (cubeIncrement Q k (fun x => G x i))) := by
    simp_rw [Finset.mul_sum]
    exact summable_sum (fun i _ => hsi i)
  have hfull : (∑' k, q ^ k * ∑ i, Haar.energy Q (cubeIncrement Q k (fun x => G x i))) =
      ∑ i, primalEnergy Q q (fun x => G x i) := by
    simp_rw [Finset.mul_sum]
    rw [Summable.tsum_finsetSum (fun i _ => hsi i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [(hsi i).tsum_eq_zero_add]
    simp only [pow_zero, one_mul, primalEnergy]
  have habel : (∑ i, primalEnergy Q q (fun x => G x i)) =
      vecEnergy Q G + (q - 1) * ∑' j, q ^ j * residualEnergy Q j G := by
    simp_rw [primalEnergy_eq_abel Q hq1 (hG _) (hs _)]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    congr 1
    congr 1
    unfold residualEnergy
    simp_rw [Finset.mul_sum]
    exact (Summable.tsum_finsetSum (fun i _ => hs i)).symm
  have hbound : (∑' j, q ^ j * residualEnergy Q j G) ≤ minSeries q A H :=
    hsR.tsum_le_tsum (fun j => mul_le_mul_of_nonneg_left (hr j) (pow_nonneg hq0 j)) hmajor
  unfold haarPrimal
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k =>
    mul_nonneg (pow_nonneg hq0 k) (Finset.sum_nonneg (fun _ _ => energy_nonneg _ _))) htotal]
  apply ENNReal.ofReal_le_ofReal
  rw [hfull, habel]
  exact add_le_add he (mul_le_mul_of_nonneg_left hbound (sub_nonneg.mpr hq1.le))

end GMCExplicitDelta.Localization.LocWeights
