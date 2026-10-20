module

public import GMCExplicitDelta.Proofs.EnergyTest.Projection

/-! Vector Haar duality with the exact nonnegative series used in localization. -/

@[expose] public section

open Homogenization MeasureTheory Filter
open scoped Topology ENNReal

namespace GMCExplicitDelta.Localization.EnergyTest

variable {d : ℕ}

theorem ofReal_partialEnergy_sum_le (Q : TriadicCube d) {q : ℝ} (hq : 0 ≤ q)
    (N : ℕ) (F : Vec d → Vec d) :
    ENNReal.ofReal (∑ i, Haar.partialEnergy Q q N (fun x => F x i)) ≤ haarPrimal Q q F := by
  have he : (∑ i, Haar.partialEnergy Q q N (fun x => F x i)) =
      ∑ k ∈ Finset.range (N + 1), q ^ k * ∑ i, Haar.energy Q (cubeIncrement Q k fun x => F x i) := by
    unfold Haar.partialEnergy
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  rw [he, ENNReal.ofReal_sum_of_nonneg (fun k _ => mul_nonneg (pow_nonneg hq k)
    (Finset.sum_nonneg fun i _ => Haar.energy_nonneg Q _))]
  exact ENNReal.sum_le_tsum _

/-- H1(a) for vector fields, without assuming either infinite Haar series finite. -/
theorem ofReal_vector_pairing_sq_le (Q : TriadicCube d) {q : ℝ} (hq : 1 < q)
    {F G : Vec d → Vec d}
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q)) :
    ENNReal.ofReal |cubeAverage Q (fun x => vecDot (F x) (G x))| ^ 2 ≤
      haarDual Q q F * haarPrimal Q q G := by
  have hq0 : 0 ≤ q := le_trans zero_le_one hq.le
  let a : ℕ → ℝ := fun N => ∑ i, Haar.pairing Q
    (cubeProjection Q N fun x => F x i) (cubeProjection Q N fun x => G x i)
  have halim : Tendsto a atTop (𝓝 (∑ i, Haar.pairing Q (fun x => F x i) (fun x => G x i))) :=
    tendsto_finsetSum _ fun i _ => pairing_projection_tendsto Q (hF i) (hG i)
  have havg : (∑ i, Haar.pairing Q (fun x => F x i) (fun x => G x i)) =
      cubeAverage Q (fun x => vecDot (F x) (G x)) := by
    simp only [Haar.pairing, cubeAverage_eq_integral_normalizedCubeMeasure, vecDot]
    exact (integral_finsetSum _ (fun i _ => (hF i).integrable_mul (hG i))).symm
  rw [havg] at halim
  apply le_of_tendsto ((ENNReal.continuous_pow 2).tendsto _ |>.comp (ENNReal.tendsto_ofReal halim.abs))
  apply Filter.Eventually.of_forall
  intro N
  let A := ∑ i, Haar.partialEnergy Q q⁻¹ N (fun x => F x i)
  let B := ∑ i, Haar.partialEnergy Q q N (fun x => G x i)
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ =>
    mul_nonneg (pow_nonneg (inv_nonneg.mpr hq0) k) (Haar.energy_nonneg Q _)
  have hB : 0 ≤ B := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ =>
    mul_nonneg (pow_nonneg hq0 k) (Haar.energy_nonneg Q _)
  have hs : a N ^ 2 ≤ A * B := by
    have hh := pow_le_pow_left₀ (abs_nonneg (a N)) (vector_projection_pairing_le Q hq N hF hG) 2
    change |a N| ^ 2 ≤ (Real.sqrt A * Real.sqrt B) ^ 2 at hh
    simpa only [sq_abs, mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB] using hh
  calc
    _ = ENNReal.ofReal (a N ^ 2) := by
      change ENNReal.ofReal |a N| ^ (2 : ℕ) = _
      rw [← ENNReal.ofReal_pow (abs_nonneg (a N)) 2, sq_abs]
    _ ≤ ENNReal.ofReal (A * B) := ENNReal.ofReal_le_ofReal hs
    _ = ENNReal.ofReal A * ENNReal.ofReal B := ENNReal.ofReal_mul hA
    _ ≤ _ := mul_le_mul' (ofReal_partialEnergy_sum_le Q (inv_nonneg.mpr hq0) N F)
      (ofReal_partialEnergy_sum_le Q hq0 N G)

end GMCExplicitDelta.Localization.EnergyTest
