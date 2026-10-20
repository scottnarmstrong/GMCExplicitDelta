module

public import GMCExplicitDelta.Proofs.LocWeights.Weights
public import GMCExplicitDelta.Haar.MultiplierTensor
public import GMCExplicitDelta.Localization.CoreDefs

/-! The cutoff's classical C¹ properties used in the energy test. -/

@[expose] public section

open Homogenization Real
open scoped Topology

namespace GMCExplicitDelta.Localization.EnergyTest

variable {d : ℕ}

theorem cubeCutoff_contDiff (row : Contract.Row d) (hO : row.Obligations) (n : ℕ) :
    ContDiff ℝ 1 (cubeCutoff row n) := by
  unfold cubeCutoff Haar.cutoffProduct
  apply contDiff_prod
  intro i _
  exact (Haar.cutoffProfile_contDiff (LocWeights.omega_bounds row hO).2).comp (by fun_prop)

theorem cubeCutoff_fderiv (row : Contract.Row d) (hO : row.Obligations) (n : ℕ)
    (x : Vec d) (i : Fin d) :
    (fderiv ℝ (cubeCutoff row n) x) (basisVec i) = cubeCutoffGrad row n x i := by
  let S := (3 : ℝ) ^ n
  let f : Fin d → ℝ → ℝ := fun _ y => Haar.cutoffProfile row.omegaEff (y / S)
  have hd (j : Fin d) (y : ℝ) : HasDerivAt (f j)
      (Haar.cutoffSlope row.omegaEff (y / S) / S) y := by
    have hh := (Haar.cutoffProfile_hasDerivAt (LocWeights.omega_bounds row hO).2 (y / S)).comp y
      ((hasDerivAt_id y).div_const S)
    change HasDerivAt (f j) _ y at hh
    convert hh using 1
    simp only [div_eq_mul_inv, mul_comm, one_mul]
  have he : cubeCutoff row n = Haar.tensorMultiplier f := rfl
  rw [he, Haar.tensorMultiplier_fderiv_basis f (fun j y => (hd j y).differentiableAt)]
  unfold Haar.tensorDerivative cubeCutoffGrad Haar.cutoffGradient
  change deriv (f i) (x i) * (∏ j ∈ Finset.univ.erase i, f j (x j)) = _
  rw [(hd i (x i)).deriv]
  change (Haar.cutoffSlope row.omegaEff (x i / S) / S) *
      (∏ j ∈ Finset.univ.erase i, Haar.cutoffProfile row.omegaEff (x j / S)) = _
  ring

theorem cos_rescaled_pos {ω t : ℝ} (hω : 0 < ω) (ht : -ω < t ∧ t < ω) :
    0 < cos (π / (2 * ω) * t) := by
  have hfac : 0 < π / (2 * ω) := div_pos pi_pos (by positivity)
  have he : π / (2 * ω) * ω = π / 2 := by field_simp [hω.ne']
  have hl := mul_lt_mul_of_pos_left ht.1 hfac
  have hr := mul_lt_mul_of_pos_left ht.2 hfac
  rw [mul_neg, he] at hl
  rw [he] at hr
  exact cos_pos_of_mem_Ioo ⟨hl, hr⟩

theorem cutoffProfile_pos {ω y : ℝ} (hω : 0 < ω) (_hω1 : ω ≤ 1 / 2)
    (hy : |y| < 1 / 2) : 0 < Haar.cutoffProfile ω y := by
  have hy' := abs_lt.mp hy
  unfold Haar.cutoffProfile Haar.joinAt
  split
  · rename_i hl
    exact cos_rescaled_pos hω ⟨by linarith, by linarith⟩
  · split
    · exact zero_lt_one
    · rename_i hl hr
      exact cos_rescaled_pos hω ⟨by linarith, by linarith⟩

theorem cubeCutoff_pos (row : Contract.Row d) (hO : row.Obligations) (n : ℕ)
    {x : Vec d} (hx : x ∈ openCubeSet (originCube d (n : ℤ))) : 0 < cubeCutoff row n x := by
  unfold cubeCutoff Haar.cutoffProduct
  apply Finset.prod_pos
  intro i _
  apply cutoffProfile_pos (LocWeights.omega_bounds row hO).1 (LocWeights.omega_bounds row hO).2
  have hi := mem_openCubeSet_originCube_iff.mp hx i
  rw [zpow_natCast] at hi
  have hS : 0 < (3 : ℝ) ^ n := by positivity
  exact abs_lt.mpr ⟨(lt_div_iff₀ hS).mpr (by linarith only [hi.1]),
    (div_lt_iff₀ hS).mpr hi.2⟩

end GMCExplicitDelta.Localization.EnergyTest
