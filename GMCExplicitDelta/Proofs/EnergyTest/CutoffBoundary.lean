module

public import GMCExplicitDelta.Proofs.EnergyTest.Cutoff

/-! Boundary vanishing of the actual plateau cutoff. -/

@[expose] public section

open Homogenization
open scoped Topology

namespace GMCExplicitDelta.Localization.EnergyTest

variable {d : ℕ}

theorem cubeCutoff_boundary_zero (row : Contract.Row d) (hO : row.Obligations) (n : ℕ)
    {x : Vec d} (hx : x ∈ closure (openCubeSet (originCube d (n : ℤ))))
    (hxU : x ∉ openCubeSet (originCube d (n : ℤ))) : cubeCutoff row n x = 0 := by
  let S := (3 : ℝ) ^ n
  have hS : S ≠ 0 := by dsimp only [S]; positivity
  have hcl (i : Fin d) : -(1 / 2 : ℝ) * S ≤ x i ∧ x i ≤ (1 / 2 : ℝ) * S := by
    have hsub : closure (openCubeSet (originCube d (n : ℤ))) ⊆
        {y : Vec d | -(1 / 2 : ℝ) * S ≤ y i ∧ y i ≤ (1 / 2 : ℝ) * S} := by
      apply closure_minimal
      · intro y hy
        have hh := mem_openCubeSet_originCube_iff.mp hy i
        rw [zpow_natCast] at hh
        exact ⟨hh.1.le, hh.2.le⟩
      · exact (isClosed_le continuous_const (continuous_apply i)).inter
          (isClosed_le (continuous_apply i) continuous_const)
    exact hsub hx
  have hface : ∃ i, x i = -(1 / 2 : ℝ) * S ∨ x i = (1 / 2 : ℝ) * S := by
    by_contra hh
    push Not at hh
    apply hxU
    apply mem_openCubeSet_originCube_iff.mpr
    intro i
    rw [zpow_natCast]
    exact ⟨lt_of_le_of_ne (hcl i).1 (hh i).1.symm, lt_of_le_of_ne (hcl i).2 (hh i).2⟩
  unfold cubeCutoff
  apply Haar.cutoffProduct_eq_zero_of_face (LocWeights.omega_bounds row hO).1 (LocWeights.omega_bounds row hO).2
  obtain ⟨i, hi | hi⟩ := hface
  · refine ⟨i, Or.inr ?_⟩
    change x i / S = -(1 / 2 : ℝ)
    rw [hi, mul_div_cancel_right₀ _ hS]
  · refine ⟨i, Or.inl ?_⟩
    change x i / S = (1 / 2 : ℝ)
    rw [hi, mul_div_cancel_right₀ _ hS]

end GMCExplicitDelta.Localization.EnergyTest
