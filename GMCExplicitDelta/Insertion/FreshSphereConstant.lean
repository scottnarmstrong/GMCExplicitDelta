module

public import GMCExplicitDelta.Insertion.SphereConstants
public import GMCExplicitDelta.Contract.Row

/-! # The exact C13 coefficient used by the fresh-return contract -/

@[expose] public section

namespace GMCExplicitDelta.Insertion

/-- The finite Gaussian ratio is the literal rational constant in `row.sym`. -/
theorem sphereMomentRatio_eq_sphereFactorPow {d : ℕ}
    (hd : d ∈ ({2, 3, 4} : Finset ℕ)) :
    sphereMomentRatio d 32 = (Contract.sphereFactorPow d : ℝ) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl
  · rw [sphereMomentRatio_two_32]
    norm_num [Contract.sphereFactorPow]
  · rw [sphereMomentRatio_three_32]
    norm_num [Contract.sphereFactorPow]
  · rw [sphereMomentRatio_four_32]
    norm_num [Contract.sphereFactorPow]

end GMCExplicitDelta.Insertion
