module

public import GMCExplicitDelta.Proofs.FineSensitivity.Sphere
public import GMCExplicitDelta.Contract.DerivedHistory

/-! # Exact sphere-factor algebra in G3 -/

@[expose] public section

open GMCExplicitDelta.Insertion
open scoped ENNReal

namespace GMCExplicitDelta.Assembly

theorem fine_sphereFactor_nonneg (d : ℕ) : 0 ≤ Contract.sphereFactor d := by
  unfold Contract.sphereFactor
  apply Real.rpow_nonneg
  unfold Contract.sphereFactorPow
  split_ifs <;> positivity

theorem fine_sphereFactor_pow {d : ℕ} (hd : d ∈ ({2,3,4} : Finset ℕ)) :
    Contract.sphereFactor d ^ (32 : ℕ) = sphereMomentRatio d 32 := by
  have h : 0 ≤ (Contract.sphereFactorPow d : ℝ) := by
    unfold Contract.sphereFactorPow
    split_ifs <;> positivity
  rw [fine_sphereMomentRatio_eq hd]
  unfold Contract.sphereFactor
  rw [← Real.rpow_natCast, ← Real.rpow_mul h]
  norm_num

/-- The conditional C13 bound factors exactly into a fixed constant and the old defect. -/
theorem fine_conditional_constant_eq {d : ℕ} (hd : d ∈ ({2,3,4} : Finset ℕ))
    {J W : ℝ} (hJ : 0 ≤ J) (hW : 0 ≤ W) :
    ENNReal.ofReal (sphereMomentRatio d 32 * ((J+1)*W)^32) =
      (ENNReal.ofReal (Contract.sphereFactor d) * ENNReal.ofReal W) ^ (32 : ℝ) *
        (1+ENNReal.ofReal J) ^ (32 : ℝ) := by
  have hsum : 1+ENNReal.ofReal J = ENNReal.ofReal (1+J) := by
    rw [ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1) hJ, ENNReal.ofReal_one]
  rw [← ENNReal.ofReal_mul (fine_sphereFactor_nonneg d), hsum]
  rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (fine_sphereFactor_nonneg d) hW) (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg (by positivity : 0 ≤ 1+J) (by norm_num)]
  norm_num only [Real.rpow_ofNat]
  rw [← ENNReal.ofReal_mul (pow_nonneg (mul_nonneg (fine_sphereFactor_nonneg d) hW) 32)]
  congr 1
  simp only [mul_pow, fine_sphereFactor_pow hd]
  ring

end GMCExplicitDelta.Assembly
