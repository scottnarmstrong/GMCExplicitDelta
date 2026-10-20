module

public import GMCExplicitDelta.Insertion.FreshFormalPositive
public import GMCExplicitDelta.Insertion.FreshFormalShift

/-! # The even and odd series of the scalar old-response reference -/

@[expose] public section

namespace GMCExplicitDelta.Insertion

/-- The old value plus the even fresh increment of the scalar reference. -/
noncomputable def oldEvenReference (j : ℝ) : PowerSeries ℝ :=
  PowerSeries.C j + PowerSeries.C (j + 1) * (formalCosh - 1)

/-- The odd fresh increment with its sharp deterministic mass. -/
noncomputable def oldOddReference (j : ℝ) : PowerSeries ℝ :=
  PowerSeries.C (Real.sqrt (j * (j + 2))) * formalSinh

theorem oldEvenReference_coeff_nonneg {j : ℝ} (hj : 0 ≤ j) (n : ℕ) :
    0 ≤ PowerSeries.coeff n (oldEvenReference j) := by
  rw [oldEvenReference, map_add, PowerSeries.coeff_C_mul]
  apply add_nonneg
  · simp only [PowerSeries.coeff_C]
    split_ifs <;> positivity
  · exact mul_nonneg (add_nonneg hj (by norm_num)) (formalCosh_sub_one_coeff_nonneg n)

theorem oldOddReference_coeff_nonneg (j : ℝ) (n : ℕ) :
    0 ≤ PowerSeries.coeff n (oldOddReference j) := by
  rw [oldOddReference, PowerSeries.coeff_C_mul]
  exact mul_nonneg (Real.sqrt_nonneg _) (formalSinh_coeff_nonneg n)

theorem rescale_neg_C (a : ℝ) : PowerSeries.rescale (-1) (PowerSeries.C a) = PowerSeries.C a := by
  ext n
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
  by_cases hn : n = 0 <;> simp [hn]

theorem rescale_neg_formalCosh : PowerSeries.rescale (-1) formalCosh = formalCosh := by
  ext n
  rw [PowerSeries.coeff_rescale]
  by_cases hn : Even n
  · simp only [formalCosh, PowerSeries.coeff_mk, ite_eq_left hn, Even.neg_one_pow hn, one_mul]
  · simp only [formalCosh, PowerSeries.coeff_mk, ite_eq_right hn, mul_zero]

theorem rescale_neg_formalSinh : PowerSeries.rescale (-1) formalSinh = -formalSinh := by
  ext n
  rw [PowerSeries.coeff_rescale, map_neg]
  by_cases hn : Even n
  · simp only [formalSinh, PowerSeries.coeff_mk, ite_eq_left hn, mul_zero, neg_zero]
  · simp only [formalSinh, PowerSeries.coeff_mk, ite_eq_right hn,
      Odd.neg_one_pow (Nat.not_even_iff_odd.mp hn), neg_one_mul]

theorem rescale_neg_oldEvenReference (j : ℝ) :
    PowerSeries.rescale (-1) (oldEvenReference j) = oldEvenReference j := by
  simp only [oldEvenReference, map_add, map_mul, map_sub, map_one,
    rescale_neg_C, rescale_neg_formalCosh]

theorem rescale_neg_oldOddReference (j : ℝ) :
    PowerSeries.rescale (-1) (oldOddReference j) = -oldOddReference j := by
  simp only [oldOddReference, map_mul, rescale_neg_C, rescale_neg_formalSinh, mul_neg]

theorem oldReference_add_eq (j : ℝ) :
    oldEvenReference j + oldOddReference j = shiftedFormalCosh j - 1 :=
  (shiftedFormalCosh_sub_one_eq j).symm

end GMCExplicitDelta.Insertion
