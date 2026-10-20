module

public import GMCExplicitDelta.Insertion.FreshEvenBinomial
public import GMCExplicitDelta.Insertion.FreshFunctionalLinear
public import GMCExplicitDelta.Insertion.FreshMomentEvaluation

/-! # Even binomial expansion of the symmetric band-moment functional -/

@[expose] public section

open scoped ENNReal

namespace GMCExplicitDelta.Insertion

/-- The symmetric functional depends only on the even Taylor coefficients. -/
theorem bandMomentApply_congr_even (δ : ℝ) (h : ℕ) {f g : PowerSeries ℝ}
    (hfg : ∀ n, PowerSeries.coeff (2 * n) f = PowerSeries.coeff (2 * n) g) :
    bandMomentApply δ h f = bandMomentApply δ h g := by
  rw [bandMomentApply_eq_even, bandMomentApply_eq_even]
  exact tsum_congr fun n => by rw [hfg n]

/-- The exact positive even-binomial expansion of the reference moment. -/
theorem bandMomentApply_add_pow (δ : ℝ) (h : ℕ) {f g : PowerSeries ℝ}
    (hf : ∀ n, 0 ≤ PowerSeries.coeff n f) (hg : ∀ n, 0 ≤ PowerSeries.coeff n g)
    (he : PowerSeries.rescale (-1) f = f) (ho : PowerSeries.rescale (-1) g = -g)
    (p : ℕ) :
    bandMomentApply δ h ((f + g) ^ p) = ∑ i ∈ Finset.range (p + 1),
      if Even i then ENNReal.ofReal (p.choose i : ℝ) *
        bandMomentApply δ h (f ^ (p - i) * g ^ i) else 0 := by
  let term (i : ℕ) : PowerSeries ℝ :=
    if Even i then (p.choose i : PowerSeries ℝ) * f ^ (p - i) * g ^ i else 0
  let S : PowerSeries ℝ := ∑ i ∈ Finset.range (p + 1), term i
  have hneg : PowerSeries.rescale (-1) ((f + g) ^ p) = (f - g) ^ p := by
    rw [map_pow, map_add, he, ho, ← sub_eq_add_neg]
  have hc (n : ℕ) : PowerSeries.coeff (2 * n) ((f - g) ^ p) =
      PowerSeries.coeff (2 * n) ((f + g) ^ p) := by
    rw [← hneg, PowerSeries.coeff_rescale, Even.neg_one_pow (even_two_mul n), one_mul]
  have heq : bandMomentApply δ h ((f + g) ^ p) = bandMomentApply δ h S := by
    apply bandMomentApply_congr_even
    intro n
    have hh := congrArg (PowerSeries.coeff (2 * n)) (add_pow_add_sub_pow f g p)
    change PowerSeries.coeff (2 * n) ((f + g) ^ p + (f - g) ^ p) =
      PowerSeries.coeff (2 * n) (2 * S) at hh
    rw [map_add, hc, PowerSeries.coeff_ofNat_mul] at hh
    linarith only [hh]
  have hterm (i n : ℕ) : 0 ≤ PowerSeries.coeff n (term i) := by
    dsimp only [term]
    split_ifs
    · rw [mul_assoc, PowerSeries.coeff_natCast_mul]
      exact mul_nonneg (Nat.cast_nonneg _) (Source.coeff_mul_nonneg
        (Source.coeff_pow_nonneg hf (p - i)) (Source.coeff_pow_nonneg hg i) n)
    · simp only [map_zero, le_refl]
  rw [heq]
  change coefficientFunctional (bandMomentFunctional δ h) S = _
  rw [coefficientFunctional_sum _ _ term (fun i _ n => hterm i n)]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [term]
  split_ifs with hi
  · have hh : (p.choose i : PowerSeries ℝ) = PowerSeries.C (p.choose i : ℝ) := by simp
    rw [mul_assoc, hh, coefficientFunctional_C_mul _ (Nat.cast_nonneg _)]
    rfl
  · simp only [coefficientFunctional, map_zero, ENNReal.ofReal_zero, zero_mul, tsum_zero]

end GMCExplicitDelta.Insertion
