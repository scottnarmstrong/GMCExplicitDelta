module

public import GMCExplicitDelta.Averaging.MeanSensitiveMoments
public import GMCExplicitDelta.Insertion.FreshBandOperator

/-! # The old directional moment profile (I5) -/

@[expose] public section

open MeasureTheory

namespace GMCExplicitDelta.Insertion

/-- I5, including the probability-normalized zeroth moment, with the exact row profile. -/
theorem integral_pow_le_profile {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {d : ℕ} (row : Contract.Row d) {D F : ℝ}
    (hpos : 0 < row.Fnext F) (hle : row.Fnext F ≤ row.Dnext D F)
    {X : Ω → ℝ} (hX : ∀ ω, 0 ≤ X ω) (hm : Measurable X)
    (hint : Integrable (fun ω => X ω ^ (32 : ℕ)) μ)
    (hmean : ∫ ω, X ω ∂μ ≤ row.Fnext F)
    (hmoment : ∫ ω, X ω ^ (32 : ℕ) ∂μ ≤ row.Dnext D F ^ (32 : ℕ))
    (r : Fin 33) :
    ∫ ω, X ω ^ (r : ℕ) ∂μ ≤ row.profile D F r := by
  by_cases hr : (r : ℕ) = 0
  · simp only [hr, pow_zero, integral_const, probReal_univ, smul_eq_mul, one_mul,
      Contract.Row.profile, ↓reduceIte, le_refl]
  · have hr1 : 1 ≤ (r : ℕ) := by omega
    have hr32 : (r : ℕ) ≤ 32 := by omega
    have hb := Averaging.moment_interp (by norm_num : 2 ≤ 32) hr1 hr32
      hpos (lt_of_lt_of_le hpos hle) hX hm hint hmean hmoment
    simpa only [Contract.Row.profile, ite_eq_right hr, Nat.cast_ofNat, show (32 : ℝ) - 1 = 31 by norm_num]
      using hb

/-- Integrate the exact band polynomial against the old directional profile. -/
theorem integral_band_polynomial_le_freshMoment
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {d : ℕ} (row : Contract.Row d) {D F : ℝ}
    (hpos : 0 < row.Fnext F) (hle : row.Fnext F ≤ row.Dnext D F)
    {X : Ω → ℝ} (hX : ∀ ω, 0 ≤ X ω) (hm : Measurable X)
    (hint : Integrable (fun ω => X ω ^ (32 : ℕ)) μ)
    (hmean : ∫ ω, X ω ∂μ ≤ row.Fnext F)
    (hmoment : ∫ ω, X ω ^ (32 : ℕ) ∂μ ≤ row.Dnext D F ^ (32 : ℕ))
    (δ : ℝ) (hc : ∀ r : Fin 33, 0 ≤ Contract.bandRow δ row.h r) :
    (∫ ω, ∑ r : Fin 33, Contract.bandRow δ row.h r * X ω ^ (r : ℕ) ∂μ) ≤
      row.freshMoment δ D F := by
  have hi (r : Fin 33) : Integrable (fun ω => X ω ^ (r : ℕ)) μ :=
    Averaging.integrable_pow_of_le (by omega) hX hm hint
  rw [integral_finsetSum _ (fun r _ => (hi r).const_mul _)]
  unfold Contract.Row.freshMoment
  refine Finset.sum_le_sum fun r _ => ?_
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left
    (integral_pow_le_profile row hpos hle hX hm hint hmean hmoment r) (hc r)

end GMCExplicitDelta.Insertion
