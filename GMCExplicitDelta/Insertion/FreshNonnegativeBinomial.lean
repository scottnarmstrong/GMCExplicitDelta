module

public import GMCExplicitDelta.Insertion.FreshSymmetrizedMoment

/-! # The even binomial sum as a finite sum of nonnegative moments -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace GMCExplicitDelta.Insertion

theorem ofReal_even_binomial_sum {A : ℝ} (hA : 0 ≤ A) (O : ℝ) (p : ℕ) :
    ENNReal.ofReal (∑ i ∈ Finset.range (p + 1),
      if Even i then (p.choose i : ℝ) * A ^ (p - i) * |O| ^ i else 0) =
      ∑ i ∈ Finset.range (p + 1), if Even i then
        ENNReal.ofReal (p.choose i : ℝ) * ENNReal.ofReal A ^ (p - i) *
          ENNReal.ofReal |O| ^ i else 0 := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by split_ifs <;> positivity)]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs
  · rw [ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hA _)),
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_pow hA,
      ENNReal.ofReal_pow (abs_nonneg _)]
  · exact ENNReal.ofReal_zero

/-- Evaluate the nonnegative even-binomial polynomial by finite Tonelli. -/
theorem lintegral_even_binomial_sum {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {A O : Ω → ℝ} (hA : Measurable A) (hO : Measurable O) (hA0 : ∀ ω, 0 ≤ A ω) (p : ℕ) :
    (∫⁻ ω, ENNReal.ofReal (∑ i ∈ Finset.range (p + 1),
      if Even i then (p.choose i : ℝ) * A ω ^ (p - i) * |O ω| ^ i else 0) ∂μ) =
      ∑ i ∈ Finset.range (p + 1), if Even i then ENNReal.ofReal (p.choose i : ℝ) *
        (∫⁻ ω, ENNReal.ofReal (A ω) ^ (p - i) * ENNReal.ofReal |O ω| ^ i ∂μ) else 0 := by
  have ha := hA.ennreal_ofReal
  have ho := (continuous_abs.measurable.comp hO).ennreal_ofReal
  have hm (i : ℕ) : Measurable (fun ω => if Even i then
      ENNReal.ofReal (p.choose i : ℝ) * ENNReal.ofReal (A ω) ^ (p - i) *
        ENNReal.ofReal |O ω| ^ i else 0) := by
    by_cases hi : Even i
    · simp only [ite_eq_left hi]
      exact (measurable_const.mul (ha.pow_const _)).mul (ho.pow_const _)
    · simp only [ite_eq_right hi]
      exact measurable_const
  calc
    _ = ∫⁻ ω, ∑ i ∈ Finset.range (p + 1), if Even i then
        ENNReal.ofReal (p.choose i : ℝ) * ENNReal.ofReal (A ω) ^ (p - i) *
          ENNReal.ofReal |O ω| ^ i else 0 ∂μ :=
      lintegral_congr fun ω => ofReal_even_binomial_sum (hA0 ω) (O ω) p
    _ = _ := by
      rw [lintegral_finsetSum _ (fun i _ => hm i)]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : Even i
      · simp only [ite_eq_left hi]
        have hp : Measurable (fun ω => ENNReal.ofReal (A ω) ^ (p - i) *
            ENNReal.ofReal |O ω| ^ i) := (ha.pow_const _).mul (ho.pow_const _)
        simp only [mul_assoc]
        exact lintegral_const_mul _ hp
      · simp only [ite_eq_right hi, lintegral_zero]

end GMCExplicitDelta.Insertion
