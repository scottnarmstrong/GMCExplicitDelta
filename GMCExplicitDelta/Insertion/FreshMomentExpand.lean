module

public import GMCExplicitDelta.Insertion.FreshSymmetrizedMoment
public import Mathlib.Data.Nat.Choose.Sum

/-! # Nonnegative binomial expansion of spatial energy moments -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace GMCExplicitDelta.Insertion

/-- Expand the old constant and the even fresh energy inside a mixed moment. -/
theorem lintegral_const_add_pow_mul {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y : Ω → ℝ≥0∞} (hX : Measurable X) (hY : Measurable Y)
    (c : ℝ≥0∞) (p l : ℕ) :
    (∫⁻ ω, (c + X ω) ^ p * Y ω ^ l ∂μ) = ∑ k ∈ Finset.range (p + 1),
      (c ^ (p - k) * (p.choose k : ℝ≥0∞)) * ∫⁻ ω, X ω ^ k * Y ω ^ l ∂μ := by
  have he (ω : Ω) : (c + X ω) ^ p * Y ω ^ l = ∑ k ∈ Finset.range (p + 1),
      (c ^ (p - k) * (p.choose k : ℝ≥0∞)) * (X ω ^ k * Y ω ^ l) := by
    rw [add_comm c (X ω), add_pow, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hm (k : ℕ) : Measurable (fun ω =>
      (c ^ (p - k) * (p.choose k : ℝ≥0∞)) * (X ω ^ k * Y ω ^ l)) :=
    measurable_const.mul ((hX.pow_const k).mul (hY.pow_const l))
  calc
    _ = ∫⁻ ω, ∑ k ∈ Finset.range (p + 1),
        (c ^ (p - k) * (p.choose k : ℝ≥0∞)) * (X ω ^ k * Y ω ^ l) ∂μ := lintegral_congr he
    _ = _ := by
      rw [lintegral_finsetSum _ (fun k _ => hm k)]
      apply Finset.sum_congr rfl
      intro k _
      exact lintegral_const_mul _ ((hX.pow_const k).mul (hY.pow_const l))

end GMCExplicitDelta.Insertion
