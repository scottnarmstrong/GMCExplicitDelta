module

public import GMCExplicitDelta.Proofs.ProjPoincare.Digits

/-! Conditional variance on the three child digits. -/
@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace GMCExplicitDelta.Localization.ProjPoincare

theorem digit_pairwise_variance (F : Fin 3 → ℝ) :
    (1 / 2 : ℝ) * (∫ r, ∫ s, (F s - F r) ^ 2 ∂digitMeasure ∂digitMeasure) =
      ∫ r, (F r - ∫ s, F s ∂digitMeasure) ^ 2 ∂digitMeasure := by
  simp_rw [digit_integral]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  ring

/-- Efron--Stein with the resampling energy written as a variance in one digit. -/
theorem child_digits_conditional_variance (n : ℕ)
    (F : (Fin (n + 1) → Fin 3) → ℝ) :
    (∫ x, (F x - ∫ y, F y ∂(Measure.pi fun _ => digitMeasure)) ^ 2
      ∂(Measure.pi fun _ => digitMeasure)) ≤
    ∑ i : Fin (n + 1), ∫ z, ∫ r,
      (F (i.insertNth r z) - ∫ s, F (i.insertNth s z) ∂digitMeasure) ^ 2
        ∂digitMeasure ∂(Measure.pi fun _ : Fin n => digitMeasure) := by
  obtain ⟨M, hM⟩ := Finite.exists_le (fun x => |F x|)
  have h := Homogenization.efronStein_pi (fun _ : Fin (n + 1) => digitMeasure)
    (F := F) (Measurable.of_discrete (f := F)) hM
  rw [variance_eq_integral (Measurable.of_discrete (f := F)).aemeasurable] at h
  refine h.trans_eq ?_
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [digitPi_peel n i, ← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  simp only [Fin.update_insertNth]
  exact digit_pairwise_variance (fun r => F (i.insertNth r z))

end GMCExplicitDelta.Localization.ProjPoincare
