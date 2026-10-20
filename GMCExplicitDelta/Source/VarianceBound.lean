module

public import GMCExplicitDelta.Source.VarianceCov

/-!
# The six-term lower bound

For the abstract diagonal process, `E (a+b+c)² ≥ 35 s + (13 + 2√2) r`, where `s = E G(0)²`,
`r = E G'(0)²` (step S6).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace GMCExplicitDelta.Source

open MeasureTheory ProbabilityTheory

namespace DiagProc

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {G G' : ℝ → Ω → ℝ} {a b c : Ω → ℝ} (H : DiagProc P G G' a b c)
include H

theorem continuous_G (ω : Ω) : Continuous fun t => G t ω :=
  continuous_iff_continuousAt.2 fun t => (H.hasDeriv ω t).continuousAt

/-- Centering: `E G(0) G'(0) = 0`. -/
theorem cross_zero : ∫ ω, G 0 ω * G' 0 ω ∂P = 0 := by
  have hmeas : Measurable (Function.uncurry fun (τ : ℝ) (ω : Ω) => 2 * (G τ ω * G' τ ω)) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun ω => continuous_const.mul ((H.continuous_G ω).mul (H.cont' ω)))
      (fun τ => measurable_const.mul ((H.mG τ).mul (H.mG' τ)))
  obtain ⟨_, hS⟩ := integral_intervalIntegral_swap (P := P) hmeas zero_le_one
    (B := fun ω => 2 * (a ω * b ω)) (H.int_ab.const_mul 2) (fun ω t ht => by
      rw [abs_mul, abs_mul, abs_two]
      have := H.bG ω t ht
      have := H.bG' ω t ht
      have : |G t ω| * |G' t ω| ≤ a ω * b ω :=
        mul_le_mul (H.bG ω t ht) (H.bG' ω t ht) (abs_nonneg _) (H.a_nonneg ω)
      linarith)
  have hL : ∫ τ in (0:ℝ)..1, (∫ ω, 2 * (G τ ω * G' τ ω) ∂P) = 2 * ∫ ω, G 0 ω * G' 0 ω ∂P := by
    have : ∀ τ : ℝ, ∫ ω, 2 * (G τ ω * G' τ ω) ∂P = 2 * ∫ ω, G 0 ω * G' 0 ω ∂P := fun τ => by
      rw [integral_const_mul]
      congr 1
      simpa only [zero_add] using H.shift_GG' 0 0 τ
    simp_rw [this]
    simp
  have hR : ∀ ω, ∫ τ in (0:ℝ)..1, 2 * (G τ ω * G' τ ω) = G 1 ω ^ 2 - G 0 ω ^ 2 := fun ω => by
    have hd : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun s => G s ω ^ 2) (2 * (G x ω * G' x ω)) x :=
      fun x _ => by
        have := (H.hasDeriv ω x).pow 2
        convert this using 1; simp; ring
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((continuous_const.mul ((H.continuous_G ω).mul (H.cont' ω))).intervalIntegrable _ _)
  have hE : ∫ ω, (∫ τ in (0:ℝ)..1, 2 * (G τ ω * G' τ ω)) ∂P = 0 := by
    simp_rw [hR]
    rw [integral_sub (H.int_sq_G 1) H.int_sq_G0, H.integral_sq_G 1]; simp
  rw [hL, hE] at hS
  linarith

end DiagProc

end GMCExplicitDelta.Source
