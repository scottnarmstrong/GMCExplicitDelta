module

public import GMCExplicitDelta.Proofs.FineSensitivity.Remainder

/-! # The canonical energy budgets for measurable gradient representatives -/

@[expose] public section

open Homogenization Homogenization.Book.Ch02 MeasureTheory Matrix
open SubdiffusiveProcess.CoarseGrainingVocab (ScalarCoeffOnData)

namespace GMCExplicitDelta.Assembly

variable {d : ℕ} {U : Domain d}

theorem fine_measured_energy_budgets {a : Vec d → ℝ}
    (h : ScalarCoeffOnData U a) {e : Vec d} (he : e ⬝ᵥ e = 1) :
    (∫ x, a x * vecNormSq (fineMeasGradient h.toCoeffOn false e x -
        fineMeasGradient h.toCoeffOn true e x) ∂fineDomainMeasure U) =
        2 * responseJ U h.toCoeffOn e e + 4 ∧
      (1/2 : ℝ) * (∫ x, a x * vecNormSq (fineMeasGradient h.toCoeffOn true e x)
        ∂fineDomainMeasure U) ≤ responseJ U h.toCoeffOn e e + 1 := by
  let v := canonicalMaximizer (responseExistenceTheory U h.toCoeffOn) e 0
  let u := canonicalMaximizer (responseExistenceTheory U h.toCoeffOn) 0 e
  have hv : fineMeasGradient h.toCoeffOn false e =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      v.toSolution.toH1.grad := fineMeasGradient_ae h.toCoeffOn false e
  have hu : fineMeasGradient h.toCoeffOn true e =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      u.toSolution.toH1.grad := fineMeasGradient_ae h.toCoeffOn true e
  have h₁ := Coarse.average_congr_ae (U := U) (show
      (fun x => a x * vecNormSq (fineMeasGradient h.toCoeffOn false e x -
        fineMeasGradient h.toCoeffOn true e x)) =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      (fun x => a x * vecNormSq (v.toSolution.toH1.grad x - u.toSolution.toH1.grad x)) from by
    filter_upwards [hv, hu] with x hx hy
    rw [hx, hy])
  have h₂ := Coarse.average_congr_ae (U := U) (hu.mono fun x hx =>
    congrArg (fun g => a x * vecNormSq g) hx)
  simp_rw [fine_average_eq_integral] at h₁ h₂
  rw [h₁, h₂, ← fine_average_eq_integral, ← fine_average_eq_integral]
  exact fine_old_energy_budgets h he v.isMaximizer u.isMaximizer

end GMCExplicitDelta.Assembly
