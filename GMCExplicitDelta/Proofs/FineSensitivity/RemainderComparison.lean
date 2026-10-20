module

public import GMCExplicitDelta.Proofs.FineSensitivity.Remainder

/-! # C12 compared with the positive remainder matrix -/

@[expose] public section

open Homogenization Homogenization.Book.Ch02 MeasureTheory Matrix
open SubdiffusiveProcess.CoarseGrainingVocab (ScalarCoeffOnData)

namespace GMCExplicitDelta.Assembly

variable {d : ℕ} {U : Domain d}

theorem responseJ_le_fineRemainderMatrix {a a' ρ : Vec d → ℝ}
    (h : ScalarCoeffOnData U a) (h' : ScalarCoeffOnData U a')
    {η : ℝ} (hη : 0 < η) {e : Vec d} (he : e ⬝ᵥ e = 1)
    (hρ : ∀ x, 0 < ρ x) (hc : Continuous ρ)
    (hrel : ∀ᵐ x ∂volumeMeasureOn (U : Set (Vec d)), a' x = a x * ρ x) :
    responseJ U h'.toCoeffOn e e ≤ (1+η) * responseJ U h.toCoeffOn e e +
      Coarse.qf (fineRemainderMatrix h ρ η) e := by
  obtain ⟨i⟩ := Coarse.nonempty_fin_of_dot_one he
  let v := canonicalMaximizer (responseExistenceTheory U h.toCoeffOn) e 0
  let u := canonicalMaximizer (responseExistenceTheory U h.toCoeffOn) 0 e
  let V := v.toSolution.toH1.grad
  let W := u.toSolution.toH1.grad
  have hc₁ : Continuous (fun x => (ρ x - 1)^2 / (8*η)) := by fun_prop
  have hc₂ : Continuous (fun x => (ρ x + (ρ x)⁻¹ - 2)/2) := by
    exact ((hc.add (hc.inv₀ fun x => (hρ x).ne')).sub continuous_const).div_const 2
  have hD : GradMemL2On (U : Set (Vec d)) (fun x => V x - W x) :=
    fun j => (v.toSolution.toH1.gradMemL2 j).sub (u.toSolution.toH1.gradMemL2 j)
  have h₁ := Coarse.integrable_energy h i hD
  have h₂ := Coarse.integrable_energy h i u.toSolution.toH1.gradMemL2
  have hnorm₁ := (U.isDomain.toBoundedMeasurableDomain U.nonempty).integrable_normalizedVolume _ h₁
  have hnorm₂ := (U.isDomain.toBoundedMeasurableDomain U.nonempty).integrable_normalizedVolume _ h₂
  have hRnorm : Integrable (fineRemainderDensity a ρ η V W) (fineDomainMeasure U) := by
    convert (fine_integrable_mul_continuous hnorm₁ hc₁).add
      (fine_integrable_mul_continuous hnorm₂ hc₂) using 1
    funext x
    dsimp [fineRemainderDensity, vecNormSq, V, W]
    ring
  have hR : Integrable (fineRemainderDensity a ρ η V W)
      (volumeMeasureOn (U : Set (Vec d))) :=
    ((U.isDomain.toBoundedMeasurableDomain U.nonempty).integrable_normalizedVolume_iff _).mp hRnorm
  have hb := responseJ_le_fineRemainder h h' hη he v.isMaximizer u.isMaximizer
    (hrel.mono fun x hx => ⟨hρ x, hx⟩) hR
  have hv : fineMeasGradient h.toCoeffOn false e =ᵐ[volumeMeasureOn (U : Set (Vec d))] V :=
    fineMeasGradient_ae h.toCoeffOn false e
  have hu : fineMeasGradient h.toCoeffOn true e =ᵐ[volumeMeasureOn (U : Set (Vec d))] W :=
    fineMeasGradient_ae h.toCoeffOn true e
  have hav := Coarse.average_congr_ae (U := U) (show
      fineRemainderDensity a ρ η (fineMeasGradient h.toCoeffOn false e)
        (fineMeasGradient h.toCoeffOn true e) =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      fineRemainderDensity a ρ η V W from by
    filter_upwards [hv, hu] with x hx hy
    simp only [fineRemainderDensity, hx, hy])
  have heq : Coarse.qf (fineRemainderMatrix h ρ η) e =
      average U (fineRemainderDensity a ρ η V W) := by
    rw [fineRemainderMatrix_qf h i hρ hc η e, ← hav, fine_average_eq_integral]
    have hm₁ := fine_integrable_mul_continuous
      ((U.isDomain.toBoundedMeasurableDomain U.nonempty).integrable_normalizedVolume _
        (Coarse.integrable_energy h i (fun j =>
          (fineMeasGradient_memL2 h.toCoeffOn false e j).sub
            (fineMeasGradient_memL2 h.toCoeffOn true e j)))) hc₁
    have hm₂ := fine_integrable_mul_continuous
      ((U.isDomain.toBoundedMeasurableDomain U.nonempty).integrable_normalizedVolume _
        (Coarse.integrable_energy h i (fineMeasGradient_memL2 h.toCoeffOn true e))) hc₂
    have hpoint : fineRemainderDensity a ρ η (fineMeasGradient h.toCoeffOn false e)
        (fineMeasGradient h.toCoeffOn true e) =
        (fun x => (a x * vecNormSq (fineMeasGradient h.toCoeffOn false e x -
          fineMeasGradient h.toCoeffOn true e x)) * ((ρ x - 1)^2/(8*η)) +
          (a x * vecNormSq (fineMeasGradient h.toCoeffOn true e x)) *
            ((ρ x+(ρ x)⁻¹-2)/2)) := by
      funext x
      dsimp [fineRemainderDensity]
      ring
    change Integrable (fun x => (a x * vecNormSq
      (fineMeasGradient h.toCoeffOn false e x - fineMeasGradient h.toCoeffOn true e x)) *
        ((ρ x-1)^2/(8*η))) (fineDomainMeasure U) at hm₁
    change Integrable (fun x => (a x * vecNormSq (fineMeasGradient h.toCoeffOn true e x)) *
      ((ρ x+(ρ x)⁻¹-2)/2)) (fineDomainMeasure U) at hm₂
    rw [hpoint, integral_add hm₁ hm₂]
    congr 1 <;> apply integral_congr_ae <;> exact Filter.Eventually.of_forall (fun x => by ring)
  rwa [heq]

end GMCExplicitDelta.Assembly
