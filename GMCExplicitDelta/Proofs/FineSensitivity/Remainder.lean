module

public import GMCExplicitDelta.Proofs.FineSensitivity.GradientEnergy
public import GMCExplicitDelta.Proofs.FineSensitivity.Young

/-! # The fixed-old-sample positive remainder matrix -/

@[expose] public section

open Homogenization Homogenization.Book.Ch02 MeasureTheory Matrix
open SubdiffusiveProcess.CoarseGrainingVocab (ScalarCoeffOnData)
open scoped Matrix.Norms.Elementwise

namespace GMCExplicitDelta.Assembly

noncomputable local instance w3dRemainderContinuousENorm {n : ℕ} : ContinuousENorm (Matrix (Fin n) (Fin n) ℝ) :=
  SeminormedAddGroup.toContinuousENorm

variable {d : ℕ} {U : Domain d}

/-- Difference of primal and dual old gradient matrices. -/
noncomputable def fineDifferenceMatrix (a : CoeffOn U) (x : Vec d) : Mat d :=
  fineGradientMatrix a false x - fineGradientMatrix a true x

theorem fineDifferenceMatrix_mulVec (a : CoeffOn U) (x e : Vec d) :
    fineDifferenceMatrix a x *ᵥ e =
      fineMeasGradient a false e x - fineMeasGradient a true e x := by
  rw [fineDifferenceMatrix, Matrix.sub_mulVec, fineGradientMatrix_mulVec,
    fineGradientMatrix_mulVec]

theorem fineDifferenceMatrix_memL2 (a : CoeffOn U) (i : Fin d) :
    GradMemL2On (U : Set (Vec d)) (fun x => fineDifferenceMatrix a x *ᵥ Pi.single i 1) := by
  intro j
  have heq : (fun x => (fineDifferenceMatrix a x *ᵥ Pi.single i 1) j) =
      (fun x => fineMeasGradient a false (Pi.single i 1) x j -
        fineMeasGradient a true (Pi.single i 1) x j) := by
    funext x
    rw [fineDifferenceMatrix_mulVec]
    rfl
  rw [heq]
  exact (fineMeasGradient_memL2 a false (Pi.single i 1) j).sub
    (fineMeasGradient_memL2 a true (Pi.single i 1) j)

/-- Positive matrix whose probes are the two Young remainders. -/
noncomputable def fineRemainderMatrix {a : Vec d → ℝ} (h : ScalarCoeffOnData U a)
    (ρ : Vec d → ℝ) (η : ℝ) : Mat d :=
  fineWeightedGram (fineDomainMeasure U) (fun x => a x * ((ρ x - 1)^2 / (8*η)))
      (fineDifferenceMatrix h.toCoeffOn) +
    fineWeightedGram (fineDomainMeasure U) (fun x => a x * ((ρ x + (ρ x)⁻¹ - 2)/2))
      (fineGradientMatrix h.toCoeffOn true)

theorem fineRemainderMatrix_posSemidef {a ρ : Vec d → ℝ}
    (h : ScalarCoeffOnData U a) (i : Fin d) {η : ℝ} (hη : 0 < η)
    (ha : ∀ x, 0 ≤ a x) (hρ : ∀ x, 0 < ρ x) (hc : Continuous ρ) :
    (fineRemainderMatrix h ρ η).PosSemidef := by
  have hc₁ : Continuous (fun x => (ρ x - 1)^2 / (8*η)) := by fun_prop
  have hc₂ : Continuous (fun x => (ρ x + (ρ x)⁻¹ - 2)/2) := by
    exact ((hc.add (hc.inv₀ fun x => (hρ x).ne')).sub continuous_const).div_const 2
  apply Matrix.PosSemidef.add
  · exact fineWeightedGram_posSemidef _ _ _
      (fine_integrable_gram h i (fineDifferenceMatrix_memL2 h.toCoeffOn) hc₁)
      (fun x => mul_nonneg (ha x) (div_nonneg (sq_nonneg _) (by positivity)))
  · exact fineWeightedGram_posSemidef _ _ _
      (fine_integrable_gram h i (fineGradientMatrix_memL2 h.toCoeffOn true) hc₂)
      (fun x => mul_nonneg (ha x) (by
        rw [fine_ratio_weight_eq (hρ x)]
        exact div_nonneg (mul_nonneg (inv_nonneg.mpr (hρ x).le) (sq_nonneg _)) (by norm_num)))

theorem fineRemainderMatrix_qf {a ρ : Vec d → ℝ}
    (h : ScalarCoeffOnData U a) (i : Fin d) (hρ : ∀ x, 0 < ρ x)
    (hc : Continuous ρ) (η : ℝ) (e : Vec d) :
    Coarse.qf (fineRemainderMatrix h ρ η) e =
      (∫ x, a x * ((ρ x-1)^2/(8*η)) *
        vecNormSq (fineMeasGradient h.toCoeffOn false e x -
          fineMeasGradient h.toCoeffOn true e x) ∂fineDomainMeasure U) +
      ∫ x, a x * ((ρ x+(ρ x)⁻¹-2)/2) *
        vecNormSq (fineMeasGradient h.toCoeffOn true e x) ∂fineDomainMeasure U := by
  have hc₁ : Continuous (fun x => (ρ x - 1)^2 / (8*η)) := by fun_prop
  have hc₂ : Continuous (fun x => (ρ x + (ρ x)⁻¹ - 2)/2) := by
    exact ((hc.add (hc.inv₀ fun x => (hρ x).ne')).sub continuous_const).div_const 2
  simp only [fineRemainderMatrix, Coarse.qf, Matrix.add_mulVec, dotProduct_add]
  change Coarse.qf _ e + Coarse.qf _ e = _
  rw [fineWeightedGram_qf _ _ _
      (fine_integrable_gram h i (fineDifferenceMatrix_memL2 h.toCoeffOn) hc₁),
    fineWeightedGram_qf _ _ _
      (fine_integrable_gram h i (fineGradientMatrix_memL2 h.toCoeffOn true) hc₂)]
  simp only [fineDifferenceMatrix_mulVec, fineGradientMatrix_mulVec]

end GMCExplicitDelta.Assembly
