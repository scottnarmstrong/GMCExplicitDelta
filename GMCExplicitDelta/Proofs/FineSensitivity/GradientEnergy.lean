module

public import GMCExplicitDelta.Proofs.FineSensitivity.Gram
public import GMCExplicitDelta.Proofs.FineSensitivity.Spatial

/-! # Integrability of the deterministic old-gradient Gram matrices -/

@[expose] public section

open Homogenization Homogenization.Book.Ch02 MeasureTheory Matrix
open SubdiffusiveProcess.CoarseGrainingVocab (ScalarCoeffOnData)

open scoped Matrix.Norms.Elementwise

namespace GMCExplicitDelta.Assembly

noncomputable local instance fineGradientEnergyContinuousENorm {n : ℕ} : ContinuousENorm (Matrix (Fin n) (Fin n) ℝ) :=
  SeminormedAddGroup.toContinuousENorm

variable {d : ℕ} {U : Domain d}

theorem fineMeasGradient_memL2 (a : CoeffOn U) (dual : Bool) (e : Vec d) :
    GradMemL2On (U : Set (Vec d)) (fineMeasGradient a dual e) := by
  intro j
  have h := (canonicalMaximizer (responseExistenceTheory U a)
    (if dual then 0 else e) (if dual then e else 0)).toSolution.toH1.gradMemL2 j
  exact h.ae_eq ((fineMeasGradient_ae a dual e).symm.fun_comp (fun v => v j))

theorem fine_gram_entry (G : Mat d) (i j : Fin d) :
    (Gᵀ * G) i j = vecDot (G *ᵥ Pi.single i 1) (G *ᵥ Pi.single j 1) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec_single_one,
    Matrix.col_apply, vecDot]

/-- Compactness bounds every continuous fresh multiplier; all old gradients remain fixed. -/
theorem fine_integrable_gram {a : Vec d → ℝ} (h : ScalarCoeffOnData U a)
    (i₀ : Fin d) {G : Vec d → Mat d}
    (hG : ∀ i, GradMemL2On (U : Set (Vec d)) (fun x => G x *ᵥ Pi.single i 1))
    {Y : Vec d → ℝ} (hY : Continuous Y) :
    Integrable (fun x => (a x * Y x) • ((G x)ᵀ * G x)) (fineDomainMeasure U) := by
  apply integrable_pi_iff.mpr
  intro i
  apply integrable_pi_iff.mpr
  intro j
  have hi := (U.isDomain.toBoundedMeasurableDomain U.nonempty).integrable_normalizedVolume _
    (Coarse.integrable_a_mul h i₀ (Coarse.integrable_dot_grad (hG i) (hG j)))
  have hmul := fine_integrable_mul_continuous hi hY
  convert hmul using 1
  funext x
  change (a x * Y x) * (((G x)ᵀ * G x) i j) =
    (a x * vecDot (G x *ᵥ Pi.single i 1) (G x *ᵥ Pi.single j 1)) * Y x
  rw [fine_gram_entry]
  ring

/-- The measured primal and dual matrix columns have the required spatial L² control. -/
theorem fineGradientMatrix_memL2 (a : CoeffOn U) (dual : Bool) (i : Fin d) :
    GradMemL2On (U : Set (Vec d)) (fun x => fineGradientMatrix a dual x *ᵥ Pi.single i 1) := by
  simpa only [fineGradientMatrix_mulVec] using fineMeasGradient_memL2 a dual (Pi.single i 1)

end GMCExplicitDelta.Assembly
