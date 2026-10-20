module

public import GMCExplicitDelta.Proofs.FineSensitivity.Energies
public import Mathlib.Order.Filter.Germ.Basic
public import Mathlib.LinearAlgebra.Pi

/-! # Linear representatives of deterministic old maximizer gradients -/

@[expose] public section

open Homogenization Homogenization.Book.Ch02 MeasureTheory

namespace GMCExplicitDelta.Assembly

variable {d : ℕ} {U : Domain d}

/-- Canonical maximizer gradient for a primal or dual loading. -/
noncomputable def fineCanonicalGradient (a : CoeffOn U) (dual : Bool) (e : Vec d) : Vec d → Vec d :=
  (canonicalMaximizer (responseExistenceTheory U a)
    (if dual then 0 else e) (if dual then e else 0)).toSolution.toH1.grad

/-- Taking an a.e. germ is linear and requires no measurability selection. -/
noncomputable def fineGermMk : (Vec d → Vec d) →ₗ[ℝ]
    Filter.Germ (ae (volumeMeasureOn (U : Set (Vec d)))) (Vec d) where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The canonical gradient is linear modulo spatial null sets. -/
noncomputable def fineGradientGerm (a : CoeffOn U) (dual : Bool) : Vec d →ₗ[ℝ]
    Filter.Germ (ae (volumeMeasureOn (U : Set (Vec d)))) (Vec d) where
  toFun e := fineCanonicalGradient a dual e
  map_add' e f := by
    apply Filter.Germ.coe_eq.mpr
    have h00 : (0 : Vec d) + 0 = 0 := add_zero _
    cases dual
    · have h := canonicalMaximizer_add_gradientAE (responseExistenceTheory U a)
        (responseGradientLinearityTheory U a) e 0 f 0
      rw [h00] at h
      simpa [fineCanonicalGradient, Function.comp_def] using h
    · have h := canonicalMaximizer_add_gradientAE (responseExistenceTheory U a)
        (responseGradientLinearityTheory U a) 0 e 0 f
      rw [h00] at h
      simpa [fineCanonicalGradient, Function.comp_def] using h
  map_smul' c e := by
    apply Filter.Germ.coe_eq.mpr
    have h0 : c • (0 : Vec d) = 0 := smul_zero _
    cases dual
    · have h := canonicalMaximizer_smul_gradientAE (responseExistenceTheory U a)
        (responseGradientLinearityTheory U a) c e 0
      rw [h0] at h
      simpa [fineCanonicalGradient, Function.comp_def] using h
    · have h := canonicalMaximizer_smul_gradientAE (responseExistenceTheory U a)
        (responseGradientLinearityTheory U a) c 0 e
      rw [h0] at h
      simpa [fineCanonicalGradient, Function.comp_def] using h

/-- Finite basis interpolation gives gradients linear at every spatial point. -/
noncomputable def fineLinearGradient (a : CoeffOn U) (dual : Bool) : Vec d →ₗ[ℝ] (Vec d → Vec d) :=
  (Pi.basisFun ℝ (Fin d)).constr ℝ (fun i => fineCanonicalGradient a dual (Pi.single i 1))

theorem fineLinearGradient_ae (a : CoeffOn U) (dual : Bool) (e : Vec d) :
    fineLinearGradient a dual e =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      fineCanonicalGradient a dual e := by
  have hm : (fineGermMk (U := U)).comp (fineLinearGradient a dual) = fineGradientGerm a dual := by
    apply (Pi.basisFun ℝ (Fin d)).ext
    intro i
    change fineGermMk (fineLinearGradient a dual ((Pi.basisFun ℝ (Fin d)) i)) = _
    rw [fineLinearGradient, Module.Basis.constr_basis, Pi.basisFun_apply]
    rfl
  exact Filter.Germ.coe_eq.mp (LinearMap.congr_fun hm e)

end GMCExplicitDelta.Assembly
