module

public import GMCExplicitDelta.Proofs.FineSensitivity.Gradient

/-! # Measurable spatial representatives after fixing the old coefficient -/

@[expose] public section

open Homogenization Homogenization.Book.Ch02 MeasureTheory

namespace GMCExplicitDelta.Assembly

variable {d : ℕ} {U : Domain d}

theorem fineGradientCoordMeas (a : CoeffOn U) (dual : Bool) (e : Vec d) (i : Fin d) :
    AEStronglyMeasurable (fun x => fineCanonicalGradient a dual e x i)
      (volumeMeasureOn (U : Set (Vec d))) :=
  ((canonicalMaximizer (responseExistenceTheory U a)
    (if dual then 0 else e) (if dual then e else 0)).toSolution.toH1.gradMemL2 i).aestronglyMeasurable

/-- Each deterministic basis gradient has a Borel representative. -/
noncomputable def fineBasisGradient (a : CoeffOn U) (dual : Bool) (i : Fin d) : Vec d → Vec d :=
  fun x j => (fineGradientCoordMeas a dual (Pi.single i 1) j).mk
    (fun y => fineCanonicalGradient a dual (Pi.single i 1) y j) x

theorem measurable_fineBasisGradient (a : CoeffOn U) (dual : Bool) (i : Fin d) :
    Measurable (fineBasisGradient a dual i) := by
  apply Measurable.of_eval
  intro j
  exact (fineGradientCoordMeas a dual (Pi.single i 1) j).measurable_mk

theorem fineBasisGradient_ae (a : CoeffOn U) (dual : Bool) (i : Fin d) :
    fineBasisGradient a dual i =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      fineCanonicalGradient a dual (Pi.single i 1) := by
  have h : ∀ j, ∀ᵐ x ∂volumeMeasureOn (U : Set (Vec d)),
      fineBasisGradient a dual i x j = fineCanonicalGradient a dual (Pi.single i 1) x j :=
    fun j => (fineGradientCoordMeas a dual (Pi.single i 1) j).ae_eq_mk.symm
  filter_upwards [ae_all_iff.mpr h] with x hx
  exact funext hx

/-- Linear interpolation of the chosen Borel basis gradients. -/
noncomputable def fineMeasGradient (a : CoeffOn U) (dual : Bool) : Vec d →ₗ[ℝ] (Vec d → Vec d) :=
  (Pi.basisFun ℝ (Fin d)).constr ℝ (fineBasisGradient a dual)

theorem measurable_fineMeasGradient (a : CoeffOn U) (dual : Bool) (e : Vec d) :
    Measurable (fineMeasGradient a dual e) := by
  unfold fineMeasGradient
  rw [Module.Basis.constr_apply_fintype]
  have he : (∑ i : Fin d, (Pi.basisFun ℝ (Fin d)).equivFun e i • fineBasisGradient a dual i) =
      (fun x => ∑ i : Fin d, (Pi.basisFun ℝ (Fin d)).equivFun e i • fineBasisGradient a dual i x) := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply]
  rw [he]
  exact Finset.measurable_sum Finset.univ (fun i _ =>
    (measurable_fineBasisGradient a dual i).const_smul ((Pi.basisFun ℝ (Fin d)).equivFun e i))

theorem fineMeasGradient_ae (a : CoeffOn U) (dual : Bool) (e : Vec d) :
    fineMeasGradient a dual e =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      fineCanonicalGradient a dual e := by
  have hm : (fineGermMk (U := U)).comp (fineMeasGradient a dual) = fineGradientGerm a dual := by
    apply (Pi.basisFun ℝ (Fin d)).ext
    intro i
    change (fineGermMk (fineMeasGradient a dual ((Pi.basisFun ℝ (Fin d)) i))) = _
    rw [fineMeasGradient, Module.Basis.constr_basis, Pi.basisFun_apply]
    exact (fineBasisGradient_ae a dual i).germ_eq
  exact Filter.Germ.coe_eq.mp (LinearMap.congr_fun hm e)

end GMCExplicitDelta.Assembly
