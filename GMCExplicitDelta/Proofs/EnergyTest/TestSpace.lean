module

public import GMCExplicitDelta.Proofs.EnergyTest.Flux
public import Homogenization.Sobolev.Truncation.Basic
public import Homogenization.Sobolev.Foundations.PoincareMeanZero

/-! Zero-trace testing through exact Sobolev representatives. -/

@[expose] public section

open Homogenization MeasureTheory

namespace GMCExplicitDelta.Localization.EnergyTest

variable {d : ℕ}

/-- Zero-trace membership of the value suffices; weak-gradient uniqueness
identifies the gradient of the chosen zero-trace representative. -/
theorem integral_flux_grad_eq_zero_of_memH10 {U : Set (Vec d)} (hU : IsOpen U)
    {F : Vec d → Vec d} (hF : IsSolenoidalOn U F) (u : H1Function U)
    (hu : MemH10 U u.toFun) :
    (∫ x in U, vecDot (F x) (u.grad x)) = 0 := by
  obtain ⟨v, hv⟩ := hu
  have he (i : Fin d) : (fun x => v.toH1Function.grad x i) =ᵐ[volume.restrict U]
      (fun x => u.grad x i) := by
    have hw := v.toH1Function.hasWeakGradient i
    rw [hv] at hw
    exact HasWeakPartialDerivOn.ae_eq hU
      (locallyIntegrableOn_of_locallyIntegrable_restrict
        ((v.toH1Function.gradMemL2 i).locallyIntegrable (by norm_num)))
      (locallyIntegrableOn_of_locallyIntegrable_restrict
        ((u.gradMemL2 i).locallyIntegrable (by norm_num))) hw (u.hasWeakGradient i)
  have hgrad : v.toH1Function.grad =ᵐ[volume.restrict U] u.grad := by
    filter_upwards [Filter.eventually_all.2 he] with x hx
    exact funext hx
  calc
    _ = ∫ x in U, vecDot (F x) (v.toH1Function.grad x) :=
      integral_congr_ae (hgrad.symm.mono fun x hx => by rw [hx])
    _ = 0 := hF v

/-- Every compactly supported C¹ test is valid for a solenoidal field. -/
theorem integral_flux_fderiv_eq_zero {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {F : Vec d → Vec d} (hF : IsSolenoidalOn U F)
    {f : Vec d → ℝ} (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) (hsub : tsupport f ⊆ U) :
    (∫ x in U, vecDot (F x) (fun i => (fderiv ℝ f x) (basisVec i))) = 0 := by
  let u := H1Function.ofContDiffOnIsOpenBoundedConvexDomain hU hf
  have hu : MemH10 U u.toFun := memH10_of_compactSupport hU u hs.isCompact hsub
    (fun x hx => by
      change f x = 0
      by_contra h
      exact hx (subset_closure h))
  exact integral_flux_grad_eq_zero_of_memH10 hU.isOpen hF u hu

end GMCExplicitDelta.Localization.EnergyTest
