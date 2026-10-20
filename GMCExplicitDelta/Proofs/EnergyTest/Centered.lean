module

public import GMCExplicitDelta.Proofs.EnergyTest.BoundaryTest

/-! Centering the Sobolev factor without changing its gradient. -/

@[expose] public section

open Homogenization

namespace GMCExplicitDelta.Localization.EnergyTest

variable {d : ℕ}

noncomputable def subtractConstantH1 {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U) (c : ℝ) : H1Function U :=
  u - H1Function.ofContDiffOnIsOpenBoundedConvexDomain hU (f := fun _ => c) contDiff_const

theorem subtractConstantH1_toFun {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U) (c : ℝ) :
    (subtractConstantH1 hU u c).toFun = fun x => u.toFun x - c := by
  rw [subtractConstantH1, H1Function.sub_toFun]
  rfl

theorem subtractConstantH1_grad {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U) (c : ℝ) : (subtractConstantH1 hU u c).grad = u.grad := by
  rw [subtractConstantH1, H1Function.sub_grad]
  funext x i
  change u.grad x i - (fderiv ℝ (fun _ : Vec d => c) x) (basisVec i) = u.grad x i
  rw [(hasFDerivAt_const c x).fderiv]
  simp only [zero_apply, sub_zero]

end GMCExplicitDelta.Localization.EnergyTest
