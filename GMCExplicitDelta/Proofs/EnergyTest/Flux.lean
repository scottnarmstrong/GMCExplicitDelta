module

public import GMCExplicitDelta.Localization.Bridge

/-! Solenoidality of the actual normalized frozen flux. -/

@[expose] public section

open Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab

namespace GMCExplicitDelta.Localization.EnergyTest

variable {d : ℕ}

/-- The normalization is a deterministic scalar, so it preserves the weak flux equation. -/
theorem frozenFlux_isSolenoidal (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (U : Ch02.Domain d) (p q : Homogenization.Vec d)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    IsSolenoidalOn (U : Set (Homogenization.Vec d)) (frozenFlux M L U p q ω) := by
  have hs := (frozenSol M L U p q ω).isHarmonic.2
  have he : frozenFlux M L U p q ω = (Real.sqrt (ahom M L) / ahom M L) •
      (fun x => matVecMul ((aCutoffCoeffOnData M L ω U).toCoeffOn.toCoeffField x)
        ((frozenSol M L U p q ω).toH1.grad x)) := by
    funext x i
    simp only [Pi.smul_apply]
    rw [show matVecMul ((aCutoffCoeffOnData M L ω U).toCoeffOn.toCoeffField x)
        ((frozenSol M L U p q ω).toH1.grad x) =
      SubdiffusiveProcess.Model.aCutoff M L ω x • (frozenSol M L U p q ω).toH1.grad x from
        matVecMul_scalarMatrix _ _]
    simp only [frozenFlux, frozenH1, H1Function.smul_grad, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  rw [he]
  exact isSolenoidalOn_smul hs _

end GMCExplicitDelta.Localization.EnergyTest
