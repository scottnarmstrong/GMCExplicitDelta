module

public import GMCExplicitDelta.Localization.HaarDefs
public import GMCExplicitDelta.Haar.PoincareCell

/-! Proof of the H8 target `cell_poincare` (sharp cell Poincaré inequality). -/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta.Localization

open Assembly Contract

variable {d : ℕ}

/-- **H8 (cell Poincaré inequality, sharp constant).** On a cube of side `ℓ`, for `h ∈ H¹` and every
depth `j`: `‖h - E_j h‖² ≤ 9^{-j}(ℓ/π)²‖∇h‖²`. -/
theorem cell_poincare_proof (Q : Homogenization.TriadicCube d) (j : ℕ)
    (h : H1Function (openCubeSet Q)) :
    Haar.energy Q (fun x => h.toFun x - cubeProjection Q j h.toFun x) ≤
      cubeScaleFactor Q ^ 2 / (9 ^ j * Real.pi ^ 2) * vecEnergy Q h.grad :=
  Haar.cell_poincare_of_weakGradient Q j h.memL2 h.gradMemL2 h.hasWeakGradient

end GMCExplicitDelta.Localization
