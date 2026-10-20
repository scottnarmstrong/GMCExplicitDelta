module

public import GMCExplicitDelta.Proofs.Multiplier.Multiplier
public import GMCExplicitDelta.Proofs.HaarBlocks.CellPoincare

/-! H9 with the exact target hypotheses. -/
@[expose] public section

open Homogenization
open scoped ENNReal

namespace GMCExplicitDelta.Localization

open Assembly Contract
variable {d : ℕ}

theorem haar_multiplier_proof (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (n : ℕ) (w : H1Function (openCubeSet (originCube d (n : ℤ)))) {Λ m : ℝ} (hΛ : 0 ≤ Λ)
    (hm : 0 ≤ m)
    (hw : Haar.energy (originCube d (n : ℤ))
        (fun x => w.toFun x - cubeAverage (originCube d (n : ℤ)) w.toFun) ≤
      Λ / row.kappaOmega ^ 2 * ((3 : ℝ) ^ n) ^ 2 * m ^ 2)
    (hgw : vecEnergy (originCube d (n : ℤ)) w.grad ≤ m ^ 2) :
    haarPrimal (originCube d (n : ℤ)) row.qs (fun x =>
        (w.toFun x - cubeAverage (originCube d (n : ℤ)) w.toFun) • cubeCutoffGrad row n x) ≤
      ENNReal.ofReal (multSq row Λ * m ^ 2) := by
  have _hd := hd
  have _hm := hm
  exact Multiplier.haar_multiplier_of_cell_poincare cell_poincare_proof row hO n w hΛ hw hgw

end GMCExplicitDelta.Localization
