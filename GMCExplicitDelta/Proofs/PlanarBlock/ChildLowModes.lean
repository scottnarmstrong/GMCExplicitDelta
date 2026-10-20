module

public import GMCExplicitDelta.Proofs.PlanarBlock.ChildModes
public import GMCExplicitDelta.Proofs.PlanarBlock.ThirdPatterns

/-! Planar child mode averages as products of one-dimensional patterns. -/

@[expose] public section

noncomputable section

open Homogenization

namespace GMCExplicitDelta.Localization

theorem planarBlock_child_sin_zero (Q : TriadicCube 2) (b : Fin 2 → Fin 3) (n m : ℤ) :
    cubeAverage (planarBlock_child Q b) (Haar.cubeSin Q 0 ![n, m]) =
      planarBlock_thirdSin n (b 0) * planarBlock_thirdCos m (b 1) := by
  rw [Haar.cubeSin, planarBlock_child_modeAverage]
  simp [Fin.prod_univ_two, planarBlock_thirdSin, planarBlock_thirdCos]

theorem planarBlock_child_sin_one (Q : TriadicCube 2) (b : Fin 2 → Fin 3) (n m : ℤ) :
    cubeAverage (planarBlock_child Q b) (Haar.cubeSin Q 1 ![n, m]) =
      planarBlock_thirdCos n (b 0) * planarBlock_thirdSin m (b 1) := by
  rw [Haar.cubeSin, planarBlock_child_modeAverage]
  simp [Fin.prod_univ_two, planarBlock_thirdSin, planarBlock_thirdCos]

end GMCExplicitDelta.Localization
