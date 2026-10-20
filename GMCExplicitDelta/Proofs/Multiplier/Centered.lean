module

public import GMCExplicitDelta.Proofs.Multiplier.H7
public import GMCExplicitDelta.Proofs.LocWeights.Weights

/-! The centered Sobolev multiplier step required by H9. -/
@[expose] public section

open Homogenization
open scoped BigOperators

namespace GMCExplicitDelta.Localization.Multiplier

variable {d : ℕ}

/-- Centering preserves the weak gradient. -/
noncomputable def centeredH1 (Q : TriadicCube d) (w : H1Function (openCubeSet Q)) :
    H1Function (openCubeSet Q) :=
  w - H1Function.ofContDiffOnIsOpenBoundedConvexDomain
    (isOpenBoundedConvexDomain_openCubeSet Q) (f := fun _ => cubeAverage Q w.toFun) contDiff_const

theorem centeredH1_toFun (Q : TriadicCube d) (w : H1Function (openCubeSet Q)) :
    (centeredH1 Q w).toFun = fun x => w.toFun x - cubeAverage Q w.toFun := by
  rw [centeredH1, H1Function.sub_toFun]
  rfl

theorem centeredH1_grad (Q : TriadicCube d) (w : H1Function (openCubeSet Q)) :
    (centeredH1 Q w).grad = w.grad := by
  rw [centeredH1, H1Function.sub_grad]
  funext x i
  change w.grad x i - (fderiv ℝ (fun _ : Vec d => cubeAverage Q w.toFun) x) (basisVec i) = w.grad x i
  rw [(hasFDerivAt_const (cubeAverage Q w.toFun) x).fderiv]
  simp only [zero_apply, sub_zero]

/-- H7's Sobolev multiplier estimate with the exact centering used by H9. -/
theorem cutoff_sobolev_multiplier (row : Contract.Row d) (hO : row.Obligations)
    (n : ℕ) (w : H1Function (openCubeSet (originCube d (n : ℤ)))) :
    ∃ H : Fin d → H1Function (openCubeSet (originCube d (n : ℤ))),
      (∀ i, (H i).toFun = fun x =>
        (w.toFun x - cubeAverage (originCube d (n : ℤ)) w.toFun) * cubeCutoffGrad row n x i) ∧
      (∑ i, vecEnergy (originCube d (n : ℤ)) (H i).grad) ≤
        row.kappaOmega ^ 2 / ((3 : ℝ) ^ n) ^ 2 * vecEnergy (originCube d (n : ℤ)) w.grad +
          (d : ℝ) * row.kappaOmega ^ 4 / ((3 : ℝ) ^ n) ^ 4 * Haar.energy (originCube d (n : ℤ))
            (fun x => w.toFun x - cubeAverage (originCube d (n : ℤ)) w.toFun) := by
  obtain ⟨hω0, hω1⟩ := LocWeights.omega_bounds row hO
  simpa only [centeredH1_toFun, centeredH1_grad] using
    exists_cutoffGradientH1 row hω0 hω1 n (centeredH1 (originCube d (n : ℤ)) w)

end GMCExplicitDelta.Localization.Multiplier
