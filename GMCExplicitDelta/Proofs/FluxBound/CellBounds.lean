module

public import GMCExplicitDelta.Proofs.FluxBound.Flux

/-! # G1(c): The C5 flux estimate on a descendant of the frozen domain. -/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta.Localization.FluxBound

open Assembly Contract

variable {d : ℕ}

/-- The restriction of the frozen solution of `Q_n` to a depth-`k` cell. -/
noncomputable def cellRestr (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) (n k : ℕ) (p q : Homogenization.Vec d)
    {R : Homogenization.TriadicCube d}
    (hR : R ∈ descendantsAtDepth (originCube d (n : ℤ)) k) :
    Ch02.Solution (cellAt 0 R) (cutA M L ω (cellAt 0 R)) :=
  restrictSol M L ω (cell_subset hR) (frozenSol M L (cubeAt 0 n) p q ω)

theorem varE_cell_eq (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) (R : Homogenization.TriadicCube d)
    (w : Ch02.Solution (cellAt 0 R) (cutA M L ω (cellAt 0 R))) :
    Ch02.variationEnergyValue (cellAt 0 R) (cutA M L ω (cellAt 0 R)) w =
      cubeAverage R (fun x => SubdiffusiveProcess.Model.aCutoff M L ω x *
        vecNormSq (w.toH1.grad x)) := by
  rw [Coarse.variationEnergyValue_eq_average (cutA_symm M L ω (cellAt 0 R)),
    ← average_cellAt_eq_cubeAverage]
  congr 1
  funext x
  exact Coarse.vecDot_scalar_coeff (aCutoffCoeffOnData M L ω (cellAt 0 R)) x _

theorem avgFlux_cell_eq (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) (R : Homogenization.TriadicCube d)
    (w : Ch02.Solution (cellAt 0 R) (cutA M L ω (cellAt 0 R))) :
    Ch02.averageFlux (cellAt 0 R) (cutA M L ω (cellAt 0 R)) w =
      cubeAverageVec R (fun x => SubdiffusiveProcess.Model.aCutoff M L ω x • w.toH1.grad x) := by
  funext i
  show Ch02.average (cellAt 0 R) (fun x => matVecMul
    ((cutA M L ω (cellAt 0 R)).toCoeffField x) (w.toH1.grad x) i) = _
  rw [average_cellAt_eq_cubeAverage]
  unfold cubeAverageVec
  congr 1
  funext x
  rw [Coarse.matVecMul_scalar_coeff (aCutoffCoeffOnData M L ω (cellAt 0 R)) x]

theorem cell_flux_bound (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) (n k : ℕ) (p q : Homogenization.Vec d)
    {R : Homogenization.TriadicCube d} (hR : R ∈ descendantsAtDepth (originCube d (n : ℤ)) k)
    {θ : ℝ} (hθ : 0 ≤ θ)
    (hdef : ∀ e : Homogenization.Vec d, e ⬝ᵥ e = 1 → frozenJ M L (cellAt 0 R) e e ω ≤ θ) :
    (ahom M L)⁻¹ * vecNormSq (cubeAverageVec R (fun x =>
        SubdiffusiveProcess.Model.aCutoff M L ω x •
          (frozenSol M L (cubeAt 0 n) p q ω).toH1.grad x)) ≤
      Coarse.xfun θ * cubeAverage R (fun x => SubdiffusiveProcess.Model.aCutoff M L ω x *
        vecNormSq ((frozenSol M L (cubeAt 0 n) p q ω).toH1.grad x)) := by
  have h := c5_flux M L ω (cellAt 0 R) hθ hdef (cellRestr M L ω n k p q hR)
  rw [avgFlux_cell_eq, varE_cell_eq] at h
  exact h

end GMCExplicitDelta.Localization.FluxBound
