module

public import GMCExplicitDelta.Proofs.GradPieces.Cell

/-!
Pieces of the localization argument on the good event (steps L2, G1).
Helper declarations live in the namespace `Localization.GradPieces`.

# Restriction and subtraction of frozen solutions
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta.Localization.GradPieces

open Assembly Contract

variable {d : ℕ}

/-! ### Restriction of solutions to subdomains and differences of solutions -/

theorem cellCarrier_eq (R : Homogenization.TriadicCube d) :
    ((cellAt 0 R : Ch02.Domain d) : Set (Homogenization.Vec d)) = openCubeSet R := by
  show translateSet 0 (openCubeSet R) = openCubeSet R
  simp

theorem cell_subset {Q R : Homogenization.TriadicCube d} {k : ℕ}
    (hR : R ∈ descendantsAtDepth Q k) :
    ((cellAt 0 R : Ch02.Domain d) : Set (Homogenization.Vec d)) ⊆
      ((cellAt 0 Q : Ch02.Domain d) : Set (Homogenization.Vec d)) := by
  rw [cellCarrier_eq, cellCarrier_eq]
  exact openCubeSet_subset_of_mem_descendantsAtDepth hR

/-- Restriction of a solution of the cutoff equation to a subdomain. -/
noncomputable def restrictSol (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) {U V : Ch02.Domain d}
    (hVU : (V : Set (Homogenization.Vec d)) ⊆ (U : Set (Homogenization.Vec d)))
    (u : Ch02.Solution U (cutA M L ω U)) : Ch02.Solution V (cutA M L ω V) :=
  u.restrictOfMemVectorL2 U.isOpen V.isOpen hVU (by
    have hf := Ch02.Solution.flux_memVectorL2 u
    have hle : volumeMeasureOn (V : Set (Homogenization.Vec d)) ≤
        volumeMeasureOn (U : Set (Homogenization.Vec d)) := by
      simpa [volumeMeasureOn] using MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hVU
    exact hf.mono_measure hle)

theorem restrictSol_grad (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) {U V : Ch02.Domain d}
    (hVU : (V : Set (Homogenization.Vec d)) ⊆ (U : Set (Homogenization.Vec d)))
    (u : Ch02.Solution U (cutA M L ω U)) :
    (restrictSol M L ω hVU u).toH1.grad = u.toH1.grad := rfl

/-- The difference of two solutions of the cutoff equation on `U`. -/
noncomputable def solDiff (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) (U : Ch02.Domain d)
    (w v : Ch02.Solution U (cutA M L ω U)) : Ch02.Solution U (cutA M L ω U) :=
  AHarmonicFunction.addSMulOfIntegrable w v
    (fun φ => integrableOn_vecDot_of_memVectorL2 (Ch02.Solution.flux_memVectorL2 w)
      φ.toH1Function.grad_memVectorL2)
    (fun φ => integrableOn_vecDot_of_memVectorL2 (Ch02.Solution.flux_memVectorL2 v)
      φ.toH1Function.grad_memVectorL2) (-1)

theorem solDiff_grad (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) (U : Ch02.Domain d)
    (w v : Ch02.Solution U (cutA M L ω U)) (x : Homogenization.Vec d) :
    (solDiff M L ω U w v).toH1.grad x = w.toH1.grad x - v.toH1.grad x := by
  funext i
  show w.toH1.grad x i + (-1 : ℝ) * v.toH1.grad x i = _
  simp [sub_eq_add_neg]

end GMCExplicitDelta.Localization.GradPieces
