module

public import GMCExplicitDelta.Localization.Defs
public import GMCExplicitDelta.Proofs.FreshMean.Means
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ResponseMeasureTheory

/-! # Cell integrability for the frozen coefficient -/

@[expose] public section

open MeasureTheory Homogenization Homogenization.Book SubdiffusiveProcess.CoarseGrainingVocab

namespace GMCExplicitDelta.Localization

open Assembly Contract

variable {d : ℕ}

/-- Each entry of the frozen dual matrix has a second moment on every domain. -/
theorem cellMoment_frozenY_entry_memLp (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (U : Ch02.Domain d) (i j : Fin d) :
    MemLp (fun ω => frozenY M L U ω i j) 2 M.P.toMeasure := by
  have h := (memLp_two_iff_integrable_sq
    ((((integrable_randomAStarMatrix_inv M L U).eval i).eval j).aestronglyMeasurable)).2
    (integrable_randomAStarInv_entry_sq M L U i j)
  exact h.const_mul (ahom M L)

/-- Each entry of the frozen primal matrix has a second moment on every domain. -/
theorem cellMoment_frozenX_entry_memLp (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (U : Ch02.Domain d) (i j : Fin d) :
    MemLp (fun ω => frozenX M L U ω i j) 2 M.P.toMeasure := by
  have h := (memLp_two_iff_integrable_sq
    ((((integrable_randomAMatrix M L U).eval i).eval j).aestronglyMeasurable)).2
    (integrable_randomAMatrix_entry_sq M L U i j)
  exact h.const_mul (ahom M L)⁻¹

/-- An affine function of the frozen dual flux has integrable squared norm. -/
theorem cellMoment_integrable_residual (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (U : Ch02.Domain d) (p q c : Homogenization.Vec d) :
    Integrable (fun ω => vecNormSq (-p + (frozenY M L U ω).mulVec q - c)) M.P.toMeasure := by
  have hcoord (i : Fin d) : MemLp
      (fun ω => (-p + (frozenY M L U ω).mulVec q - c) i) 2 M.P.toMeasure := by
    have hy : MemLp (fun ω => ∑ j, frozenY M L U ω i j * q j) 2 M.P.toMeasure :=
      memLp_finsetSum Finset.univ fun j _ => (cellMoment_frozenY_entry_memLp M L U i j).mul_const (q j)
    exact ((memLp_const (-p i)).add hy).sub (memLp_const (c i))
  simp only [vecNormSq, vecDot, ← sq]
  exact integrable_finsetSum Finset.univ fun i _ =>
    (memLp_two_iff_integrable_sq (hcoord i).aestronglyMeasurable).1 (hcoord i)

/-- Integrability holds on all domains, hence on every cell in the induction range. -/
theorem integrable_cell_proof (M : SubdiffusiveProcess.Model.GMCModel d) {D F : ℝ} (L : ℕ)
    (hP : InductionP M L D F) (R : Homogenization.TriadicCube d) (hR : (L : ℤ) ≤ R.scale)
    (p q c : Homogenization.Vec d) :
    MeasureTheory.Integrable (frozenJ M L (cellAt 0 R) p q) M.P.toMeasure ∧
      MeasureTheory.Integrable
        (fun ω => vecNormSq (-p + (frozenY M L (cellAt 0 R) ω).mulVec q - c)) M.P.toMeasure := by
  have _hP := hP
  have _hR := hR
  exact ⟨integrable_cutoffResponseJ M L (cellAt 0 R)
    ((Real.sqrt (ahom M L))⁻¹ • p) (Real.sqrt (ahom M L) • q),
    cellMoment_integrable_residual M L (cellAt 0 R) p q c⟩

end GMCExplicitDelta.Localization
