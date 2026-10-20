module

public import GMCExplicitDelta.Proofs.NativeCaps.Representation
public import GMCExplicitDelta.Proofs.NativeCaps.LocalMu

/-! # Frozen matrix subadditivity on arbitrary translated partitions -/

@[expose] public section

open Homogenization Homogenization.Book MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab
open GMCExplicitDelta.Insertion
open scoped BigOperators ENNReal

namespace GMCExplicitDelta.Assembly

variable {d : ℕ}

/-- Subadditivity for the canonically certified cutoff coefficient family. -/
theorem nativeResponse_subadd (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (p q : Homogenization.Vec d) (Q : Homogenization.TriadicCube d) (j : ℕ)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    nativeResponse M L p q Q ω ≤
      ((descendantsAtDepth Q j).card : ℝ)⁻¹ * ∑ R ∈ descendantsAtDepth Q j, nativeResponse M L p q R ω := by
  let F := aCutoffFamily M L ω
  let P : Ch02.DomainPartition (Ch02.cubeDomain Q) := Ch02.descendantsDomainPartition Q j
  have hcell : ∀ i : P.Cell, Ch02.CoeffOn.RestrictsTo (F.coeffOn Q) (F.coeffOn i.1) :=
    fun i => F.restrictsTo_of_subset (P.cell_subset_parent i)
  have hsub := (Ch02.responseSubadditivityAndScalingTheory (Ch02.cubeDomain Q)
    (F.coeffOn Q)).responseJ_subadditive P (fun i => F.coeffOn i.1) hcell p q
  have havg := Ch02.descendantsDomainPartition_weightedAverage Q j
    (fun R => nativeResponse M L p q R ω)
  exact hsub.trans_eq (by simpa [P, nativeResponse, F, descendantsAverage, J, aCutoffFamily, aCutoffTriadicData,
    ScalarTriadicCoeffData.toTriadicCoeffFamily, Ch02.descendantsDomainPartition] using! havg)

/-- Covariance under every deterministic spatial translation, at fixed normalization. -/
theorem frozenJ_cellAt_translate (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (z : Homogenization.Vec d) (R : Homogenization.TriadicCube d) (p q : Homogenization.Vec d)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    frozenJ M L (cellAt z R) p q ω =
      frozenJ M L (Ch02.cubeDomain R) p q (translatePotentialSequence z ω) := by
  unfold frozenJ J
  rw [Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ,
    Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ]
  change ResponseJ (translateSet z (openCubeSet R)) _ _ _ = ResponseJ (openCubeSet R) _ _ _
  rw [ResponseJ_translateSet_eq_translateCoeffField]
  apply congrArg (ResponseJ (openCubeSet R)
    ((Real.sqrt (ahom M L))⁻¹ • p) (Real.sqrt (ahom M L) • q))
  funext x
  change scalarMatrix (SubdiffusiveProcess.Model.aCutoff M L ω (x + z)) =
    scalarMatrix (SubdiffusiveProcess.Model.aCutoff M L (translatePotentialSequence z ω) x)
  exact congrArg scalarMatrix (aCutoff_translatePotentialSequence M L z ω x).symm

/-- The precise quadratic-form Loewner inequality on translated depth-j cells. -/
theorem frozenDefect_subadd_translated (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (z : Homogenization.Vec d) (Q : Homogenization.TriadicCube d)
    (j : ℕ) (ω : SubdiffusiveProcess.Model.PotentialSample d) (u : EuclideanSpace ℝ (Fin d)) :
    sphereQuadratic (frozenDefect M L (cellAt z Q) ω) u ≤
      ((descendantsAtDepth Q j).card : ℝ)⁻¹ * ∑ R ∈ descendantsAtDepth Q j,
        sphereQuadratic (frozenDefect M L (cellAt z R) ω) u := by
  simp only [sphereQuadratic_frozenDefect M L, frozenJ_cellAt_translate]
  exact nativeResponse_subadd M L ((Real.sqrt (ahom M L))⁻¹ • u.ofLp)
    (Real.sqrt (ahom M L) • u.ofLp) Q j (translatePotentialSequence z ω)

/-- Translation covariance of the actual ENNReal normalized maximum. -/
theorem normalizedDefect_cellAt_translate (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (z : Homogenization.Vec d) (R : Homogenization.TriadicCube d)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    normalizedDefect M L (cellAt z R) ω =
      normalizedDefect M L (Ch02.cubeDomain R) (translatePotentialSequence z ω) := by
  unfold normalizedDefect paperScalarProbeMaxOn
  apply iSup_congr
  intro e
  exact congrArg ENNReal.ofReal (frozenJ_cellAt_translate M L z R e.val e.val ω)

end GMCExplicitDelta.Assembly
