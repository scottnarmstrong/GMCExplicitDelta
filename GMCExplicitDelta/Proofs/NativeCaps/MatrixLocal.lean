module

public import GMCExplicitDelta.Proofs.NativeCaps.Representation
public import GMCExplicitDelta.Proofs.NativeCaps.LocalMu
public import GMCExplicitDelta.Proofs.NativeCaps.Independence

/-! # Matrix measurability and exact local representatives -/

@[expose] public section

open Homogenization Homogenization.Book MeasureTheory ProbabilityTheory Matrix Filter
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped BigOperators ENNReal

namespace GMCExplicitDelta.Assembly

variable {d : ℕ}

/-- Polarization recovers each entry of a real symmetric matrix from three quadratic probes. -/
theorem matrix_entry_polarization {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian)
    (i j : Fin d) :
    A i j = (Coarse.qf A (Pi.single i 1 + Pi.single j 1) -
      Coarse.qf A (Pi.single i 1) - Coarse.qf A (Pi.single j 1)) / 2 := by
  have hs : A j i = A i j := congrFun (congrFun (Matrix.isHermitian_iff_isSymm.mp hA) i) j
  simp only [Coarse.qf, Matrix.mulVec_add, dotProduct_add, add_dotProduct,
    Matrix.mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply]
  rw [hs]
  ring

theorem frozenDefect_entry (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (U : Ch02.Domain d) (ω : SubdiffusiveProcess.Model.PotentialSample d) (i j : Fin d) :
    frozenDefect M L U ω i j =
      (frozenJ M L U (Pi.single i 1 + Pi.single j 1) (Pi.single i 1 + Pi.single j 1) ω -
        frozenJ M L U (Pi.single i 1) (Pi.single i 1) ω -
        frozenJ M L U (Pi.single j 1) (Pi.single j 1) ω) / 2 := by
  rw [matrix_entry_polarization (frozenDefect_isHermitian M L U ω) i j]
  simp only [frozenDefect_qf]

theorem measurable_frozenDefect [NeZero d] (M : SubdiffusiveProcess.Model.GMCModel d)
    (L : ℕ) (U : Ch02.Domain d) : Measurable (frozenDefect M L U) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  have hp (e : Homogenization.Vec d) : Measurable (fun ω => frozenJ M L U e e ω) :=
    measurable_cutoff_responseJ M L U _ _
  simp_rw [frozenDefect_entry]
  exact (((hp _).sub (hp _)).sub (hp _)).div_const 2

/-- The actual frozen matrix has a representative measurable using only the open cell. -/
theorem frozenDefect_local_rep [NeZero d] (M : SubdiffusiveProcess.Model.GMCModel d)
    (L : ℕ) (R : Homogenization.TriadicCube d) :
    ∃ Y : SubdiffusiveProcess.Model.PotentialSample d → Matrix (Fin d) (Fin d) ℝ,
      @Measurable _ _ ((LocalSigmaR (openCubeSet R)).comap (aCutoffRegCoeffField M L)) _ Y ∧
      frozenDefect M L (Ch02.cubeDomain R) =ᵐ[M.P.toMeasure] Y := by
  classical
  have hex (e : Homogenization.Vec d) := cutoffResponse_local_rep M L
    ((Real.sqrt (ahom M L))⁻¹ • e) (Real.sqrt (ahom M L) • e) R
  choose Z hZ heq using hex
  let Y : SubdiffusiveProcess.Model.PotentialSample d → Matrix (Fin d) (Fin d) ℝ :=
    fun ω i j => (Z (Pi.single i 1 + Pi.single j 1) ω -
      Z (Pi.single i 1) ω - Z (Pi.single j 1) ω) / 2
  refine ⟨Y, ?_, ?_⟩
  · let : MeasurableSpace (SubdiffusiveProcess.Model.PotentialSample d) :=
      (LocalSigmaR (openCubeSet R)).comap (aCutoffRegCoeffField M L)
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    exact (((hZ _).sub (hZ _)).sub (hZ _)).div_const 2
  · have hpair : ∀ᵐ ω ∂M.P.toMeasure, ∀ i j : Fin d,
        frozenJ M L (Ch02.cubeDomain R) (Pi.single i 1 + Pi.single j 1)
          (Pi.single i 1 + Pi.single j 1) ω = Z (Pi.single i 1 + Pi.single j 1) ω :=
      ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => heq _
    have hsingle : ∀ᵐ ω ∂M.P.toMeasure, ∀ i : Fin d,
        frozenJ M L (Ch02.cubeDomain R) (Pi.single i 1) (Pi.single i 1) ω = Z (Pi.single i 1) ω :=
      ae_all_iff.mpr fun i => heq _
    filter_upwards [hpair, hsingle] with ω hp hs
    ext i j
    rw [frozenDefect_entry, hp i j, hs i, hs j]

/-- Matrix-valued mutual independence for arbitrary sharply separated cells. -/
theorem iIndepFun_frozenDefect_cells [NeZero d] {ι : Type*}
    (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (R : ι → Homogenization.TriadicCube d)
    (hsep : Pairwise fun i j => ∀ ⦃x y : Homogenization.Vec d⦄,
      x ∈ openCubeSet (R i) → y ∈ openCubeSet (R j) →
      Real.sqrt (d : ℝ) * (3 : ℝ) ^ L ≤ Ch02.vecNorm (x - y)) :
    iIndepFun (fun i => frozenDefect M L (Ch02.cubeDomain (R i))) M.P.toMeasure := by
  classical
  choose Y hY heq using fun i => frozenDefect_local_rep M L (R i)
  have hi : iIndepFun Y M.P.toMeasure := native_iIndepFun_local M L
    (fun i => isOpen_openCubeSet (R i)) hsep hY
  exact hi.congr fun i => (heq i).symm

end GMCExplicitDelta.Assembly
