module

public import GMCExplicitDelta.Localization.Defs
public import Homogenization.CoarseGraining.Subadditivity

/-!
# C2 for the frozen coefficient: subadditivity over triadic descendants

`frozenJ_le_descAvg`: for every triadic cube `R` and depth `k`,
`J(R, p, q; b_L) ≤ avg_{R' depth k of R} J(R', p, q; b_L)` (pointwise in `ω`), from CoarseGraining's
`responseJ_subadditive_openCubeSet_descendantsAtDepth_of_isEllipticFieldOn` and the bridge
`Internal.Ch02.book_responseJ_eq_ResponseJ` between the public and the internal response functional.
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta.Localization

open Assembly Contract

variable {d : ℕ}

/-- The cutoff coefficient is uniformly elliptic on every open triadic cube. -/
theorem isEllipticFieldOn_aCutoff (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) (R : Homogenization.TriadicCube d) :
    ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (openCubeSet R)
      (scalarCoeffField (SubdiffusiveProcess.Model.aCutoff M L ω)) := by
  classical
  set a := SubdiffusiveProcess.Model.aCutoff M L ω with ha
  have ha_cont : Continuous a := SubdiffusiveProcess.Model.continuous_aCutoff M L ω
  have hcomp : IsCompact (closure (openCubeSet R)) := (isBounded_openCubeSet R).isCompact_closure
  have hne : (closure (openCubeSet R)).Nonempty := (Ch02.openCubeSet_nonempty R).closure
  obtain ⟨x_min, hx_min, h_min⟩ := hcomp.exists_isMinOn hne ha_cont.continuousOn
  obtain ⟨x_max, hx_max, h_max⟩ := hcomp.exists_isMaxOn hne ha_cont.continuousOn
  refine ⟨a x_min, a x_max, ?_, ?_⟩
  · have hcont : Continuous fun x => scalarCoeffField a x :=
      ha_cont.smul continuous_const
    have h : (fun x i j => if x ∈ openCubeSet R then scalarCoeffField a x i j else 0) =
        fun x => (openCubeSet R).indicator (fun x => scalarCoeffField a x) x := by
      funext x i j
      by_cases hx : x ∈ openCubeSet R <;> simp [hx, Set.indicator]
    rw [h]
    exact hcont.measurable.indicator (measurableSet_openCubeSet R)
  · intro x hx
    have hax : 0 < a x := SubdiffusiveProcess.Model.aCutoff_pos M L ω x
    exact (Homogenization.isEllipticMatrix_scalarMatrix hax).mono
      (SubdiffusiveProcess.Model.aCutoff_pos M L ω x_min) (h_min (subset_closure hx))
      (h_max (subset_closure hx))

theorem frozenJ_eq_ResponseJ (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (R : Homogenization.TriadicCube d) (p q : Homogenization.Vec d)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    frozenJ M L (cellAt 0 R) p q ω =
      ResponseJ (openCubeSet R) ((Real.sqrt (ahom M L))⁻¹ • p) (Real.sqrt (ahom M L) • q)
        (scalarCoeffField (SubdiffusiveProcess.Model.aCutoff M L ω)) := by
  unfold frozenJ
  rw [show J (cellAt 0 R) (aCutoffCoeffOnData M L ω (cellAt 0 R)).toCoeffOn
      ((Real.sqrt (ahom M L))⁻¹ • p) (Real.sqrt (ahom M L) • q) =
      Ch02.responseJ (cellAt 0 R) (aCutoffCoeffOnData M L ω (cellAt 0 R)).toCoeffOn
      ((Real.sqrt (ahom M L))⁻¹ • p) (Real.sqrt (ahom M L) • q) from rfl,
    Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ]
  have hc : ((cellAt 0 R : Ch02.Domain d) : Set (Homogenization.Vec d)) = openCubeSet R := by
    show translateSet 0 (openCubeSet R) = openCubeSet R
    simp
  rw [hc]
  rfl

/-- **C2 (subadditivity over triadic descendants)** for the frozen coefficient. -/
theorem frozenJ_le_descAvg (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (R : Homogenization.TriadicCube d) (k : ℕ) (p q : Homogenization.Vec d)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    frozenJ M L (cellAt 0 R) p q ω ≤
      descendantsAverage R k (fun R' => frozenJ M L (cellAt 0 R') p q ω) := by
  obtain ⟨lam, Lam, hEll⟩ := isEllipticFieldOn_aCutoff M L ω R
  rw [frozenJ_eq_ResponseJ, show (fun R' => frozenJ M L (cellAt 0 R') p q ω) =
    fun R' => ResponseJ (openCubeSet R') ((Real.sqrt (ahom M L))⁻¹ • p) (Real.sqrt (ahom M L) • q)
      (scalarCoeffField (SubdiffusiveProcess.Model.aCutoff M L ω)) from
    funext fun R' => frozenJ_eq_ResponseJ M L R' p q ω]
  exact responseJ_subadditive_openCubeSet_descendantsAtDepth_of_isEllipticFieldOn k R _ hEll _ _

end GMCExplicitDelta.Localization
