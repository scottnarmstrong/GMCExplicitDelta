module

public import GMCExplicitDelta.Proofs.NativeCaps.LocalMu
public import SubdiffusiveProcess.CoarseGrainingVocab.ACutoffRange
public import GMCExplicitDelta.Proofs.NativeCaps.ColorGeometry

/-! # Mutual independence at the literal cutoff range -/

@[expose] public section

open Homogenization Homogenization.Book MeasureTheory ProbabilityTheory
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped BigOperators

namespace GMCExplicitDelta.Assembly

/-- Finite intersections of local events are local on the union. -/
theorem native_local_biInter {d : ℕ} {ι : Type*}
    (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    {U : ι → Set (Homogenization.Vec d)} {f : ι → Set (SubdiffusiveProcess.Model.PotentialSample d)}
    {s : Finset ι}
    (hf : ∀ i ∈ s, @MeasurableSet _ ((LocalSigmaR (U i)).comap (aCutoffRegCoeffField M L)) (f i)) :
    @MeasurableSet _ ((LocalSigmaR (⋃ i ∈ s, U i)).comap (aCutoffRegCoeffField M L)) (⋂ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hsubi : U i ⊆ ⋃ j ∈ insert i s, U j := by intro x hx; simp [hx]
    have hsubs : (⋃ j ∈ s, U j) ⊆ ⋃ j ∈ insert i s, U j := by intro x hx; simp [hx]
    have hi' := (MeasurableSpace.comap_mono (localSigmaR_mono hsubi))
      (f i) (hf i (by simp))
    have hs' := (MeasurableSpace.comap_mono (localSigmaR_mono hsubs))
      (⋂ j ∈ s, f j) (ih fun j hj => hf j (by simp [hj]))
    simpa only [Finset.set_biInter_insert, hi] using hi'.inter hs'

/-- G1 plus independence of the potential layers gives mutual independence of any family of
integral-local observables on open sets separated at the maximal layer range. -/
theorem native_iIndep_local {d : ℕ} [NeZero d] {ι : Type*}
    (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    {U : ι → Set (Homogenization.Vec d)} (hU : ∀ i, IsOpen (U i))
    (hsep : Pairwise fun i j => ∀ ⦃x y : Homogenization.Vec d⦄, x ∈ U i → y ∈ U j →
      Real.sqrt (d : ℝ) * (3 : ℝ) ^ L ≤ Ch02.vecNorm (x - y)) :
    iIndep (fun i => (LocalSigmaR (U i)).comap (aCutoffRegCoeffField M L)) M.P.toMeasure := by
  classical
  rw [iIndep_iff]
  intro s f hf
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hsepunion : ∀ ⦃x y : Homogenization.Vec d⦄, x ∈ U i → y ∈ ⋃ j ∈ s, U j →
        Real.sqrt (d : ℝ) * (3 : ℝ) ^ L ≤ Ch02.vecNorm (x - y) := by
      intro x y hx hy
      obtain ⟨j, hj, hy⟩ := Set.mem_iUnion₂.mp hy
      have hne : i ≠ j := by
        intro hij
        subst j
        exact hi hj
      exact hsep hne hx hy
    have hsm := native_local_biInter M L (U := U) (f := f) (s := s)
      (fun j hj => hf j (by simp [hj]))
    have hinter := (Indep_iff _ _ M.P.toMeasure).mp
      (indep_aCutoffRegCoeffField_local_of_separation M L (U i) (⋃ j ∈ s, U j)
        (hU i) (isOpen_biUnion fun j _ => hU j) hsepunion)
        (f i) (⋂ j ∈ s, f j) (hf i (by simp)) hsm
    calc
      M.P.toMeasure (⋂ j ∈ insert i s, f j) =
          M.P.toMeasure (f i ∩ ⋂ j ∈ s, f j) := by simp
      _ = M.P.toMeasure (f i) * M.P.toMeasure (⋂ j ∈ s, f j) := hinter
      _ = M.P.toMeasure (f i) * ∏ j ∈ s, M.P.toMeasure (f j) := by
        rw [ih (fun j hj => hf j (by simp [hj]))]
      _ = ∏ j ∈ insert i s, M.P.toMeasure (f j) := by simp [Finset.prod_insert, hi]

theorem native_iIndepFun_local {d : ℕ} [NeZero d] {ι : Type*} {β : ι → Type*}
    [∀ i, MeasurableSpace (β i)] (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    {U : ι → Set (Homogenization.Vec d)} {X : ∀ i, SubdiffusiveProcess.Model.PotentialSample d → β i}
    (hU : ∀ i, IsOpen (U i))
    (hsep : Pairwise fun i j => ∀ ⦃x y : Homogenization.Vec d⦄, x ∈ U i → y ∈ U j →
      Real.sqrt (d : ℝ) * (3 : ℝ) ^ L ≤ Ch02.vecNorm (x - y))
    (hX : ∀ i, @Measurable _ (β i) ((LocalSigmaR (U i)).comap (aCutoffRegCoeffField M L)) _ (X i)) :
    iIndepFun X M.P.toMeasure := by
  rw [iIndepFun_iff_iIndep, iIndep_iff]
  intro s f hf
  exact (iIndep_iff (fun i => (LocalSigmaR (U i)).comap (aCutoffRegCoeffField M L))
    M.P.toMeasure).mp (native_iIndep_local M L hU hsep) s
    (fun i hi => (Measurable.comap_le (hX i)) (f i) (hf i hi))

end GMCExplicitDelta.Assembly
