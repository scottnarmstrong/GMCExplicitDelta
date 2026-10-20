module

public import GMCExplicitDelta.Assembly.ModelEvents
public import SubdiffusiveProcess.CoarseGrainingVocab.PrefixSuffixMeasurability

/-! Measurability of the literal cutoff response and arbitrary-normalization supremum. -/
@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open scoped ENNReal

namespace GMCExplicitDelta.Assembly

variable {d : ℕ}

theorem cutoff_probe_continuous (M : SubdiffusiveProcess.Model.GMCModel d) (m : ℕ)
    (U : Ch02.Domain d) (s : ℝ) (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    Continuous (fun e : ScalarProbeUnitSphere d =>
      J U (aCutoffCoeffOnData M m ω U).toCoeffOn ((Real.sqrt s)⁻¹ • (e : Homogenization.Vec d))
        (Real.sqrt s • (e : Homogenization.Vec d))) := by
  let a := (aCutoffCoeffOnData M m ω U).toCoeffOn
  have hTheory := Ch02.responseSymmetricDirichletNeumannTheory U a
    (aCutoffCoeffOnData M m ω U).isSymmetric
  have heq (e : ScalarProbeUnitSphere d) := hTheory.response_dirichlet_neumann_split
    ((Real.sqrt s)⁻¹ • (e : Homogenization.Vec d)) (Real.sqrt s • (e : Homogenization.Vec d))
  simp_rw [hTheory.dirichlet_value_by_sigma, hTheory.neumann_value_by_sigmaStarInv] at heq
  change Continuous (fun e : ScalarProbeUnitSphere d =>
    J U a ((Real.sqrt s)⁻¹ • (e : Homogenization.Vec d)) (Real.sqrt s • (e : Homogenization.Vec d)))
  simp_rw [heq]
  unfold vecDot matVecMul
  fun_prop

theorem scaledDefect_eq_countable (M : SubdiffusiveProcess.Model.GMCModel d) [NeZero d]
    (m : ℕ) (U : Ch02.Domain d) (s : ℝ) (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    scaledDefect M m U s ω = ⨆ i : ℕ, ENNReal.ofReal
      (J U (aCutoffCoeffOnData M m ω U).toCoeffOn
        ((Real.sqrt s)⁻¹ • (TopologicalSpace.denseSeq (ScalarProbeUnitSphere d) i : Homogenization.Vec d))
        (Real.sqrt s • (TopologicalSpace.denseSeq (ScalarProbeUnitSphere d) i : Homogenization.Vec d))) := by
  let f : ScalarProbeUnitSphere d → ℝ≥0∞ := fun e => ENNReal.ofReal
    (J U (aCutoffCoeffOnData M m ω U).toCoeffOn ((Real.sqrt s)⁻¹ • (e : Homogenization.Vec d))
      (Real.sqrt s • (e : Homogenization.Vec d)))
  let c := ⨆ i : ℕ, f (TopologicalSpace.denseSeq (ScalarProbeUnitSphere d) i)
  have hf : Continuous f := ENNReal.continuous_ofReal.comp (cutoff_probe_continuous M m U s ω)
  have hclosed : IsClosed {e | f e ≤ c} := isClosed_le hf continuous_const
  have hrange : Set.range (TopologicalSpace.denseSeq (ScalarProbeUnitSphere d)) ⊆ {e | f e ≤ c} := by
    rintro _ ⟨i, rfl⟩
    change f (TopologicalSpace.denseSeq (ScalarProbeUnitSphere d) i) ≤ c
    exact le_iSup (fun j : ℕ => f (TopologicalSpace.denseSeq (ScalarProbeUnitSphere d) j)) i
  have hall := closure_minimal hrange hclosed
  rw [(TopologicalSpace.denseRange_denseSeq (ScalarProbeUnitSphere d)).closure_range] at hall
  apply le_antisymm
  · exact iSup_le (fun e => hall (Set.mem_univ e))
  · exact iSup_le (fun i => le_iSup f (TopologicalSpace.denseSeq (ScalarProbeUnitSphere d) i))

theorem measurable_cascadeObservables_proof (M : SubdiffusiveProcess.Model.GMCModel d) (m : ℕ)
    (U : Ch02.Domain d) :
    (∀ s : ℝ, Measurable (scaledDefect M m U s)) ∧
      ∀ p q : Homogenization.Vec d,
        Measurable (fun ω => J U (aCutoffCoeffOnData M m ω U).toCoeffOn p q) := by
  have hd : d ≠ 0 := by have := M.shellPrefix.dimension; omega
  let : NeZero d := ⟨hd⟩
  refine ⟨?_, fun p q => measurable_cutoff_responseJ M m U p q⟩
  intro s
  have heq : scaledDefect M m U s = fun ω => ⨆ i : ℕ, ENNReal.ofReal
      (J U (aCutoffCoeffOnData M m ω U).toCoeffOn
        ((Real.sqrt s)⁻¹ • (TopologicalSpace.denseSeq (ScalarProbeUnitSphere d) i : Homogenization.Vec d))
        (Real.sqrt s • (TopologicalSpace.denseSeq (ScalarProbeUnitSphere d) i : Homogenization.Vec d))) :=
    funext (scaledDefect_eq_countable M m U s)
  rw [heq]
  exact Measurable.iSup (fun _ => (measurable_cutoff_responseJ M m U _ _).ennreal_ofReal)

end GMCExplicitDelta.Assembly
