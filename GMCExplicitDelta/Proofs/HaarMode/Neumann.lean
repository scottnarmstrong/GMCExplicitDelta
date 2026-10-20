module

public import GMCExplicitDelta.Localization.HaarDefs
public import Homogenization.Sobolev.Foundations.CubePoisson.Solver
public import Homogenization.Sobolev.Foundations.H1Graph.CoerciveHilbert

/-! # H2: existence of the Neumann primitive on a triadic cube -/

@[expose] public section

open MeasureTheory Homogenization Homogenization.Book

namespace GMCExplicitDelta.Localization

variable {d : ℕ}

/-- H2 with the exact localization statement. -/
theorem neumann_exists_proof (Q : Homogenization.TriadicCube d)
    (G : Homogenization.Vec d → Homogenization.Vec d)
    (hG : ∀ i, MeasureTheory.MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q)) :
    ∃ w : H1Function (openCubeSet Q), IsNeumannPrimitive Q G w := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) := by
    simpa only [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hg : MemVectorL2 (openCubeSet Q) G :=
    MemLp.of_eval fun i => memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q (hG i)
  let hC := translatedCubeMeanZeroH1CoerciveEstimate Q
  let u := H1MeanZeroFunction.gradientProblemSolution hg hC
  refine ⟨u.toH1Function, ?_, ?_⟩
  · unfold cubeAverage
    rw [setIntegral_cubeSet_eq_setIntegral_openCubeSet, u.meanZero, mul_zero]
  · intro φ
    have heq := H1Function.gradientProblemSolution_firstVariation_eq_integral hg hC φ
    simpa only [cubeAverage, setIntegral_cubeSet_eq_setIntegral_openCubeSet] using
      congrArg (fun t : ℝ => (cubeVolume Q)⁻¹ * t) heq

end GMCExplicitDelta.Localization
