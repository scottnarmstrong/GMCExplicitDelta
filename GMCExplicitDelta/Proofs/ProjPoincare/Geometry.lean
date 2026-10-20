module

public import GMCExplicitDelta.Proofs.HaarMode.Tensor
public import GMCExplicitDelta.Proofs.ProjPoincare.Scalar
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Coordinate slicing and integrability on triadic cubes. -/
@[expose] public section

open Homogenization MeasureTheory Set
open scoped ENNReal

namespace GMCExplicitDelta.Localization.ProjPoincare

variable {d n : ℕ}

noncomputable def childCube (Q : TriadicCube d) (a : Fin d → Fin 3) : TriadicCube d :=
  ⟨Q.scale - 1, fun i => 3 * Q.index i + (a i : ℤ) - 1⟩

def faceCube (Q : TriadicCube (n + 1)) (i : Fin (n + 1)) : TriadicCube n :=
  ⟨Q.scale, fun j => Q.index (i.succAbove j)⟩

noncomputable def coordMeasure (Q : TriadicCube d) (i : Fin d) : Measure ℝ :=
  ENNReal.ofReal (cubeScaleFactor Q)⁻¹ • volume.restrict
    (Ico (((Q.index i : ℝ) - 1 / 2) * cubeScaleFactor Q)
      (((Q.index i : ℝ) + 1 / 2) * cubeScaleFactor Q))

instance coordMeasure_finite (Q : TriadicCube d) (i : Fin d) : IsFiniteMeasure (coordMeasure Q i) :=
  (volume.restrict _).smul_finite ENNReal.ofReal_ne_top

theorem normalizedCubeMeasure_pi (Q : TriadicCube d) :
    normalizedCubeMeasure Q = Measure.pi (coordMeasure Q) := (haarMode_normalizedCubeMeasure_pi Q).symm

theorem continuous_memLp_cube (Q : TriadicCube d) {f : Homogenization.Vec d → ℝ}
    (hf : Continuous f) (p : ℝ≥0∞) : MemLp f p (normalizedCubeMeasure Q) := by
  obtain ⟨C, hC⟩ := (isBounded_cubeSet Q).isCompact_closure.exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable C
  unfold normalizedCubeMeasure cubeMeasure
  apply Measure.ae_smul_measure
  apply (ae_restrict_iff' (measurableSet_cubeSet Q)).mpr
  exact Filter.Eventually.of_forall (fun x hx => hC x (subset_closure hx))

/-- Averaging over the remaining coordinates contracts the squared norm. -/
theorem cubeAverage_sq_le (Q : TriadicCube d) {f : Homogenization.Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    (cubeAverage Q f) ^ 2 ≤ cubeAverage Q (fun x => f x ^ 2) := by
  simp only [cubeAverage_eq_integral_normalizedCubeMeasure]
  simpa [Measure.real, normalizedCubeMeasure_apply_univ] using
    integral_mul_sq_le hf (memLp_const (1 : ℝ))

/-- Fubini on a cube, with a chosen coordinate as its inner interval. -/
theorem cubeAverage_peel (Q : TriadicCube (n + 1)) (i : Fin (n + 1))
    {f : Homogenization.Vec (n + 1) → ℝ} (hf : Integrable f (normalizedCubeMeasure Q)) :
    cubeAverage Q f = cubeAverage (faceCube Q i)
      (fun z => ∫ t, f (i.insertNth t z) ∂(coordMeasure Q i)) := by
  have hm := measurePreserving_piFinSuccAbove (coordMeasure Q) i
  have hf' : Integrable f (Measure.pi (coordMeasure Q)) := by rwa [← normalizedCubeMeasure_pi Q]
  have hf'' := hm.symm.integrable_comp_of_integrable hf'
  simp only [cubeAverage_eq_integral_normalizedCubeMeasure]
  rw [normalizedCubeMeasure_pi Q, ← hm.symm.integral_comp' f]
  change (∫ x, (f ∘ (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i).symm) x
    ∂(coordMeasure Q i).prod (Measure.pi fun j => coordMeasure Q (i.succAbove j))) = _
  rw [integral_prod_symm _ hf'']
  rw [normalizedCubeMeasure_pi (faceCube Q i)]
  rfl

theorem coord_integral (Q : TriadicCube d) (i : Fin d) (f : ℝ → ℝ) :
    (∫ t, f t ∂(coordMeasure Q i)) = (cubeScaleFactor Q)⁻¹ *
      ∫ t in (((Q.index i : ℝ) - 1 / 2) * cubeScaleFactor Q)..
        (((Q.index i : ℝ) + 1 / 2) * cubeScaleFactor Q), f t := by
  have hS : 0 < cubeScaleFactor Q := by unfold cubeScaleFactor; positivity
  have hab : ((Q.index i : ℝ) - 1 / 2) * cubeScaleFactor Q ≤
      ((Q.index i : ℝ) + 1 / 2) * cubeScaleFactor Q := by nlinarith only [hS]
  unfold coordMeasure
  rw [integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr hS.le)]
  rw [intervalIntegral.integral_of_le hab, integral_Ico_eq_integral_Ioc, smul_eq_mul]

end GMCExplicitDelta.Localization.ProjPoincare
