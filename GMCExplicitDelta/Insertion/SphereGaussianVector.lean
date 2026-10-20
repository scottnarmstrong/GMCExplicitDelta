module

public import GMCExplicitDelta.Insertion.SphereGaussian
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Gaussian projection moments for C13

Vectors use the Euclidean norm and real inner product, in particular on
`EuclideanSpace ℝ (Fin d)`; the function-space sup norm is never used.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Nat NNReal RealInnerProductSpace

namespace GMCExplicitDelta.Insertion

/-- Every linear functional of a standard Gaussian has the expected even moment. -/
theorem integral_strongDual_pow_stdGaussian_even
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : StrongDual ℝ E) (p : ℕ) :
    (∫ x : E, (L x) ^ (2 * p) ∂stdGaussian E) =
      ((2 * p - 1)‼ : ℝ) * ‖L‖ ^ (2 * p) := by
  have hm : (stdGaussian E).map L =
      gaussianReal 0 (NNReal.mk (‖L‖ ^ 2) (sq_nonneg ‖L‖)) := by
    rw [IsGaussian.map_eq_gaussianReal L, integral_strongDual_stdGaussian,
      variance_dual_stdGaussian]
    congr 1
    ext
    simpa only [NNReal.coe_mk] using Real.coe_toNNReal _ (sq_nonneg ‖L‖)
  rw [← integral_map (f := fun x : ℝ => x ^ (2 * p))
    (by fun_prop : AEMeasurable L (stdGaussian E)) (by fun_prop), hm]
  exact integral_pow_gaussianReal_sq_even ‖L‖ p

/-- The even moment of the Euclidean projection along an arbitrary vector. -/
theorem integral_inner_pow_stdGaussian_even
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (v : E) (p : ℕ) :
    (∫ x : E, ⟪v, x⟫ ^ (2 * p) ∂stdGaussian E) =
      ((2 * p - 1)‼ : ℝ) * ‖v‖ ^ (2 * p) := by
  simpa only [innerSL_apply_apply, innerSL_apply_norm] using
    integral_strongDual_pow_stdGaussian_even (innerSL ℝ v) p

end GMCExplicitDelta.Insertion
