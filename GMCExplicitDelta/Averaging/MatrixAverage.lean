module

public import GMCExplicitDelta.Averaging.SignedSphereRandom
public import GMCExplicitDelta.Averaging.MeanSensitiveAverage
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Mean-sensitive averaging of positive semidefinite matrices -/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal Matrix.Norms.L2Operator
open GMCExplicitDelta.Insertion

namespace GMCExplicitDelta.Averaging

/-- A fixed quadratic probe is continuous and linear in the matrix. -/
noncomputable def matrixProbe {d : ℕ} (u : EuclideanSpace ℝ (Fin d)) :
    Matrix (Fin d) (Fin d) ℝ →L[ℝ] ℝ :=
  ({ toFun := fun A => sphereQuadratic A u
     map_add' := fun A B => by simp [sphereQuadratic, map_add, inner_add_right]
     map_smul' := fun c A => by simp [sphereQuadratic, map_smul, inner_smul_right] } :
    Matrix (Fin d) (Fin d) ℝ →ₗ[ℝ] ℝ).toContinuousLinearMap

@[simp]
theorem matrixProbe_apply {d : ℕ} (u : EuclideanSpace ℝ (Fin d))
    (A : Matrix (Fin d) (Fin d) ℝ) : matrixProbe u A = sphereQuadratic A u := rfl

/-- The centered empirical matrix average. -/
noncomputable def centeredMatrixAverage {Ω : Type*} [MeasurableSpace Ω] {d n : ℕ}
    (μ : Measure Ω) (M : Fin n → Ω → Matrix (Fin d) (Fin d) ℝ) (ω : Ω) :
    Matrix (Fin d) (Fin d) ℝ :=
  (n : ℝ)⁻¹ • ∑ i, (M i ω - ∫ ω', M i ω' ∂μ)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {d n : ℕ} {M : Fin n → Ω → Matrix (Fin d) (Fin d) ℝ}

theorem memLp_centeredMatrixAverage (hm : ∀ i, MemLp (M i) 32 μ) :
    MemLp (centeredMatrixAverage μ M) 32 μ := by
  exact (memLp_finsetSum Finset.univ (fun i _ =>
    (hm i).sub (memLp_const _))).const_smul ((n : ℝ)⁻¹)

omit [IsProbabilityMeasure μ] in
theorem integral_matrix_isHermitian {A : Ω → Matrix (Fin d) (Fin d) ℝ}
    (hi : Integrable A μ) (hA : ∀ ω, (A ω).IsHermitian) :
    (∫ ω, A ω ∂μ).IsHermitian := by
  let t := (Matrix.transposeLinearEquiv (Fin d) (Fin d) ℝ ℝ).toLinearMap.toContinuousLinearMap
  change t (∫ ω, A ω ∂μ) = ∫ ω, A ω ∂μ
  rw [← t.integral_comp_comm hi]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
    Matrix.isHermitian_iff_isSymm.mp (hA ω))

theorem centeredMatrixAverage_isHermitian (hm : ∀ i, MemLp (M i) 32 μ)
    (hM : ∀ i ω, (M i ω).IsHermitian) (ω : Ω) :
    (centeredMatrixAverage μ M ω).IsHermitian := by
  apply Matrix.IsHermitian.smul _ (by rfl)
  rw [Matrix.isHermitian_iff_isSelfAdjoint]
  apply isSelfAdjoint_sum
  intro i _
  rw [← Matrix.isHermitian_iff_isSelfAdjoint]
  exact (hM i ω).sub (integral_matrix_isHermitian ((hm i).integrable (by norm_num)) (hM i))

theorem matrixProbe_centeredMatrixAverage (hm : ∀ i, MemLp (M i) 32 μ)
    (u : EuclideanSpace ℝ (Fin d)) (ω : Ω) :
    sphereQuadratic (centeredMatrixAverage μ M ω) u =
      (n : ℝ)⁻¹ * ∑ i, (sphereQuadratic (M i ω) u - ∫ ω', sphereQuadratic (M i ω') u ∂μ) := by
  change matrixProbe u ((n : ℝ)⁻¹ • ∑ i, (M i ω - ∫ ω', M i ω' ∂μ)) = _
  rw [map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sub, ← (matrixProbe u).integral_comp_comm ((hm i).integrable (by norm_num))]
  rfl

end GMCExplicitDelta.Averaging
