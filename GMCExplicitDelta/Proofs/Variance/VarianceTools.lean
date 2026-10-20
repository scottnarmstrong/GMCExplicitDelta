module

public import GMCExplicitDelta.Proofs.Variance.FrozenMatrix
public import GMCExplicitDelta.Proofs.Variance.Moments
public import GMCExplicitDelta.Proofs.CellMoments.Variance

/-! # Centering identities for the frozen variances -/

@[expose] public section

open MeasureTheory Matrix Homogenization Homogenization.Book SubdiffusiveProcess.CoarseGrainingVocab
open scoped Matrix.Norms.Elementwise

namespace GMCExplicitDelta.Assembly

variable {d : ℕ}

/-- Integrability of a matrix implies integrability of its trace. -/
theorem frozenVar_integrable_trace {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {A : Ω → Homogenization.Mat d} (hA : Integrable A μ) :
    Integrable (fun ω => Matrix.trace (A ω)) μ :=
  integrable_finsetSum Finset.univ fun i _ => (hA.eval i).eval i

/-- Integrating the scalar-centering identity. -/
theorem frozenVar_integral_center {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {A : Ω → Homogenization.Mat d} (hA : Integrable (fun ω => Matrix.trace (A ω)) μ)
    (hF : Integrable (fun ω => frobSq (A ω)) μ) (c : ℝ) :
    (∫ ω, frobSq (A ω - c • (1 : Homogenization.Mat d)) ∂μ) =
      (∫ ω, frobSq (A ω) ∂μ) - 2 * c * (∫ ω, Matrix.trace (A ω) ∂μ) + (d : ℝ) * c ^ 2 := by
  simp_rw [frozenVar_frobSq_sub_scalar]
  have hsub : Integrable (fun ω => frobSq (A ω) - 2 * c * Matrix.trace (A ω)) μ :=
    hF.sub (hA.const_mul (2 * c))
  have heq := integral_sub hF (hA.const_mul (2 * c))
  rw [integral_add hsub (integrable_const _), heq, integral_const_mul, integral_const]
  simp only [probReal_univ, one_smul]

/-- Centering at the scalar trace mean minimizes the mean Frobenius square. -/
theorem frozenVar_center_min {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {A : Ω → Homogenization.Mat d} (hA : Integrable (fun ω => Matrix.trace (A ω)) μ)
    (hF : Integrable (fun ω => frobSq (A ω)) μ) (a : ℝ)
    (ha : (∫ ω, Matrix.trace (A ω) ∂μ) = (d : ℝ) * a) :
    (∫ ω, frobSq (A ω - a • (1 : Homogenization.Mat d)) ∂μ) ≤
      ∫ ω, frobSq (A ω - (1 : Homogenization.Mat d)) ∂μ := by
  rw [frozenVar_integral_center hA hF a,
    show (fun ω => frobSq (A ω - 1)) = (fun ω => frobSq (A ω - (1 : ℝ) • 1)) by
      simp only [one_smul], frozenVar_integral_center hA hF 1, ha]
  nlinarith only [mul_nonneg (Nat.cast_nonneg (α := ℝ) d) (sq_nonneg (a - 1))]

/-- The primal trace mean agrees with its defining normalization. -/
theorem frozenVar_trace_X_mean (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) :
    (∫ ω, Matrix.trace (frozenX M L (cubeAt 0 n) ω) ∂M.P.toMeasure) =
      (d : ℝ) * alphaMean M L n := by
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast (neZero_of_gmcModel M).ne
  unfold alphaMean
  rw [← mul_assoc, mul_inv_cancel₀ hd, one_mul]

/-- The dual trace mean agrees with its defining normalization. -/
theorem frozenVar_trace_Y_mean (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) :
    (∫ ω, Matrix.trace (frozenY M L (cubeAt 0 n) ω) ∂M.P.toMeasure) =
      (d : ℝ) * betaMean M L n := by
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast (neZero_of_gmcModel M).ne
  unfold betaMean
  rw [← mul_assoc, mul_inv_cancel₀ hd, one_mul]

end GMCExplicitDelta.Assembly
