module

public import GMCExplicitDelta.Proofs.CellMoments.Means
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Isotropy of second moments -/

@[expose] public section

open MeasureTheory Homogenization Homogenization.Book SubdiffusiveProcess.CoarseGrainingVocab
open scoped Matrix.Norms.Elementwise

namespace GMCExplicitDelta.Localization

open Assembly

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Conjugation by a fixed matrix commutes with integrable expectation. -/
theorem cellMoment_integral_conj {F : Ω → Homogenization.Mat d} (hF : Integrable F μ)
    (R : Homogenization.Mat d) :
    ∫ ω, R * F ω * R ∂μ = R * (∫ ω, F ω ∂μ) * R := by
  let C : Homogenization.Mat d →ₗ[ℝ] Homogenization.Mat d :=
    { toFun := fun A => R * A * R
      map_add' := by intros; simp only [Matrix.mul_add, Matrix.add_mul]
      map_smul' := by intros; simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] }
  exact C.toContinuousLinearMap.integral_comp_comm hF

/-- A measure-preserving conjugation symmetry passes to the expectation. -/
theorem cellMoment_integral_invariant {F : Ω → Homogenization.Mat d} (hF : Integrable F μ)
    {T : Ω → Ω} (hT : Measurable T) (hmap : Measure.map T μ = μ)
    (R : Homogenization.Mat d) (hrot : ∀ ω, F (T ω) = R * F ω * R) :
    R * (∫ ω, F ω ∂μ) * R = ∫ ω, F ω ∂μ := by
  rw [← cellMoment_integral_conj hF]
  calc
    _ = ∫ ω, F (T ω) ∂μ := integral_congr_ae (Filter.Eventually.of_forall fun ω => (hrot ω).symm)
    _ = _ := by
      have hm : AEStronglyMeasurable F (Measure.map T μ) := by
        rw [hmap]
        exact hF.aestronglyMeasurable
      have hi := integral_map hT.aemeasurable hm
      rw [hmap] at hi
      exact hi.symm

/-- Products of square-integrable entries give an integrable Gram matrix. -/
theorem cellMoment_integrable_gram {A : Ω → Homogenization.Mat d}
    (hA : ∀ i j, MemLp (fun ω => A ω i j) 2 μ) :
    Integrable (fun ω => (A ω).transpose * A ω) μ := by
  apply Integrable.of_eval
  intro i
  apply Integrable.of_eval
  intro j
  exact integrable_finsetSum Finset.univ fun k _ => (hA k i).integrable_mul (hA k j)

/-- A symmetric involution conjugates the Gram matrix in the same way. -/
theorem cellMoment_gram_conj (A R : Homogenization.Mat d) (hRt : R.transpose = R)
    (hRR : R * R = 1) :
    (R * A * R).transpose * (R * A * R) = R * (A.transpose * A) * R := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, hRt]
  calc
    _ = R * A.transpose * (R * R) * A * R := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hRR]; simp only [Matrix.mul_one, Matrix.mul_assoc]

/-- The trace of a Gram matrix is the squared Frobenius norm. -/
theorem cellMoment_trace_gram (A : Homogenization.Mat d) :
    Matrix.trace (A.transpose * A) = frobSq A := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, ← sq, frobSq]
  exact Finset.sum_comm

/-- The directional quadratic form of a Gram matrix is the squared image norm. -/
theorem cellMoment_gram_quadratic (A : Homogenization.Mat d) (q : Homogenization.Vec d) :
    vecDot q (matVecMul (A.transpose * A) q) = vecNormSq (A.mulVec q) := by
  change q ⬝ᵥ (A.transpose * A).mulVec q = (A.mulVec q) ⬝ᵥ (A.mulVec q)
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec]

/-- Integration commutes with a deterministic matrix quadratic form. -/
theorem cellMoment_integral_quadratic {A : Ω → Homogenization.Mat d} (hA : Integrable A μ)
    (q : Homogenization.Vec d) :
    ∫ ω, vecDot q (matVecMul (A ω) q) ∂μ = vecDot q (matVecMul (∫ ω, A ω ∂μ) q) := by
  let C : Homogenization.Mat d →ₗ[ℝ] ℝ :=
    { toFun := fun B => vecDot q (matVecMul B q)
      map_add' := by intros; simp only [add_matVecMul, vecDot_add_right]
      map_smul' := by intros; simp only [smul_matVecMul, vecDot_smul_right, RingHom.id_apply, smul_eq_mul] }
  exact C.toContinuousLinearMap.integral_comp_comm hA

/-- Scalar expected Gram matrices determine directional second moments from their trace. -/
theorem cellMoment_integral_normSq_of_scalar_gram [NeZero d] {A : Ω → Homogenization.Mat d}
    (hA : ∀ i j, MemLp (fun ω => A ω i j) 2 μ)
    (hscalar : IsScalarMatrix (∫ ω, (A ω).transpose * A ω ∂μ))
    (q : Homogenization.Vec d) :
    ∫ ω, vecNormSq ((A ω).mulVec q) ∂μ =
      vecNormSq q / d * ∫ ω, frobSq (A ω) ∂μ := by
  obtain ⟨s, hs⟩ := hscalar
  have hG := cellMoment_integrable_gram hA
  have htrace : ∫ ω, frobSq (A ω) ∂μ = (d : ℝ) * s := by
    simp_rw [← cellMoment_trace_gram]
    rw [freshRet_integral_trace hG, hs]
    simp [Matrix.trace, mul_comm]
  simp_rw [← cellMoment_gram_quadratic]
  rw [cellMoment_integral_quadratic hG, hs, smul_matVecMul, cellMoment_matVecMul_one,
    vecDot_smul_right, cellMoment_vecDot_self, htrace]
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
  field_simp

end GMCExplicitDelta.Localization
