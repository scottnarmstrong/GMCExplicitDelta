module

public import GMCExplicitDelta.Proofs.Variance.Matrix
public import GMCExplicitDelta.Proofs.CellMoments.Variance
public import Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.Additivity.AnalyticInequalities

/-! # Frobenius Cauchy and triangle estimates under expectation -/

@[expose] public section

open MeasureTheory Matrix Homogenization Homogenization.Book

namespace GMCExplicitDelta.Assembly

variable {d : ℕ}

noncomputable def frozenVar_matrixPair (A B : Homogenization.Mat d) : ℝ := ∑ i, ∑ j, A i j * B i j

theorem frozenVar_matrixPair_le (A B : Homogenization.Mat d) :
    frozenVar_matrixPair A B ≤ Real.sqrt (frobSq A) * Real.sqrt (frobSq B) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin d × Fin d))
    (fun p => A p.1 p.2) (fun p => B p.1 p.2)
  simpa only [frozenVar_matrixPair, frobSq, Fintype.sum_prod_type] using h

theorem frozenVar_matrixPair_eq_trace (A B : Homogenization.Mat d) :
    frozenVar_matrixPair A B = Matrix.trace (Aᵀ * B) := by
  simp only [frozenVar_matrixPair, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_comm

theorem frozenVar_frobSq_add (A B : Homogenization.Mat d) :
    frobSq (A + B) = frobSq A + frobSq B + 2 * frozenVar_matrixPair A B := by
  change Matrix (Fin d) (Fin d) ℝ at A B
  have hpoint (i j : Fin d) : (A i j + B i j) ^ 2 =
      A i j ^ 2 + B i j ^ 2 + 2 * (A i j * B i j) := by ring
  simp only [frobSq, Matrix.add_apply, hpoint, Finset.sum_add_distrib,
    ← Finset.mul_sum, frozenVar_matrixPair]

section Integral

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {A B : Ω → Homogenization.Mat d}
    (hA : ∀ i j, MemLp (fun ω => A ω i j) 2 μ)
    (hB : ∀ i j, MemLp (fun ω => B ω i j) 2 μ)

include hA hB

omit [IsFiniteMeasure μ] in
theorem frozenVar_integrable_matrixPair : Integrable (fun ω => frozenVar_matrixPair (A ω) (B ω)) μ :=
  integrable_finsetSum Finset.univ fun i _ => integrable_finsetSum Finset.univ fun j _ =>
    (hA i j).integrable_mul (hB i j)

theorem frozenVar_integral_matrixPair_le :
    (∫ ω, frozenVar_matrixPair (A ω) (B ω) ∂μ) ≤
      Real.sqrt (∫ ω, frobSq (A ω) ∂μ) * Real.sqrt (∫ ω, frobSq (B ω) ∂μ) := by
  have hfa := Localization.cellMoment_integrable_frobSq hA
  have hfb := Localization.cellMoment_integrable_frobSq hB
  have hprod := Ch05.Section53.JUpperBoundWeakNorms.integrable_sqrt_mul_sqrt_of_integrable_of_ae_nonneg
    hfa hfb (Filter.Eventually.of_forall fun ω => frobSq_nonneg (A ω))
    (Filter.Eventually.of_forall fun ω => frobSq_nonneg (B ω))
  exact (integral_mono (frozenVar_integrable_matrixPair hA hB) hprod
    (fun ω => frozenVar_matrixPair_le (A ω) (B ω))).trans
    (Ch05.Section53.JUpperBoundWeakNorms.integral_sqrt_mul_sqrt_le_sqrt_integral_mul_sqrt_integral
      hfa hfb (Filter.Eventually.of_forall fun ω => frobSq_nonneg (A ω))
      (Filter.Eventually.of_forall fun ω => frobSq_nonneg (B ω)))

omit [IsFiniteMeasure μ] in
theorem frozenVar_integral_frobSq_add :
    (∫ ω, frobSq (A ω + B ω) ∂μ) =
      (∫ ω, frobSq (A ω) ∂μ) + (∫ ω, frobSq (B ω) ∂μ) +
        2 * ∫ ω, frozenVar_matrixPair (A ω) (B ω) ∂μ := by
  simp_rw [frozenVar_frobSq_add]
  have hsum : Integrable (fun ω => frobSq (A ω) + frobSq (B ω)) μ :=
    (Localization.cellMoment_integrable_frobSq hA).add (Localization.cellMoment_integrable_frobSq hB)
  rw [integral_add hsum ((frozenVar_integrable_matrixPair hA hB).const_mul 2),
    integral_add (Localization.cellMoment_integrable_frobSq hA) (Localization.cellMoment_integrable_frobSq hB),
    integral_const_mul]

theorem frozenVar_integral_frobSq_triangle :
    Real.sqrt (∫ ω, frobSq (A ω + B ω) ∂μ) ≤
      Real.sqrt (∫ ω, frobSq (A ω) ∂μ) + Real.sqrt (∫ ω, frobSq (B ω) ∂μ) := by
  have hna : (0 : ℝ) ≤ ∫ ω, frobSq (A ω) ∂μ := integral_nonneg fun ω => frobSq_nonneg (A ω)
  have hnb : (0 : ℝ) ≤ ∫ ω, frobSq (B ω) ∂μ := integral_nonneg fun ω => frobSq_nonneg (B ω)
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · rw [frozenVar_integral_frobSq_add hA hB]
    have h := frozenVar_integral_matrixPair_le hA hB
    nlinarith only [h, Real.sq_sqrt hna, Real.sq_sqrt hnb]

end Integral

end GMCExplicitDelta.Assembly
