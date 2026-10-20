module

public import GMCExplicitDelta.Proofs.Variance.Cauchy

/-! # Finite families of matrix observables in L2 -/

@[expose] public section

open MeasureTheory Matrix Homogenization Homogenization.Book

namespace GMCExplicitDelta.Assembly

variable {d : ℕ} {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {A B : ι → Ω → Homogenization.Mat d}
    (hA : ∀ r i j, MemLp (fun ω => A r ω i j) 2 μ)
    (hB : ∀ r i j, MemLp (fun ω => B r ω i j) 2 μ)

include hA hB

theorem frozenVar_family_pair_le :
    (∑ r, ∫ ω, frozenVar_matrixPair (A r ω) (B r ω) ∂μ) ≤
      Real.sqrt (∑ r, ∫ ω, frobSq (A r ω) ∂μ) *
        Real.sqrt (∑ r, ∫ ω, frobSq (B r ω) ∂μ) := by
  have hnonnegA (r : ι) : (0 : ℝ) ≤ ∫ ω, frobSq (A r ω) ∂μ :=
    integral_nonneg fun ω => frobSq_nonneg (A r ω)
  have hnonnegB (r : ι) : (0 : ℝ) ≤ ∫ ω, frobSq (B r ω) ∂μ :=
    integral_nonneg fun ω => frobSq_nonneg (B r ω)
  calc
    _ ≤ ∑ r, Real.sqrt (∫ ω, frobSq (A r ω) ∂μ) *
        Real.sqrt (∫ ω, frobSq (B r ω) ∂μ) :=
      Finset.sum_le_sum fun r _ => frozenVar_integral_matrixPair_le (hA r) (hB r)
    _ ≤ _ := by
      have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset ι)
        (fun r => Real.sqrt (∫ ω, frobSq (A r ω) ∂μ))
        (fun r => Real.sqrt (∫ ω, frobSq (B r ω) ∂μ))
      simpa only [Real.sq_sqrt (hnonnegA _), Real.sq_sqrt (hnonnegB _)] using h

theorem frozenVar_family_triangle :
    Real.sqrt (∑ r, ∫ ω, frobSq (A r ω + B r ω) ∂μ) ≤
      Real.sqrt (∑ r, ∫ ω, frobSq (A r ω) ∂μ) +
        Real.sqrt (∑ r, ∫ ω, frobSq (B r ω) ∂μ) := by
  have hna : (0 : ℝ) ≤ ∑ r, ∫ ω, frobSq (A r ω) ∂μ :=
    Finset.sum_nonneg fun r _ => integral_nonneg fun ω => frobSq_nonneg (A r ω)
  have hnb : (0 : ℝ) ≤ ∑ r, ∫ ω, frobSq (B r ω) ∂μ :=
    Finset.sum_nonneg fun r _ => integral_nonneg fun ω => frobSq_nonneg (B r ω)
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · simp_rw [frozenVar_integral_frobSq_add (hA _) (hB _)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    have h := frozenVar_family_pair_le hA hB
    nlinarith only [h, Real.sq_sqrt hna, Real.sq_sqrt hnb]

end GMCExplicitDelta.Assembly
