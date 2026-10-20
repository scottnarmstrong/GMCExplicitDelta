module

public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.MeasureTheory.Order.Lattice
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Exponential moments of finite maxima, without independence (S8(c)) -/

@[expose] public section

open MeasureTheory Real

namespace GMCExplicitDelta.Source

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Exponential moments of a finite maximum are bounded by the sum of the individual moments.
All integrability assumptions are explicit; there is no joint-distribution assumption. -/
theorem integral_exp_finset_sup'_le (s : Finset ι) (hs : s.Nonempty)
    (X : ι → Ω → ℝ) (hX : ∀ i ∈ s, Measurable (X i)) (t B : ℝ)
    (hint : ∀ i ∈ s, Integrable (fun ω => exp (t * X i ω)) μ)
    (hbound : ∀ i ∈ s, ∫ ω, exp (t * X i ω) ∂μ ≤ B) :
    ∫ ω, exp (t * s.sup' hs (fun i => X i ω)) ∂μ ≤ s.card * B := by
  let F : Ω → ℝ := fun ω => ∑ i ∈ s, exp (t * X i ω)
  have hF : Integrable F μ := integrable_finsetSum s hint
  have hdom : ∀ ω, exp (t * s.sup' hs (fun i => X i ω)) ≤ F ω := by
    intro ω
    obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup' hs (fun i => X i ω)
    rw [heq]
    exact Finset.single_le_sum (fun j _ => (exp_pos (t * X j ω)).le) hi
  have hm : AEStronglyMeasurable
      (fun ω => exp (t * s.sup' hs (fun i => X i ω))) μ := by
    have hm := (s.measurable_sup' hs hX).const_mul t
    convert hm.exp.aestronglyMeasurable using 1
    funext ω
    rw [Finset.sup'_apply]
  have hi : Integrable (fun ω => exp (t * s.sup' hs (fun i => X i ω))) μ :=
    hF.mono' hm (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      exact hdom ω)
  calc
    _ ≤ ∫ ω, F ω ∂μ := integral_mono hi hF hdom
    _ = ∑ i ∈ s, ∫ ω, exp (t * X i ω) ∂μ := integral_finsetSum s hint
    _ ≤ ∑ _i ∈ s, B := Finset.sum_le_sum hbound
    _ = s.card * B := by rw [Finset.sum_const, nsmul_eq_mul]

/-- A power of a nonnegative finite maximum is dominated by the sum of the powers. -/
theorem integral_pow_finset_sup'_le (s : Finset ι) (hs : s.Nonempty)
    (X : ι → Ω → ℝ) (hX : ∀ i ∈ s, Measurable (X i))
    (hpos : ∀ i ∈ s, ∀ ω, 0 ≤ X i ω) (n : ℕ) (B : ℝ)
    (hint : ∀ i ∈ s, Integrable (fun ω => X i ω ^ n) μ)
    (hbound : ∀ i ∈ s, ∫ ω, X i ω ^ n ∂μ ≤ B) :
    ∫ ω, (s.sup' hs (fun i => X i ω)) ^ n ∂μ ≤ s.card * B := by
  let F : Ω → ℝ := fun ω => ∑ i ∈ s, X i ω ^ n
  have hF : Integrable F μ := integrable_finsetSum s hint
  have hdom : ∀ ω, (s.sup' hs (fun i => X i ω)) ^ n ≤ F ω := by
    intro ω
    obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup' hs (fun i => X i ω)
    rw [heq]
    exact Finset.single_le_sum (fun j hj => pow_nonneg (hpos j hj ω) n) hi
  have hm : AEStronglyMeasurable (fun ω => (s.sup' hs (fun i => X i ω)) ^ n) μ := by
    have hm := (s.measurable_sup' hs hX).pow_const n
    simpa only [Finset.sup'_apply] using hm.aestronglyMeasurable
  have hi : Integrable (fun ω => (s.sup' hs (fun i => X i ω)) ^ n) μ := by
    apply hF.mono' hm
    apply Filter.Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact hdom ω
    · obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup' hs (fun i => X i ω)
      rw [heq]
      exact pow_nonneg (hpos i hi ω) n
  calc
    _ ≤ ∫ ω, F ω ∂μ := integral_mono hi hF hdom
    _ = ∑ i ∈ s, ∫ ω, X i ω ^ n ∂μ := integral_finsetSum s hint
    _ ≤ ∑ _i ∈ s, B := Finset.sum_le_sum hbound
    _ = s.card * B := by rw [Finset.sum_const, nsmul_eq_mul]

end GMCExplicitDelta.Source
