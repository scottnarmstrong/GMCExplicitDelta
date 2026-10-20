module

public import GMCExplicitDelta.Insertion.FreshLorentz
public import Homogenization.CoarseGraining.QuadraticStability.Integral

/-! # Integrated Cauchy–Schwarz for the deterministic odd weight -/

@[expose] public section

open MeasureTheory Homogenization

namespace GMCExplicitDelta.Insertion

/-- A pointwise product bound gives the sharp product of integrated energies. -/
theorem integral_abs_le_sqrt_integral_mul_sqrt_integral
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {z f g : Ω → ℝ}
    (hz : Integrable z μ) (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : ∀ᵐ ω ∂μ, 0 ≤ f ω) (hg0 : ∀ᵐ ω ∂μ, 0 ≤ g ω)
    (hpoint : ∀ᵐ ω ∂μ, z ω ^ 2 ≤ f ω * g ω) :
    (∫ ω, |z ω| ∂μ) ≤ Real.sqrt (∫ ω, f ω ∂μ) * Real.sqrt (∫ ω, g ω ∂μ) := by
  have hmeas : AEStronglyMeasurable
      (fun ω => Real.sqrt (f ω) * Real.sqrt (g ω)) μ :=
    (Real.continuous_sqrt.comp_aestronglyMeasurable hf.aestronglyMeasurable).mul
      (Real.continuous_sqrt.comp_aestronglyMeasurable hg.aestronglyMeasurable)
  have hi : Integrable (fun ω => Real.sqrt (f ω) * Real.sqrt (g ω)) μ := by
    apply ((hf.add hg).div_const 2).mono' hmeas
    filter_upwards [hf0, hg0] with ω hωf hωg
    rw [Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    exact sqrt_mul_sqrt_le_half_add hωf hωg
  refine (integral_mono_ae hz.abs hi ?_).trans (integral_sqrt_mul_sqrt_le hf hg hf0 hg0)
  filter_upwards [hf0, hpoint] with ω hωf hω
  rw [← Real.sqrt_mul hωf]
  exact Real.le_sqrt_of_sq_le (by simpa only [sq_abs] using hω)

end GMCExplicitDelta.Insertion
