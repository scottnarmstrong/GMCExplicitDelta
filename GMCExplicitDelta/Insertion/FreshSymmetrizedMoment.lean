module

public import GMCExplicitDelta.Insertion.FreshEvenBinomial
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-! # Nonnegative symmetrization of the competitor moment -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace GMCExplicitDelta.Insertion

/-- Whole-field sign symmetry gives the even binomial moment expansion directly
for nonnegative integrals, without a separate signed-integrability argument. -/
theorem lintegral_pow_eq_even_binomial {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {τ : Ω → Ω} (hτ : MeasurePreserving τ μ μ) {A O : Ω → ℝ}
    (hA : Measurable A) (hO : Measurable O)
    (hAe : ∀ ω, A (τ ω) = A ω) (hOo : ∀ ω, O (τ ω) = -O ω)
    {p : ℕ} (hp : Even p) :
    (∫⁻ ω, ENNReal.ofReal ((A ω + O ω) ^ p) ∂μ) =
      ∫⁻ ω, ENNReal.ofReal (∑ i ∈ Finset.range (p + 1),
        if Even i then (p.choose i : ℝ) * A ω ^ (p - i) * |O ω| ^ i else 0) ∂μ := by
  have hm : Measurable (fun ω => ENNReal.ofReal ((A ω + O ω) ^ p)) :=
    ((hA.add hO).pow_const p).ennreal_ofReal
  have hn : Measurable (fun ω => ENNReal.ofReal ((A ω - O ω) ^ p)) :=
    ((hA.sub hO).pow_const p).ennreal_ofReal
  have hs := hτ.lintegral_comp hm
  change (∫⁻ ω, ENNReal.ofReal ((A (τ ω) + O (τ ω)) ^ p) ∂μ) =
    ∫⁻ ω, ENNReal.ofReal ((A ω + O ω) ^ p) ∂μ at hs
  simp only [hAe, hOo, ← sub_eq_add_neg] at hs
  have hc : ENNReal.ofReal ((1 : ℝ) / 2) * (2 : ℝ≥0∞) = 1 := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    norm_num
  have hsum : Measurable (fun ω => ENNReal.ofReal ((A ω + O ω) ^ p) +
      ENNReal.ofReal ((A ω - O ω) ^ p)) := hm.add hn
  calc
    _ = ENNReal.ofReal ((1 : ℝ) / 2) *
        ((∫⁻ ω, ENNReal.ofReal ((A ω + O ω) ^ p) ∂μ) +
          ∫⁻ ω, ENNReal.ofReal ((A ω - O ω) ^ p) ∂μ) := by
      rw [hs, ← two_mul, ← mul_assoc, hc, one_mul]
    _ = ∫⁻ ω, ENNReal.ofReal ((1 : ℝ) / 2) *
        (ENNReal.ofReal ((A ω + O ω) ^ p) + ENNReal.ofReal ((A ω - O ω) ^ p)) ∂μ := by
      rw [lintegral_const_mul _ hsum, lintegral_add_aux hm hn]
    _ = _ := by
      apply lintegral_congr
      intro ω
      rw [← ENNReal.ofReal_add (hp.pow_nonneg _) (hp.pow_nonneg _),
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      congr 1
      rw [← symmetrized_power_eq_even_sum]
      ring

end GMCExplicitDelta.Insertion
