module

public import Homogenization.Probability.EfronStein.Fin
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! Efron--Stein on the independent uniform child digits. -/
@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace GMCExplicitDelta.Localization.ProjPoincare

noncomputable def digitMeasure : Measure (Fin 3) := (PMF.uniformOfFintype (Fin 3)).toMeasure

instance digitMeasure_probability : IsProbabilityMeasure digitMeasure :=
  inferInstanceAs (IsProbabilityMeasure (PMF.uniformOfFintype (Fin 3)).toMeasure)

theorem digitMeasure_singleton (x : Fin 3) : digitMeasure {x} = (3 : ℝ≥0∞)⁻¹ := by
  unfold digitMeasure
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), PMF.uniformOfFintype_apply]
  norm_num

theorem digit_integral (f : Fin 3 → ℝ) : ∫ x, f x ∂digitMeasure = (1 / 3 : ℝ) * ∑ x, f x := by
  rw [integral_fintype (memLp_one_iff_integrable.mp MemLp.of_discrete)]
  simp only [Measure.real, digitMeasure_singleton, ENNReal.toReal_inv, ENNReal.toReal_ofNat,
    smul_eq_mul, ← Finset.mul_sum]
  ring

theorem digitPi_integral (d : ℕ) (F : (Fin d → Fin 3) → ℝ) :
    (∫ x, F x ∂(Measure.pi fun _ : Fin d => digitMeasure)) =
      ((3 : ℝ) ^ d)⁻¹ * ∑ x, F x := by
  have hm (x : Fin d → Fin 3) : (Measure.pi fun _ : Fin d => digitMeasure).real {x} = ((3 : ℝ) ^ d)⁻¹ := by
    simp only [Measure.real, Measure.pi_singleton, digitMeasure_singleton, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, ENNReal.toReal_pow, ENNReal.toReal_inv,
      ENNReal.toReal_ofNat, inv_pow]
  rw [integral_fintype (memLp_one_iff_integrable.mp MemLp.of_discrete)]
  simp only [hm, smul_eq_mul, ← Finset.mul_sum]

/-- Efron--Stein written entirely as finite sums over child digits. -/
theorem child_digits_efronStein (d : ℕ) (F : (Fin d → Fin 3) → ℝ) :
    ((3 : ℝ) ^ d)⁻¹ * (∑ x, (F x - ((3 : ℝ) ^ d)⁻¹ * ∑ y, F y) ^ 2) ≤
      (1 / 2 : ℝ) * ∑ i : Fin d,
        ((3 : ℝ) ^ d)⁻¹ * ∑ x, (1 / 3 : ℝ) * ∑ y : Fin 3,
          (F (Function.update x i y) - F x) ^ 2 := by
  obtain ⟨M, hM⟩ := Finite.exists_le (fun x => |F x|)
  have h := Homogenization.efronStein_pi (fun _ : Fin d => digitMeasure)
    (F := F) (Measurable.of_discrete (f := F)) hM
  rw [variance_eq_integral (Measurable.of_discrete (f := F)).aemeasurable] at h
  simp_rw [digitPi_integral, digit_integral] at h
  exact h

/-- Peel one uniform digit off the finite product. -/
theorem digitPi_peel (n : ℕ) (i : Fin (n + 1)) (F : (Fin (n + 1) → Fin 3) → ℝ) :
    (∫ x, F x ∂(Measure.pi fun _ : Fin (n + 1) => digitMeasure)) =
      ∫ z, ∫ r, F (i.insertNth r z) ∂digitMeasure
        ∂(Measure.pi fun _ : Fin n => digitMeasure) := by
  let μ : Fin (n + 1) → Measure (Fin 3) := fun _ => digitMeasure
  have hm := measurePreserving_piFinSuccAbove μ i
  have hf : Integrable F (Measure.pi μ) := memLp_one_iff_integrable.mp MemLp.of_discrete
  have hf' := hm.symm.integrable_comp_of_integrable hf
  rw [← hm.symm.integral_comp' F]
  change (∫ x, (F ∘ (MeasurableEquiv.piFinSuccAbove (fun _ => Fin 3) i).symm) x
    ∂(μ i).prod (Measure.pi fun j => μ (i.succAbove j))) = _
  rw [integral_prod_symm _ hf']
  rfl

end GMCExplicitDelta.Localization.ProjPoincare
