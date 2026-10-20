module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Generic probabilistic lemmas: Fubini on `[0,h]` and products of square integrable functions
-/

@[expose] public section

namespace GMCExplicitDelta.Source

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Fubini for an interval integral against a probability measure, for a jointly measurable integrand
bounded by an integrable function on `[0,h]`.  Also returns integrability of the inner integral. -/
theorem integral_intervalIntegral_swap {P : Measure Ω} [IsFiniteMeasure P] {Ψ : ℝ → Ω → ℝ}
    (hm : Measurable (Function.uncurry Ψ)) {h : ℝ} (hh : 0 ≤ h) {B : Ω → ℝ} (hB : Integrable B P)
    (hb : ∀ ω t, t ∈ Set.Icc (0:ℝ) h → |Ψ t ω| ≤ B ω) :
    Integrable (fun ω => ∫ t in (0:ℝ)..h, Ψ t ω) P ∧
    ∫ t in (0:ℝ)..h, (∫ ω, Ψ t ω ∂P) = ∫ ω, (∫ t in (0:ℝ)..h, Ψ t ω) ∂P := by
  set cl : ℝ → ℝ := fun t => max 0 (min t h) with hcl
  have hclm : ∀ t, cl t ∈ Set.Icc (0:ℝ) h := fun t =>
    ⟨le_max_left _ _, max_le hh (min_le_right _ _)⟩
  have hcleq : ∀ t ∈ Set.Icc (0:ℝ) h, cl t = t := fun t ht => by
    simp only [hcl, min_eq_left ht.2, max_eq_right ht.1]
  set Ψ' : ℝ → Ω → ℝ := fun t ω => Ψ (cl t) ω with hΨ'
  have hm' : Measurable (Function.uncurry Ψ') := by
    have : Function.uncurry Ψ' = Function.uncurry Ψ ∘ (fun p : ℝ × Ω => (cl p.1, p.2)) := rfl
    rw [this]
    exact hm.comp ((measurable_const.max (measurable_fst.min measurable_const)).prodMk measurable_snd)
  have : IsFiniteMeasure (volume.restrict (Set.uIoc (0:ℝ) h)) := by
    rw [Set.uIoc_of_le hh]; infer_instance
  have hint : Integrable (Function.uncurry Ψ') ((volume.restrict (Set.uIoc (0:ℝ) h)).prod P) := by
    refine Integrable.mono' (g := fun p : ℝ × Ω => B p.2) (hB.comp_snd _) hm'.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs]
    exact hb p.2 (cl p.1) (hclm p.1)
  have hswap := intervalIntegral_integral_swap hint
  have hL : ∫ t in (0:ℝ)..h, (∫ ω, Ψ t ω ∂P) = ∫ t in (0:ℝ)..h, (∫ ω, Ψ' t ω ∂P) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hh] at ht
    simp only [hΨ', hcleq t ht]
  have hR : ∀ ω, ∫ t in (0:ℝ)..h, Ψ t ω = ∫ t in (0:ℝ)..h, Ψ' t ω := fun ω => by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hh] at ht
    simp only [hΨ', hcleq t ht]
  refine ⟨?_, ?_⟩
  · refine hint.integral_prod_right.congr (Filter.Eventually.of_forall fun ω => ?_)
    show ∫ t, Ψ' t ω ∂(volume.restrict (Set.uIoc (0:ℝ) h)) = ∫ t in (0:ℝ)..h, Ψ t ω
    rw [hR ω, Set.uIoc_of_le hh, intervalIntegral.integral_of_le hh]
  · rw [hL, hswap]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => (hR ω).symm)

/-- Square integrable measurable functions have integrable product. -/
theorem integrable_mul_of_sq {P : Measure Ω} {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hf2 : Integrable (fun ω => f ω ^ 2) P) (hg2 : Integrable (fun ω => g ω ^ 2) P) :
    Integrable (fun ω => f ω * g ω) P := by
  refine Integrable.mono' (g := fun ω => (f ω ^ 2 + g ω ^ 2) / 2) ((hf2.add hg2).div_const 2)
    (hf.mul hg).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_abs (f ω), sq_abs (g ω), sq_nonneg (|f ω| - |g ω|), abs_nonneg (f ω), abs_nonneg (g ω)]

/-- Quadratic expansion of a finite linear combination of square integrable functions. -/
theorem integral_sq_sum {P : Measure Ω} {ι : Type*} [Fintype ι] {f : ι → Ω → ℝ}
    (hint : ∀ i j, Integrable (fun ω => f i ω * f j ω) P) (x : ι → ℝ) :
    ∫ ω, (∑ i, x i * f i ω) ^ 2 ∂P = ∑ i, ∑ j, x i * x j * ∫ ω, f i ω * f j ω ∂P := by
  have e : ∀ ω, (∑ i, x i * f i ω) ^ 2 = ∑ i, ∑ j, x i * x j * (f i ω * f j ω) := fun ω => by
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp_rw [e]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => (hint i j).const_mul _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => (hint i j).const_mul _)]
  exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _

theorem integrable_sq_sum {P : Measure Ω} {ι : Type*} [Fintype ι] {f : ι → Ω → ℝ}
    (hint : ∀ i j, Integrable (fun ω => f i ω * f j ω) P) (x : ι → ℝ) :
    Integrable (fun ω => (∑ i, x i * f i ω) ^ 2) P := by
  have e : ∀ ω, (∑ i, x i * f i ω) ^ 2 = ∑ i, ∑ j, x i * x j * (f i ω * f j ω) := fun ω => by
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp_rw [e]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hint i j).const_mul _

end GMCExplicitDelta.Source
