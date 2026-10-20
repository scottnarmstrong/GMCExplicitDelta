module

public import SubdiffusiveProcess.CoarseGrainingVocab.Defect
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# History lane: elementary facts about `paperENNRealLpNorm`

Monotonicity, scalar multiplication, Minkowski for finite sums and the union bound for a finite
supremum, for the `ℝ≥0∞`-valued norm `paperENNRealLpNorm μ ξ X = (∫⁻ X^ξ)^{1/ξ}` (steps G5, G7).
-/

@[expose] public section

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

namespace GMCExplicitDelta.HistoryLane

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem lnorm_mono {ξ : ℝ} (hξ : 0 ≤ ξ) {X Y : Ω → ℝ≥0∞} (h : ∀ ω, X ω ≤ Y ω) :
    paperENNRealLpNorm μ ξ X ≤ paperENNRealLpNorm μ ξ Y := by
  unfold paperENNRealLpNorm
  exact ENNReal.rpow_le_rpow (lintegral_mono fun ω => ENNReal.rpow_le_rpow (h ω) hξ)
    (inv_nonneg.mpr hξ)

theorem lnorm_add_le {ξ : ℝ} (hξ : 1 ≤ ξ) {X Y : Ω → ℝ≥0∞} (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) :
    paperENNRealLpNorm μ ξ (fun ω => X ω + Y ω) ≤
      paperENNRealLpNorm μ ξ X + paperENNRealLpNorm μ ξ Y := by
  unfold paperENNRealLpNorm
  simpa only [one_div] using! ENNReal.lintegral_Lp_add_le (μ := μ) hX hY hξ

theorem lnorm_zero {ξ : ℝ} (hξ : 0 < ξ) :
    paperENNRealLpNorm μ ξ (fun _ : Ω => (0 : ℝ≥0∞)) = 0 := by
  unfold paperENNRealLpNorm
  simp [ENNReal.zero_rpow_of_pos hξ, hξ]

theorem lnorm_finset_sum_le {ι : Type*} {ξ : ℝ} (hξ : 1 ≤ ξ) (s : Finset ι) (X : ι → Ω → ℝ≥0∞)
    (hX : ∀ i ∈ s, AEMeasurable (X i) μ) :
    paperENNRealLpNorm μ ξ (fun ω => ∑ i ∈ s, X i ω) ≤ ∑ i ∈ s, paperENNRealLpNorm μ ξ (X i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [lnorm_zero (zero_lt_one.trans_le hξ)]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have hs : AEMeasurable (fun ω => ∑ i ∈ s, X i ω) μ :=
      
      Finset.aemeasurable_fun_sum s fun i hi => hX i (Finset.mem_insert_of_mem hi)
    refine (lnorm_add_le hξ (hX a (Finset.mem_insert_self _ _)) hs).trans ?_
    exact add_le_add le_rfl (ih fun i hi => hX i (Finset.mem_insert_of_mem hi))

theorem lnorm_const_mul {ξ : ℝ} (hξ : 0 < ξ) {c : ℝ≥0∞} (hc : c ≠ ∞) (X : Ω → ℝ≥0∞) :
    paperENNRealLpNorm μ ξ (fun ω => c * X ω) = c * paperENNRealLpNorm μ ξ X := by
  unfold paperENNRealLpNorm
  have hcp : c ^ ξ ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hξ.le hc
  have : (fun ω => (c * X ω) ^ ξ) = fun ω => c ^ ξ * X ω ^ ξ := by
    funext ω; exact ENNReal.mul_rpow_of_nonneg _ _ hξ.le
  rw [this, lintegral_const_mul' _ _ hcp, ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hξ.le),
    ← ENNReal.rpow_mul, mul_inv_cancel₀ hξ.ne', ENNReal.rpow_one]

theorem lintegral_rpow_le_of_lnorm_le {ξ : ℝ} (hξ : 0 < ξ) {X : Ω → ℝ≥0∞} {c : ℝ≥0∞}
    (h : paperENNRealLpNorm μ ξ X ≤ c) : ∫⁻ ω, X ω ^ ξ ∂μ ≤ c ^ ξ := by
  unfold paperENNRealLpNorm at h
  calc ∫⁻ ω, X ω ^ ξ ∂μ = ((∫⁻ ω, X ω ^ ξ ∂μ) ^ ξ⁻¹) ^ ξ := (ENNReal.rpow_inv_rpow hξ.ne' _).symm
    _ ≤ c ^ ξ := ENNReal.rpow_le_rpow h hξ.le

/-- Union bound: the `ξ`-norm of a finite supremum is at most `card^{1/ξ}` times the largest norm. -/
theorem lnorm_finset_sup_le {ι : Type*} {ξ : ℝ} (hξ : 0 < ξ) (s : Finset ι) (X : ι → Ω → ℝ≥0∞)
    (hX : ∀ i ∈ s, AEMeasurable (X i) μ) {c : ℝ≥0∞}
    (hc : ∀ i ∈ s, paperENNRealLpNorm μ ξ (X i) ≤ c) :
    paperENNRealLpNorm μ ξ (fun ω => s.sup fun i => X i ω) ≤ (s.card : ℝ≥0∞) ^ (1 / ξ) * c := by
  classical
  have hpt : ∀ ω, (s.sup fun i => X i ω) ^ ξ ≤ ∑ i ∈ s, X i ω ^ ξ := by
    intro ω
    rcases s.eq_empty_or_nonempty with rfl | hne
    · simp [ENNReal.zero_rpow_of_pos hξ]
    · obtain ⟨i, hi, hEq⟩ := Finset.exists_mem_eq_sup s hne fun i => X i ω
      rw [hEq]
      exact Finset.single_le_sum (f := fun i => X i ω ^ ξ) (fun _ _ => zero_le) hi
  have hint : ∫⁻ ω, (s.sup fun i => X i ω) ^ ξ ∂μ ≤ (s.card : ℝ≥0∞) * c ^ ξ := by
    calc ∫⁻ ω, (s.sup fun i => X i ω) ^ ξ ∂μ ≤ ∫⁻ ω, ∑ i ∈ s, X i ω ^ ξ ∂μ := lintegral_mono hpt
      _ = ∑ i ∈ s, ∫⁻ ω, X i ω ^ ξ ∂μ :=
          lintegral_finsetSum' _ fun i hi => (hX i hi).pow_const ξ
      _ ≤ ∑ i ∈ s, c ^ ξ := Finset.sum_le_sum fun i hi => lintegral_rpow_le_of_lnorm_le hξ (hc i hi)
      _ = (s.card : ℝ≥0∞) * c ^ ξ := by simp
  unfold paperENNRealLpNorm
  calc (∫⁻ ω, (s.sup fun i => X i ω) ^ ξ ∂μ) ^ ξ⁻¹ ≤ ((s.card : ℝ≥0∞) * c ^ ξ) ^ ξ⁻¹ :=
        ENNReal.rpow_le_rpow hint (inv_nonneg.mpr hξ.le)
    _ = (s.card : ℝ≥0∞) ^ (1 / ξ) * c := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hξ.le), ← ENNReal.rpow_mul,
          mul_inv_cancel₀ hξ.ne', ENNReal.rpow_one, one_div]

end GMCExplicitDelta.HistoryLane
