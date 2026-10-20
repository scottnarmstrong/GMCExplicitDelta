module

public import GMCExplicitDelta.Proofs.FineSensitivity.Holder
public import SubdiffusiveProcess.CoarseGrainingVocab.PrefixSuffixMeasurability

/-! # Weighted Hölder for the conditional G3 remainder estimate -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace GMCExplicitDelta.Assembly

/-- The weighted power inequality used before prefix/suffix factorization. -/
theorem fine_weighted_integral_pow_le {E : Type*} [MeasurableSpace E] (ν : Measure E)
    {X Y : E → ℝ≥0∞} (hX : AEMeasurable X ν) (hY : AEMeasurable Y ν) :
    (∫⁻ x, X x * Y x ∂ν) ^ (32 : ℝ) ≤
      (∫⁻ x, X x ∂ν) ^ (31 : ℝ) * ∫⁻ x, X x * Y x ^ (32 : ℝ) ∂ν := by
  have hc : (32 / 31 : ℝ).HolderConjugate 32 := by
    constructor <;> norm_num
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hc
    (hX.pow_const (31 / 32 : ℝ)) ((hX.pow_const (1 / 32 : ℝ)).mul hY)
  simp only [Pi.mul_apply] at h
  have hL : (∫⁻ x, X x ^ (31 / 32 : ℝ) * (X x ^ (1 / 32 : ℝ) * Y x) ∂ν) =
      ∫⁻ x, X x * Y x ∂ν := by
    apply lintegral_congr
    intro x
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have h := hL.symm.trans_le h
  simp only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 32),
    ← ENNReal.rpow_mul] at h
  norm_num only [show (31 / 32 : ℝ) * (32 / 31) = 1 by norm_num,
    show (1 / 32 : ℝ) * 32 = 1 by norm_num, ENNReal.rpow_one] at h
  have hroot := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 32)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)] at hroot
  simp only [← ENNReal.rpow_mul] at hroot
  norm_num only [show (1 / (32 / 31) : ℝ) * 32 = 31 by norm_num,
    show (1 / 32 : ℝ) * 32 = 1 by norm_num, ENNReal.rpow_one] at hroot
  exact hroot

/-- The conditional weighted moment estimate, proved by weighted Hölder, Tonelli,
and independence of prefix and suffix sigma-fields. -/
theorem fine_independent_weighted_moment_le {Ω E : Type*}
    (m₁ m₂ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (ν : Measure E) [SFinite μ] [SFinite ν]
    (hm₁ : m₁ ≤ mΩ) (hm₂ : m₂ ≤ mΩ) (hind : ProbabilityTheory.Indep m₁ m₂ μ)
    {X Y : Ω → E → ℝ≥0∞} (hXa : Measurable (Function.uncurry X))
    (hYa : Measurable (Function.uncurry Y))
    (hX : ∀ x, @Measurable Ω ℝ≥0∞ m₁ inferInstance (fun ω => X ω x))
    (hY : ∀ x, @Measurable Ω ℝ≥0∞ m₂ inferInstance (fun ω => Y ω x))
    (hI : @Measurable Ω ℝ≥0∞ m₁ inferInstance (fun ω => ∫⁻ x, X ω x ∂ν))
    {C : ℝ≥0∞} (hC : ∀ x, ∫⁻ ω, Y ω x ^ (32 : ℝ) ∂μ ≤ C) :
    ∫⁻ ω, (∫⁻ x, X ω x * Y ω x ∂ν) ^ (32 : ℝ) ∂μ ≤
      C * ∫⁻ ω, (∫⁻ x, X ω x ∂ν) ^ (32 : ℝ) ∂μ := by
  let I := fun ω => ∫⁻ x, X ω x ∂ν
  have hIa : Measurable I := hI.mono hm₁ le_rfl
  have hW : Measurable (fun p : Ω × E => I p.1 ^ (31 : ℝ) * X p.1 p.2) :=
    ((hIa.comp measurable_fst).pow_const 31).mul hXa
  have hWY : Measurable (fun p : Ω × E =>
      I p.1 ^ (31 : ℝ) * X p.1 p.2 * Y p.1 p.2 ^ (32 : ℝ)) := hW.mul (hYa.pow_const 32)
  have hfactor (x : E) : (∫⁻ ω, I ω ^ (31 : ℝ) * X ω x * Y ω x ^ (32 : ℝ) ∂μ) =
      (∫⁻ ω, I ω ^ (31 : ℝ) * X ω x ∂μ) * ∫⁻ ω, Y ω x ^ (32 : ℝ) ∂μ :=
    ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
      hm₁ hm₂ hind ((hI.pow_const 31).mul (hX x)) ((hY x).pow_const 32)
  calc
    _ ≤ ∫⁻ ω, I ω ^ (31 : ℝ) * ∫⁻ x, X ω x * Y ω x ^ (32 : ℝ) ∂ν ∂μ :=
      lintegral_mono fun ω => fine_weighted_integral_pow_le ν
        hXa.of_uncurry_left.aemeasurable hYa.of_uncurry_left.aemeasurable
    _ = ∫⁻ ω, ∫⁻ x, I ω ^ (31 : ℝ) * X ω x * Y ω x ^ (32 : ℝ) ∂ν ∂μ := by
      apply lintegral_congr
      intro ω
      have hm : Measurable (fun x => X ω x * Y ω x ^ (32 : ℝ)) :=
        hXa.of_uncurry_left.mul (hYa.of_uncurry_left.pow_const (32 : ℝ))
      calc
        _ = ∫⁻ x, I ω ^ (31 : ℝ) * (X ω x * Y ω x ^ (32 : ℝ)) ∂ν :=
          (lintegral_const_mul _ hm).symm
        _ = _ := lintegral_congr fun x => (mul_assoc _ _ _).symm
    _ = ∫⁻ x, ∫⁻ ω, I ω ^ (31 : ℝ) * X ω x * Y ω x ^ (32 : ℝ) ∂μ ∂ν :=
      lintegral_lintegral_swap hWY.aemeasurable
    _ ≤ ∫⁻ x, (∫⁻ ω, I ω ^ (31 : ℝ) * X ω x ∂μ) * C ∂ν := by
      apply lintegral_mono
      intro x
      change (∫⁻ ω, I ω ^ (31 : ℝ) * X ω x * Y ω x ^ (32 : ℝ) ∂μ) ≤
        (∫⁻ ω, I ω ^ (31 : ℝ) * X ω x ∂μ) * C
      rw [hfactor x]
      exact mul_le_mul' le_rfl (hC x)
    _ = C * ∫⁻ x, ∫⁻ ω, I ω ^ (31 : ℝ) * X ω x ∂μ ∂ν := by
      rw [lintegral_mul_const _ hW.lintegral_prod_left]
      exact mul_comm _ _
    _ = C * ∫⁻ ω, ∫⁻ x, I ω ^ (31 : ℝ) * X ω x ∂ν ∂μ := by
      rw [← lintegral_lintegral_swap hW.aemeasurable]
    _ = _ := by
      congr 1
      apply lintegral_congr
      intro ω
      rw [lintegral_const_mul _ hXa.of_uncurry_left]
      change I ω ^ (31 : ℝ) * I ω = I ω ^ (32 : ℝ)
      conv_lhs => rhs; rw [← ENNReal.rpow_one (I ω)]
      rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
      norm_num

end GMCExplicitDelta.Assembly
