module

public import GMCExplicitDelta.Source.MomentBounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Probability.IdentDistrib

/-! # Symmetric exponential moments and the even moment series -/

@[expose] public section

namespace GMCExplicitDelta.Source

open MeasureTheory ProbabilityTheory Real

/-- The exact even factorial identity, including order zero. -/
theorem factorial_two_mul_eq (k : ℕ) :
    (2 * k).factorial = (2 * k - 1).doubleFactorial * (2 ^ k * k.factorial) := by
  rcases k with _ | k
  · norm_num
  · have heq : 2 * (k + 1) - 1 + 1 = 2 * (k + 1) := by omega
    have h := Nat.factorial_eq_mul_doubleFactorial (2 * (k + 1) - 1)
    rw [heq, Nat.doubleFactorial_two_mul] at h
    simpa only [mul_comm] using h

/-- The normalized Gaussian even moment is the coefficient of an exponential. -/
theorem doubleFactorial_div_even_factorial (a : ℝ) (k : ℕ) :
    ((2 * k - 1).doubleFactorial : ℝ) * a ^ k / (2 * k).factorial =
      (a / 2) ^ k / k.factorial := by
  rw [factorial_two_mul_eq]
  push_cast
  have hf : ((2 * k - 1).doubleFactorial : ℝ) ≠ 0 := by positivity
  rw [div_pow]
  field_simp

/-- Scaling a positive power from a fraction of the unit interval. -/
theorem gaussian_coefficient_scale {a s : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (hs4 : s ≤ 1 / 4)
    {k : ℕ} (hk : 1 ≤ k) : (a * s / 2) ^ k ≤ 4 * s * (a / 8) ^ k := by
  have hl0 : 0 ≤ 4 * s := mul_nonneg (by norm_num) hs
  have hl1 : 4 * s ≤ 1 := by linarith only [hs4]
  have hp : (4 * s) ^ (k - 1) ≤ 1 := pow_le_one₀ hl0 hl1
  have hpow : (4 * s) ^ k ≤ 4 * s := by
    calc
      _ = (4 * s) * (4 * s) ^ (k - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel hk]
      _ ≤ (4 * s) * 1 := mul_le_mul_of_nonneg_left hp hl0
      _ = _ := mul_one _
  calc
    _ = (4 * s) ^ k * (a / 8) ^ k := by rw [← mul_pow]; congr 1; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hpow (pow_nonneg (by positivity) _)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A symmetric law has equal positive and negative exponential moments. -/
theorem integral_exp_eq_neg_of_symm {X : Ω → ℝ}
    (hsym : IdentDistrib X (fun ω => -X ω) μ μ) :
    ∫ ω, exp (X ω) ∂μ = ∫ ω, exp (-X ω) ∂μ :=
  (hsym.comp measurable_exp).integral_eq

/-- Termwise integration of the even series under its integrable sum. -/
theorem hasSum_even_moments_cosh {X : Ω → ℝ}
    (hpow : ∀ k : ℕ, Integrable (fun ω => X ω ^ (2 * k)) μ)
    (hcosh : Integrable (fun ω => cosh (X ω)) μ) :
    HasSum (fun k => (∫ ω, X ω ^ (2 * k) ∂μ) / (2 * k).factorial)
      (∫ ω, cosh (X ω) ∂μ) := by
  let F : ℕ → Ω → ℝ := fun k ω => X ω ^ (2 * k) / (2 * k).factorial
  have hInt : ∀ k, Integrable (F k) μ := fun k => (hpow k).div_const _
  have hFn : ∀ k ω, 0 ≤ F k ω := by
    intro k ω
    dsimp [F]
    apply div_nonneg
    · rw [pow_mul]
      exact pow_nonneg (sq_nonneg _) _
    · positivity
  have hbound : ∀ k, ∀ᵐ ω ∂μ, ‖F k ω‖ ≤ F k ω := fun k =>
    Filter.Eventually.of_forall fun ω => (Real.norm_of_nonneg (hFn k ω)).le
  have hsum : ∀ ω, HasSum (fun k => F k ω) (cosh (X ω)) := fun ω => hasSum_cosh (X ω)
  have hIntT : Integrable (fun ω => ∑' k, F k ω) μ := by
    simpa only [F, ← cosh_eq_tsum] using hcosh
  have h := hasSum_integral_of_dominated_convergence F
    (fun k => (hInt k).aestronglyMeasurable) hbound
    (Filter.Eventually.of_forall fun ω => (hsum ω).summable) hIntT
    (Filter.Eventually.of_forall hsum)
  simpa only [F, integral_div] using h

/-- Integrating the even series computes the exponential moment of a symmetric law. -/
theorem hasSum_even_moments_exp {X : Ω → ℝ}
    (hsym : IdentDistrib X (fun ω => -X ω) μ μ)
    (hint : Integrable (fun ω => exp (X ω)) μ)
    (hpow : ∀ k : ℕ, Integrable (fun ω => X ω ^ (2 * k)) μ) :
    HasSum (fun k => (∫ ω, X ω ^ (2 * k) ∂μ) / (2 * k).factorial)
      (∫ ω, exp (X ω) ∂μ) := by
  have hneg : Integrable (fun ω => exp (-X ω)) μ := (hsym.comp measurable_exp).integrable_snd hint
  have hcosh : Integrable (fun ω => cosh (X ω)) μ := by
    simpa only [cosh_eq, Pi.add_apply] using (hint.add hneg).div_const 2
  have heq : ∫ ω, cosh (X ω) ∂μ = ∫ ω, exp (X ω) ∂μ := by
    simp_rw [cosh_eq]
    rw [integral_div, integral_add hint hneg, ← integral_exp_eq_neg_of_symm hsym]
    ring
  rw [← heq]
  exact hasSum_even_moments_cosh hpow hcosh

/-- Gaussian even moments imply exponential integrability; no exponential moment is assumed. -/
theorem integrable_exp_of_even_moments [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hsym : IdentDistrib X (fun ω => -X ω) μ μ)
    (hpow : ∀ k : ℕ, Integrable (fun ω => X ω ^ (2 * k)) μ)
    {a s : ℝ}
    (hmoment : ∀ k : ℕ, ∫ ω, X ω ^ (2 * k) ∂μ ≤
      ((2 * k - 1).doubleFactorial : ℝ) * (a * s) ^ k) :
    Integrable (fun ω => exp (X ω)) μ := by
  let F : ℕ → Ω → ℝ := fun k ω => X ω ^ (2 * k) / (2 * k).factorial
  have hFn : ∀ k ω, 0 ≤ F k ω := by
    intro k ω
    dsimp [F]
    apply div_nonneg
    · rw [pow_mul]
      exact pow_nonneg (sq_nonneg _) _
    · positivity
  have hInt : ∀ k, Integrable (F k) μ := fun k => (hpow k).div_const _
  have hGauss : Summable (fun k : ℕ => (a * s / 2) ^ k / k.factorial) := by
    have h := (NormedSpace.expSeries_div_hasSum_exp (a * s / 2)).summable
    exact h
  have hSum : Summable (fun k => ∫ ω, ‖F k ω‖ ∂μ) := by
    apply Summable.of_nonneg_of_le (fun k => integral_nonneg fun ω => norm_nonneg _) _ hGauss
    intro k
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (hFn k _)]
    dsimp [F]
    rw [integral_div]
    exact (div_le_div_of_nonneg_right (hmoment k) (by positivity)).trans_eq
      (doubleFactorial_div_even_factorial (a * s) k)
  have hseries := hasSum_integral_of_summable_integral_norm hInt hSum
  have hseries' : HasSum (fun k => ∫ ω, F k ω ∂μ) (∫ ω, cosh (X ω) ∂μ) := by
    simpa only [F, ← cosh_eq_tsum] using hseries
  have hone := hseries'.summable.le_tsum 0 (fun k _ => integral_nonneg (hFn k))
  rw [hseries'.tsum_eq] at hone
  norm_num [F] at hone
  have hC : Integrable (fun ω => cosh (X ω)) μ :=
    Integrable.of_integral_ne_zero (by linarith only [hone])
  apply (hC.const_mul 2).mono'
    (continuous_exp.comp_aestronglyMeasurable hsym.aestronglyMeasurable_fst)
  apply Filter.Eventually.of_forall
  intro ω
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), cosh_eq]
  have hpos := (exp_pos (-X ω)).le
  linarith only [hpos]

/-- S7 in terms of the variance scale `s`, before substituting `s = δ²`. -/
theorem integral_exp_le_of_even_moments [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hsym : IdentDistrib X (fun ω => -X ω) μ μ)
    (hpow : ∀ k : ℕ, Integrable (fun ω => X ω ^ (2 * k)) μ)
    {a u s : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (hs4 : s ≤ 1 / 4)
    (hmoment : ∀ k : ℕ, ∫ ω, X ω ^ (2 * k) ∂μ ≤
      ((2 * k - 1).doubleFactorial : ℝ) * (a * s) ^ k)
    (hvar : ∫ ω, X ω ^ 2 ∂μ ≤ u * s) :
    ∫ ω, exp (X ω) ∂μ ≤ 1 + s * (u / 2 + 4 * (exp (a / 8) - 1 - a / 8)) := by
  have hint := integrable_exp_of_even_moments hsym hpow hmoment
  let f : ℕ → ℝ := fun k => (∫ ω, X ω ^ (2 * k) ∂μ) / (2 * k).factorial
  let g : ℕ → ℝ := fun k => (a / 8) ^ k / k.factorial
  have hf : HasSum f (∫ ω, exp (X ω) ∂μ) := hasSum_even_moments_exp hsym hint hpow
  have hg : HasSum g (exp (a / 8)) := by
    simpa only [g, Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (a / 8)
  have hterm : ∀ k : ℕ, f k ≤ (a * s / 2) ^ k / k.factorial := by
    intro k
    exact (div_le_div_of_nonneg_right (hmoment k) (by positivity)).trans_eq
      (doubleFactorial_div_even_factorial (a * s) k)
  have htail : ∑' k, f (k + 2) ≤ (4 * s) * ∑' k, g (k + 2) := by
    rw [← tsum_mul_left]
    apply ((summable_nat_add_iff 2).mpr hf.summable).tsum_le_tsum
      (fun k => ?_) (((summable_nat_add_iff 2).mpr hg.summable).mul_left (4 * s))
    calc
      _ ≤ (a * s / 2) ^ (k + 2) / (k + 2).factorial := hterm _
      _ ≤ (4 * s * (a / 8) ^ (k + 2)) / (k + 2).factorial :=
        div_le_div_of_nonneg_right (gaussian_coefficient_scale ha hs hs4 (by omega)) (by positivity)
      _ = _ := by dsimp [g]; ring
  have hgtail : ∑' k, g (k + 2) = exp (a / 8) - 1 - a / 8 := by
    have h := hg.summable.sum_add_tsum_nat_add 2
    rw [hg.tsum_eq] at h
    norm_num [g, Finset.sum_range_succ] at h
    linarith only [h]
  have hftail : ∫ ω, exp (X ω) ∂μ = 1 + (∫ ω, X ω ^ 2 ∂μ) / 2 + ∑' k, f (k + 2) := by
    have h := hf.summable.sum_add_tsum_nat_add 2
    rw [hf.tsum_eq] at h
    norm_num [f, Finset.sum_range_succ] at h
    exact h.symm
  rw [hgtail] at htail
  rw [hftail]
  calc
    _ ≤ 1 + (u * s) / 2 + (4 * s) * (exp (a / 8) - 1 - a / 8) :=
      add_le_add (add_le_add_right (div_le_div_of_nonneg_right hvar (show (0 : ℝ) ≤ 2 by norm_num)) 1) htail
    _ = _ := by ring

/-- S7 with both signs and the disorder parameter in the normalization of the proof map. -/
theorem exp_moment_bounds_of_even_moments [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hsym : IdentDistrib X (fun ω => -X ω) μ μ)
    (hpow : ∀ k : ℕ, Integrable (fun ω => X ω ^ (2 * k)) μ)
    {a u δ : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (hmoment : ∀ k : ℕ, ∫ ω, X ω ^ (2 * k) ∂μ ≤
      ((2 * k - 1).doubleFactorial : ℝ) * (a * δ ^ 2) ^ k)
    (hvar : ∫ ω, X ω ^ 2 ∂μ ≤ u * δ ^ 2) :
    Integrable (fun ω => exp (X ω)) μ ∧ Integrable (fun ω => exp (-X ω)) μ ∧
    (∫ ω, exp (X ω) ∂μ ≤ 1 + δ ^ 2 * (u / 2 + 4 * (exp (a / 8) - 1 - a / 8))) ∧
    (∫ ω, exp (-X ω) ∂μ ≤ 1 + δ ^ 2 * (u / 2 + 4 * (exp (a / 8) - 1 - a / 8))) := by
  have hint := integrable_exp_of_even_moments hsym hpow hmoment
  have hneg := (hsym.comp measurable_exp).integrable_snd hint
  have hs4 : δ ^ 2 ≤ 1 / 4 := by
    calc
      _ ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ hδ.le hδhalf 2
      _ = _ := by norm_num
  have hb := integral_exp_le_of_even_moments hsym hpow ha (sq_nonneg _) hs4 hmoment hvar
  refine ⟨hint, hneg, hb, ?_⟩
  rw [← integral_exp_eq_neg_of_symm hsym]
  exact hb

end GMCExplicitDelta.Source
