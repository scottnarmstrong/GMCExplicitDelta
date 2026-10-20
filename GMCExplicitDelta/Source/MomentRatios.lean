module

public import GMCExplicitDelta.Source.MomentBounds
public import GMCExplicitDelta.Contract.Row

/-! # Refined nonnegative moment ratios (step S4) -/

@[expose] public section

namespace GMCExplicitDelta.Source

open Real MeasureTheory

/-- The Gaussian comparator for the normalized square. -/
noncomputable def gaussianSquareMoment (k : ℕ) : ℝ :=
  ((2 * k - 1).doubleFactorial : ℝ) / 2 ^ k

/-- The ratio between the exponential-envelope maximizer and the Gaussian moment. -/
noncomputable def exponentialMomentRatio (k : ℕ) : ℝ :=
  ((k : ℝ) / exp 1) ^ k / gaussianSquareMoment k

/-- The logarithmic midpoint estimate makes the ratio decrease at each positive integer. -/
theorem exponentialMomentRatio_succ_le {k : ℕ} (hk : 1 ≤ k) :
    exponentialMomentRatio (k + 1) ≤ exponentialMomentRatio k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hb : 0 < gaussianSquareMoment k := by unfold gaussianSquareMoment; positivity
  have hb1 : 0 < gaussianSquareMoment (k + 1) := by unfold gaussianSquareMoment; positivity
  have hform : ∀ n : ℕ, 0 < n → exponentialMomentRatio n =
      exp ((n : ℝ) * log n - n - log (gaussianSquareMoment n)) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [exponentialMomentRatio, exp_sub, exp_sub, exp_log (by
      unfold gaussianSquareMoment; positivity), ← log_pow, exp_log (pow_pos hn0 _),
      div_pow, ← exp_nat_mul, mul_one]
  rw [hform (k + 1) (by omega), hform k (by omega)]
  apply exp_le_exp.mpr
  have hbrec : gaussianSquareMoment (k + 1) = gaussianSquareMoment k * (k + 1 / 2) :=
    doubleFactorial_ratio_succ k
  rw [hbrec, log_mul hb.ne' (by positivity)]
  have h := log_step_le hk
  push_cast
  linarith only [h]

/-- The largest ratio for orders at least three occurs at order three. -/
theorem exponentialMomentRatio_le_three {k : ℕ} (hk : 3 ≤ k) :
    exponentialMomentRatio k ≤ exponentialMomentRatio 3 := by
  induction k, hk using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih => exact (exponentialMomentRatio_succ_le (by omega)).trans ih

/-- The order-three envelope ratio in its closed form. -/
theorem exponentialMomentRatio_three_div :
    exponentialMomentRatio 3 / (1 - exp (-2)) = 72 / (5 * ((exp 1) ^ 3 - exp 1)) := by
  have he : 2 < exp 1 := by linarith only [exp_one_gt_d9]
  have hexp : exp (-2) = ((exp 1) ^ 2)⁻¹ := by
    rw [exp_neg, ← exp_nat_mul]
    norm_num
  have hratio : exponentialMomentRatio 3 = (3 / exp 1) ^ 3 / (15 / 8) := by
    norm_num [exponentialMomentRatio, gaussianSquareMoment, Nat.doubleFactorial]
  rw [hratio, hexp]
  generalize exp 1 = e at *
  have he0 : e ≠ 0 := by linarith only [he]
  have he2 : e ^ 2 - 1 ≠ 0 := by nlinarith only [he]
  have he3 : e ^ 3 - e ≠ 0 := by
    have hp : 0 < e * (e ^ 2 - 1) := mul_pos (by linarith only [he]) (by nlinarith only [he])
    nlinarith only [hp]
  field_simp [he0, he2, he3]
  ring

/-- Numerical obligation O.src.4, using the contract's exact rational constant. -/
theorem sqrt_three_ratio_le_ratioC2 :
    (4 / 3 : ℝ) * (sqrt 3 - 1) ≤ (GMCExplicitDelta.Contract.ratioC2 : ℝ) := by
  have hs : sqrt (3 : ℝ) ≤ 1.732050808 := by
    rw [sqrt_le_left (by norm_num)]
    norm_num
  norm_num [GMCExplicitDelta.Contract.ratioC2]
  linarith only [hs]

/-- Numerical obligation O.src.5, using nine-digit bounds on `e`. -/
theorem sqrt_three_ratio_le_ratioC3 :
    72 * (sqrt 3 - 1) / (5 * ((exp 1) ^ 3 - exp 1)) ≤
      (GMCExplicitDelta.Contract.ratioC3 : ℝ) := by
  have hs : sqrt (3 : ℝ) ≤ 1.732050808 := by
    rw [sqrt_le_left (by norm_num)]
    norm_num
  have harith : ∀ e z : ℝ, 2.7182818283 ≤ e → e ≤ 2.7182818286 → z ≤ 1.732050808 →
      0 < 5 * (e ^ 3 - e) ∧ 72 * (z - 1) ≤ (303489 / 500000 : ℝ) * (5 * (e ^ 3 - e)) := by
    intro e z hlo hhi hz
    have hc := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283) hlo 3
    constructor <;> nlinarith only [hc, hhi, hz]
  obtain ⟨hd, hb⟩ := harith (exp 1) (sqrt 3) exp_one_gt_d9.le exp_one_lt_d9.le hs
  rw [div_le_iff₀ hd]
  simpa only [GMCExplicitDelta.Contract.ratioC3, Rat.cast_div, Rat.cast_ofNat] using hb

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- S4: the fourth source moment is controlled by the excess exponential moment. -/
theorem integral_sq_le_sqrt_three_sub_one {Z : Ω → ℝ} (hZm : Measurable Z)
    (hZ0 : ∀ ω, 0 ≤ Z ω) (hint : Integrable (fun ω => exp (Z ω)) μ)
    (hbound : ∫ ω, exp (Z ω) ∂μ ≤ sqrt 3) :
    Integrable (fun ω => Z ω ^ 2) μ ∧ ∫ ω, Z ω ^ 2 ∂μ ≤ sqrt 3 - 1 := by
  obtain ⟨hi, hb⟩ := integrable_pow_of_le hZm hint (k := 2) (C := 1)
    (fun z hz => by simpa only [one_mul] using exp_sub_one_sub_sq_nonneg hz) hZ0
  refine ⟨hi, hb.trans ?_⟩
  simpa only [one_mul] using sub_le_sub_right hbound 1

/-- S4: the exact exponential-envelope moment bound, before comparison to Gaussian moments. -/
theorem integral_pow_le_sqrt_three_envelope {Z : Ω → ℝ} (hZm : Measurable Z)
    (hZ0 : ∀ ω, 0 ≤ Z ω) (hint : Integrable (fun ω => exp (Z ω)) μ)
    (hbound : ∫ ω, exp (Z ω) ∂μ ≤ sqrt 3) {k : ℕ} (hk : 3 ≤ k) :
    Integrable (fun ω => Z ω ^ k) μ ∧
      ∫ ω, Z ω ^ k ∂μ ≤ (sqrt 3 - 1) * ((k : ℝ) / exp 1) ^ k /
        (1 - exp (-((k : ℝ) - 1))) := by
  obtain ⟨hi, hb⟩ := integrable_pow_of_le hZm hint
    (fun z hz => pow_le_const_mul_exp_sub_one hk hz) hZ0
  refine ⟨hi, hb.trans ?_⟩
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hden : 0 < 1 - exp (-((k : ℝ) - 1)) := by
    exact sub_pos.mpr (exp_lt_one_iff.mpr (by linarith only [hkR]))
  calc
    _ ≤ (((k : ℝ) / exp 1) ^ k / (1 - exp (-((k : ℝ) - 1)))) * (sqrt 3 - 1) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_right hbound 1) (by positivity)
    _ = _ := by ring

/-- S4: uniform ratio bound for every order at least three. -/
theorem integral_pow_div_gaussian_le {Z : Ω → ℝ} (hZm : Measurable Z)
    (hZ0 : ∀ ω, 0 ≤ Z ω) (hint : Integrable (fun ω => exp (Z ω)) μ)
    (hbound : ∫ ω, exp (Z ω) ∂μ ≤ sqrt 3) {k : ℕ} (hk : 3 ≤ k) :
    Integrable (fun ω => Z ω ^ k) μ ∧
      (∫ ω, Z ω ^ k ∂μ) / gaussianSquareMoment k ≤
        72 * (sqrt 3 - 1) / (5 * ((exp 1) ^ 3 - exp 1)) := by
  obtain ⟨hi, hb⟩ := integral_pow_le_sqrt_three_envelope hZm hZ0 hint hbound hk
  have hg : 0 < gaussianSquareMoment k := by unfold gaussianSquareMoment; positivity
  have hs : 0 ≤ sqrt (3 : ℝ) - 1 := by
    have h := le_sqrt_of_sq_le (by norm_num : (1 : ℝ) ^ 2 ≤ 3)
    linarith only [h]
  have hd3 : 0 < 1 - exp (-2) := sub_pos.mpr (exp_lt_one_iff.mpr (by norm_num))
  have hkd : 1 - exp (-2) ≤ 1 - exp (-((k : ℝ) - 1)) := by
    have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
    exact sub_le_sub_left (exp_le_exp.mpr (by linarith only [hkR])) 1
  have hratio := exponentialMomentRatio_le_three hk
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ((sqrt 3 - 1) * ((k : ℝ) / exp 1) ^ k /
        (1 - exp (-((k : ℝ) - 1)))) / gaussianSquareMoment k :=
      div_le_div_of_nonneg_right hb hg.le
    _ = (sqrt 3 - 1) * exponentialMomentRatio k / (1 - exp (-((k : ℝ) - 1))) := by
      unfold exponentialMomentRatio
      ring
    _ ≤ (sqrt 3 - 1) * exponentialMomentRatio k / (1 - exp (-2)) :=
      div_le_div_of_nonneg_left (mul_nonneg hs (by unfold exponentialMomentRatio; positivity)) hd3 hkd
    _ ≤ (sqrt 3 - 1) * exponentialMomentRatio 3 / (1 - exp (-2)) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hratio hs) hd3.le
    _ = _ := by rw [mul_div_assoc, exponentialMomentRatio_three_div]; ring

/-- S4's fourth-moment comparison with the contract constant. -/
theorem integral_sq_le_ratioC2 {Z : Ω → ℝ} (hZm : Measurable Z)
    (hZ0 : ∀ ω, 0 ≤ Z ω) (hint : Integrable (fun ω => exp (Z ω)) μ)
    (hbound : ∫ ω, exp (Z ω) ∂μ ≤ sqrt 3) :
    Integrable (fun ω => Z ω ^ 2) μ ∧
      ∫ ω, Z ω ^ 2 ∂μ ≤ (GMCExplicitDelta.Contract.ratioC2 : ℝ) * gaussianSquareMoment 2 := by
  obtain ⟨hi, hb⟩ := integral_sq_le_sqrt_three_sub_one hZm hZ0 hint hbound
  refine ⟨hi, hb.trans ?_⟩
  norm_num [gaussianSquareMoment, Nat.doubleFactorial]
  linarith only [sqrt_three_ratio_le_ratioC2]

/-- S4's higher-moment comparison with the contract constant. -/
theorem integral_pow_le_ratioC3 {Z : Ω → ℝ} (hZm : Measurable Z)
    (hZ0 : ∀ ω, 0 ≤ Z ω) (hint : Integrable (fun ω => exp (Z ω)) μ)
    (hbound : ∫ ω, exp (Z ω) ∂μ ≤ sqrt 3) {k : ℕ} (hk : 3 ≤ k) :
    Integrable (fun ω => Z ω ^ k) μ ∧
      ∫ ω, Z ω ^ k ∂μ ≤ (GMCExplicitDelta.Contract.ratioC3 : ℝ) * gaussianSquareMoment k := by
  obtain ⟨hi, hb⟩ := integral_pow_div_gaussian_le hZm hZ0 hint hbound hk
  have hg : 0 < gaussianSquareMoment k := by unfold gaussianSquareMoment; positivity
  exact ⟨hi, (div_le_iff₀ hg).mp (hb.trans sqrt_three_ratio_le_ratioC3)⟩

end GMCExplicitDelta.Source
