module

public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Measure.Real

/-! # Integer moments from exponential tails -/

@[expose] public section

open MeasureTheory Real Set

namespace GMCExplicitDelta.Source

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Layer-cake moment estimate for a nonnegative variable with exponential tails. -/
theorem integral_pow_le_of_exponential_tail {X : Ω → ℝ}
    (hX : AEMeasurable X μ) (hpos : ∀ ω, 0 ≤ X ω) {n : ℕ} (hn : 0 < n)
    (hint : Integrable (fun ω => X ω ^ n) μ) {C : ℝ} (hC : 0 ≤ C)
    (htail : ∀ t : ℝ, 0 < t → μ.real {ω | t ≤ X ω} ≤ C * exp (-t)) :
    ∫ ω, X ω ^ n ∂μ ≤ C * Gamma (n + 1) := by
  let g : ℝ → ℝ := fun t => (n : ℝ) * t ^ (n - 1)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hprimitive : ∀ x : ℝ, ∫ t in 0..x, g t = x ^ n := by
    intro x
    dsimp [g]
    rw [intervalIntegral.integral_const_mul, integral_pow]
    have heq : n - 1 + 1 = n := Nat.sub_add_cancel hn
    rw [heq, zero_pow hn.ne']
    have hncast : ((n - 1 : ℕ) : ℝ) + 1 = n := by exact_mod_cast heq
    rw [sub_zero, hncast, mul_div_cancel₀ _ hn0]
  have hpow : ∀ t : ℝ, t ^ ((n : ℝ) - 1) = t ^ (n - 1) := by
    intro t
    rw [← Nat.cast_one, ← Nat.cast_sub (by omega : 1 ≤ n), rpow_natCast]
  have hgamma : IntegrableOn (fun t : ℝ => exp (-t) * t ^ (n - 1)) (Ioi 0) := by
    simpa only [hpow] using GammaIntegral_convergent
      (by exact_mod_cast hn : (0 : ℝ) < n)
  have hmajor : IntegrableOn (fun t : ℝ => C * exp (-t) * g t) (Ioi 0) := by
    have heq : (fun t : ℝ => C * exp (-t) * g t) =
        (fun t : ℝ => (C * n) * (exp (-t) * t ^ (n - 1))) := by
      funext t
      dsimp [g]
      ring
    rw [heq]
    exact hgamma.const_mul (C * n)
  have hmajorInt : ∫ t in Ioi (0 : ℝ), C * exp (-t) * g t = C * Gamma (n + 1) := by
    calc
      _ = (C * n) * ∫ t in Ioi (0 : ℝ), t ^ ((n : ℝ) - 1) * exp (-(1 * t)) := by
        rw [← integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t _
        dsimp [g]
        rw [hpow, one_mul]
        ring
      _ = (C * n) * Gamma n := by
        rw [integral_rpow_mul_exp_neg_mul_Ioi (by exact_mod_cast hn) zero_lt_one]
        simp only [div_one, one_rpow, one_mul]
      _ = _ := by rw [Gamma_add_one hn0]; ring
  have hlayer := lintegral_comp_eq_lintegral_meas_le_mul (g := g) μ
    (Filter.Eventually.of_forall hpos) hX
    (fun t _ => (continuous_const.mul (continuous_pow (n - 1))).intervalIntegrable 0 t)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (Nat.cast_nonneg n) (pow_nonneg ht.le _))
  simp_rw [hprimitive] at hlayer
  have hle : ENNReal.ofReal (∫ ω, X ω ^ n ∂μ) ≤
      ENNReal.ofReal (C * Gamma (n + 1)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun ω => pow_nonneg (hpos ω) n), hlayer,
      ← hmajorInt, ofReal_integral_eq_lintegral_ofReal hmajor]
    · apply setLIntegral_mono' measurableSet_Ioi
      intro t ht
      rw [← ofReal_measureReal, ← ENNReal.ofReal_mul measureReal_nonneg]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (htail t ht)
        (mul_nonneg (Nat.cast_nonneg n) (pow_nonneg ht.le _)))
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (mul_nonneg hC (exp_pos _).le)
        (mul_nonneg (Nat.cast_nonneg n) (pow_nonneg ht.le _))
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC
    (Gamma_nonneg_of_nonneg (by positivity)))).mp hle

/-- Gaussian-tail moment estimate, including the S8(b) case `n = 2*p`. -/
theorem integral_abs_pow_le_of_gaussian_tail {Z : Ω → ℝ}
    (hZ : AEMeasurable Z μ) {s C : ℝ} (hs : 0 < s) (hC : 0 ≤ C)
    {n : ℕ} (hn : 0 < n) (hint : Integrable (fun ω => |Z ω| ^ (2 * n)) μ)
    (htail : ∀ u : ℝ, 0 ≤ u → μ.real {ω | u ≤ |Z ω|} ≤ C * exp (-u ^ 2 / s ^ 2)) :
    ∫ ω, |Z ω| ^ (2 * n) ∂μ ≤ C * s ^ (2 * n) * Gamma (n + 1) := by
  let X : Ω → ℝ := fun ω => |Z ω| ^ 2 / s ^ 2
  have hpow : ∀ ω, X ω ^ n = |Z ω| ^ (2 * n) / s ^ (2 * n) := by
    intro ω
    simp only [X, div_pow, ← pow_mul]
  have hX : AEMeasurable X μ := (hZ.norm.pow_const 2).div_const _
  have hInt : Integrable (fun ω => X ω ^ n) μ := by
    simpa only [hpow] using hint.div_const (s ^ (2 * n))
  have htailX : ∀ t : ℝ, 0 < t → μ.real {ω | t ≤ X ω} ≤ C * exp (-t) := by
    intro t ht
    have hu : 0 ≤ s * sqrt t := mul_nonneg hs.le (sqrt_nonneg t)
    have heq : {ω | t ≤ X ω} = {ω | s * sqrt t ≤ |Z ω|} := by
      ext ω
      change (t ≤ |Z ω| ^ 2 / s ^ 2) ↔ (s * sqrt t ≤ |Z ω|)
      rw [le_div_iff₀ (sq_pos_of_pos hs), ← sq_le_sq₀ hu (abs_nonneg _),
        mul_pow, sq_sqrt ht.le]
      rw [mul_comm t]
    have hexp : -(s * sqrt t) ^ 2 / s ^ 2 = -t := by
      rw [mul_pow, sq_sqrt ht.le]
      field_simp
    rw [heq]
    simpa only [hexp] using htail (s * sqrt t) hu
  have h := integral_pow_le_of_exponential_tail hX (fun ω => by
    exact div_nonneg (sq_nonneg _) (sq_nonneg _)) hn hInt hC htailX
  simp only [hpow, integral_div] at h
  have hscale := (div_le_iff₀ (pow_pos hs (2 * n))).mp h
  calc
    _ ≤ (C * Gamma (n + 1)) * s ^ (2 * n) := hscale
    _ = _ := by ring

/-- The factor `P_p` in S8 and S10. -/
noncomputable def subgaussianMomentFactor (p : ℕ) : ℝ :=
  (2 * Gamma ((2 * p : ℕ) + 1)) ^ (1 / (2 * p : ℝ))

/-- Taking a positive integer root of a moment bound. -/
theorem moment_root_le {m s K : ℝ} (hm : 0 ≤ m) (hs : 0 ≤ s) (hK : 0 ≤ K)
    {n : ℕ} (hn : n ≠ 0) (h : m ≤ s ^ n * K) :
    m ^ (1 / (n : ℝ)) ≤ s * K ^ (1 / (n : ℝ)) := by
  calc
    _ ≤ (s ^ n * K) ^ (1 / (n : ℝ)) :=
      rpow_le_rpow hm h (by positivity)
    _ = (s ^ n) ^ (1 / (n : ℝ)) * K ^ (1 / (n : ℝ)) :=
      mul_rpow (pow_nonneg hs _) hK
    _ = _ := by rw [one_div, pow_rpow_inv_natCast hs hn]

/-- The factor appearing after taking the `4p`-th root. -/
theorem sqrt_subgaussianMomentFactor {p : ℕ} (hp : 0 < p) :
    sqrt (subgaussianMomentFactor p) =
      (2 * Gamma ((2 * p : ℕ) + 1)) ^ (1 / (4 * p : ℝ)) := by
  rw [subgaussianMomentFactor, sqrt_eq_rpow, ← rpow_mul (by positivity)]
  congr 1
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp [hp0]
  ring

/-- S8(b), with the probability-space `L^{4p}` norm written as its integral formula. -/
theorem moment_root_le_of_gaussian_tail {Z : Ω → ℝ}
    (hZ : AEMeasurable Z μ) {s : ℝ} (hs : 0 < s) {p : ℕ} (hp : 0 < p)
    (hint : Integrable (fun ω => |Z ω| ^ (4 * p)) μ)
    (htail : ∀ u : ℝ, 0 ≤ u → μ.real {ω | u ≤ |Z ω|} ≤ 2 * exp (-u ^ 2 / s ^ 2)) :
    (∫ ω, |Z ω| ^ (4 * p) ∂μ) ^ (1 / (4 * p : ℝ)) ≤
      s * sqrt (subgaussianMomentFactor p) := by
  have h := integral_abs_pow_le_of_gaussian_tail hZ hs (by norm_num : (0 : ℝ) ≤ 2)
    (by omega : 0 < 2 * p) (by simpa only [show 2 * (2 * p) = 4 * p by omega] using hint) htail
  rw [show 2 * (2 * p) = 4 * p by omega] at h
  rw [sqrt_subgaussianMomentFactor hp]
  have hnorm : (∫ ω, |Z ω| ^ (4 * p) ∂μ) ≤
      s ^ (4 * p) * (2 * Gamma ((2 * p : ℕ) + 1)) := by
    calc
      _ ≤ 2 * s ^ (4 * p) * Gamma ((2 * p : ℕ) + 1) := h
      _ = _ := by ring
  have hroot := moment_root_le (integral_nonneg fun ω => pow_nonneg (abs_nonneg (Z ω)) (4 * p))
    hs.le (by positivity : 0 ≤ 2 * Gamma ((2 * p : ℕ) + 1))
    (by omega : 4 * p ≠ 0) hnorm
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hroot

end GMCExplicitDelta.Source
