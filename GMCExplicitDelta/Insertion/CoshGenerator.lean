module

public import GMCExplicitDelta.Insertion.CoshGeneratorTaylor
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# Comparison with the generator series, Gaussian case and proportional scaling

(G3) `integral_coshPow_le`, (G4) `gaussian_coeff_eq` / `integral_coshPow_le_gaussian`,
(G5) `gaussianMajorant_scale_le`.  Notation: `L = coshL`, `e_p = X^p`, `A = cosh θ - 1`.
-/

@[expose] public section

open Polynomial MeasureTheory
open scoped Nat

namespace GMCExplicitDelta.Insertion

theorem continuous_coshPow (p : ℕ) : Continuous (coshPow p) := by
  unfold coshPow; fun_prop

theorem coshPow_le_exp (p : ℕ) {u : ℝ} (hu : 0 ≤ u) : coshPow p u ≤ Real.exp (p * u) := by
  have h1 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h2 : 1 ≤ Real.exp u := Real.one_le_exp hu
  have h3 : 0 ≤ Real.cosh u - 1 := by linarith [Real.one_le_cosh u]
  have h4 : Real.cosh u - 1 ≤ Real.exp u := by rw [Real.cosh_eq]; linarith
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ h3 h4 p

theorem coshPow_nonneg (p : ℕ) {u : ℝ} : 0 ≤ coshPow p u :=
  pow_nonneg (by linarith [Real.one_le_cosh u]) p

/-- Symmetry of the law gives vanishing odd moments. -/
theorem integral_pow_odd_eq_zero {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Y : Ω → ℝ}
    (hY : Measurable Y) (hsym : μ.map Y = μ.map (fun ω => -Y ω)) (n : ℕ) :
    ∫ ω, Y ω ^ (2 * n + 1) ∂μ = 0 := by
  have h1 : ∫ ω, Y ω ^ (2 * n + 1) ∂μ = ∫ x, x ^ (2 * n + 1) ∂(μ.map Y) :=
    (integral_map hY.aemeasurable (continuous_pow _).aestronglyMeasurable).symm
  have h2 : ∫ x, x ^ (2 * n + 1) ∂(μ.map Y) = ∫ ω, (-Y ω) ^ (2 * n + 1) ∂μ := by
    rw [hsym]
    exact integral_map (hY.neg.aemeasurable) (continuous_pow _).aestronglyMeasurable
  have h3 : ∫ ω, (-Y ω) ^ (2 * n + 1) ∂μ = - ∫ ω, Y ω ^ (2 * n + 1) ∂μ := by
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp [Odd.neg_pow (odd_two_mul_add_one n)]
  linarith

/-- Taylor coefficients of `(cosh t - 1)^p` at `θ`. -/
noncomputable def coshTaylorCoeff (p : ℕ) (θ : ℝ) (j : ℕ) : ℝ :=
  (j ! : ℝ)⁻¹ * iteratedDeriv j (coshPow p) θ

theorem coshTaylorCoeff_nonneg (p : ℕ) {θ : ℝ} (hθ : 0 ≤ θ) (j : ℕ) :
    0 ≤ coshTaylorCoeff p θ j :=
  mul_nonneg (by positivity) (iteratedDeriv_coshPow_nonneg p j hθ)

theorem hasSum_coshTaylor (p : ℕ) (θ x : ℝ) :
    HasSum (fun j => coshTaylorCoeff p θ j * x ^ j) (coshPow p (θ + x)) :=
  hasSum_taylor_coshPow p θ x

theorem coshTaylorCoeff_even (p n : ℕ) (θ : ℝ) :
    coshTaylorCoeff p θ (2 * n) = 2 ^ n / ((2 * n)! : ℝ) *
      ((coshL ^ n) (X ^ p : ℝ[X])).eval (Real.cosh θ - 1) := by
  unfold coshTaylorCoeff
  rw [iteratedDeriv_even_eq, coshM_pow_eq]
  simp only [LinearMap.smul_apply, Polynomial.eval_smul, smul_eq_mul]
  field_simp

/-- Interchange of the Taylor expansion and the expectation. -/
theorem hasSum_integral_coshPow {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Y : Ω → ℝ}
    (hY : Measurable Y) (p : ℕ)
    (hexp : Integrable (fun ω => Real.exp (p * |Y ω|)) μ) {θ : ℝ} (hθ : 0 ≤ θ) :
    HasSum (fun j => ∫ ω, coshTaylorCoeff p θ j * Y ω ^ j ∂μ)
      (∫ ω, coshPow p (θ + Y ω) ∂μ) := by
  have hc := coshTaylorCoeff_nonneg p hθ
  have hBmeas : Measurable fun ω => coshPow p (θ + |Y ω|) :=
    (continuous_coshPow p).measurable.comp
      (measurable_const.add (continuous_abs.measurable.comp hY))
  have hBint : Integrable (fun ω => coshPow p (θ + |Y ω|)) μ := by
    refine ((hexp.const_mul (Real.exp (p * θ))).mono' hBmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_))
    rw [Real.norm_of_nonneg (coshPow_nonneg p), ← Real.exp_add]
    refine (coshPow_le_exp p (by positivity)).trans (le_of_eq ?_)
    congr 1; ring
  have hnorm : ∀ j ω, ‖coshTaylorCoeff p θ j * Y ω ^ j‖ = coshTaylorCoeff p θ j * |Y ω| ^ j :=
    fun j ω => by
      simp only [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_nonneg (hc j)]
  have hle : ∀ j ω, coshTaylorCoeff p θ j * |Y ω| ^ j ≤ coshPow p (θ + |Y ω|) := fun j ω =>
    le_hasSum (hasSum_coshTaylor p θ |Y ω|) j fun i _ =>
      mul_nonneg (hc i) (pow_nonneg (abs_nonneg _) i)
  have hTint : ∀ j, Integrable (fun ω => coshTaylorCoeff p θ j * Y ω ^ j) μ := fun j => by
    refine (hBint.mono' ?_ (Filter.Eventually.of_forall fun ω => ?_))
    · exact ((hY.pow_const j).const_mul _).aestronglyMeasurable
    · rw [hnorm]; exact hle j ω
  have hTnormInt : ∀ j, Integrable (fun ω => ‖coshTaylorCoeff p θ j * Y ω ^ j‖) μ :=
    fun j => (hTint j).norm
  have hsumnorm : Summable fun j => ∫ ω, ‖coshTaylorCoeff p θ j * Y ω ^ j‖ ∂μ := by
    refine summable_of_sum_range_le (c := ∫ ω, coshPow p (θ + |Y ω|) ∂μ)
      (fun j => integral_nonneg fun ω => norm_nonneg _) ?_
    intro N
    rw [← integral_finsetSum _ fun j _ => hTnormInt j]
    refine integral_mono (integrable_finsetSum _ fun j _ => hTnormInt j) hBint fun ω => ?_
    simp only [hnorm]
    exact sum_le_hasSum (Finset.range N)
      (fun i _ => mul_nonneg (hc i) (pow_nonneg (abs_nonneg _) i))
      (hasSum_coshTaylor p θ |Y ω|)
  have hHS := hasSum_integral_of_summable_integral_norm hTint hsumnorm
  have hpt : ∀ ω, ∑' j, coshTaylorCoeff p θ j * Y ω ^ j = coshPow p (θ + Y ω) := fun ω =>
    (hasSum_coshTaylor p θ (Y ω)).tsum_eq
  simp only [hpt] at hHS
  exact hHS

/-- **(G3)**. For symmetric `Y` with `E exp(p|Y|) < ∞`, `E Y^(2n) ≤ m n`, and `θ ≥ 0`, with
`A = cosh θ - 1`:
`E (cosh(θ+Y) - 1)^p ≤ Σ_n (m_n 2^n/(2n)!) (L^n e_p)(A)`
(the right-hand series is assumed summable). -/
theorem integral_coshPow_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Y : Ω → ℝ}
    (hY : Measurable Y) (hsym : μ.map Y = μ.map (fun ω => -Y ω)) (p : ℕ)
    (hexp : Integrable (fun ω => Real.exp (p * |Y ω|)) μ) (m : ℕ → ℝ)
    (hm : ∀ n, ∫ ω, Y ω ^ (2 * n) ∂μ ≤ m n) {θ : ℝ} (hθ : 0 ≤ θ)
    (hsum : Summable fun n : ℕ =>
      (m n * 2 ^ n / ((2 * n)! : ℝ)) * ((coshL ^ n) (X ^ p : ℝ[X])).eval (Real.cosh θ - 1)) :
    ∫ ω, (Real.cosh (θ + Y ω) - 1) ^ p ∂μ ≤
      ∑' n : ℕ, (m n * 2 ^ n / ((2 * n)! : ℝ)) *
        ((coshL ^ n) (X ^ p : ℝ[X])).eval (Real.cosh θ - 1) := by
  have hHS := hasSum_integral_coshPow hY p hexp hθ
  have hTj : ∀ j, ∫ ω, coshTaylorCoeff p θ j * Y ω ^ j ∂μ =
      coshTaylorCoeff p θ j * ∫ ω, Y ω ^ j ∂μ := fun j => integral_const_mul _ _
  have hodd : ∀ n, ∫ ω, coshTaylorCoeff p θ (2 * n + 1) * Y ω ^ (2 * n + 1) ∂μ = 0 :=
    fun n => by rw [hTj, integral_pow_odd_eq_zero hY hsym, mul_zero]
  have hinj1 : Function.Injective fun k : ℕ => 2 * k := fun a b h => by simp at h; omega
  have hinj2 : Function.Injective fun k : ℕ => 2 * k + 1 := fun a b h => by simp at h; omega
  have hs1 : Summable fun k : ℕ => ∫ ω, coshTaylorCoeff p θ (2 * k) * Y ω ^ (2 * k) ∂μ :=
    hHS.summable.comp_injective hinj1
  have hs2 : Summable fun k : ℕ => ∫ ω, coshTaylorCoeff p θ (2 * k + 1) * Y ω ^ (2 * k + 1) ∂μ :=
    hHS.summable.comp_injective hinj2
  have hev := tsum_even_add_odd (f := fun j : ℕ => ∫ ω, coshTaylorCoeff p θ j * Y ω ^ j ∂μ)
    hs1 hs2
  have hev' : ∑' n, ∫ ω, coshTaylorCoeff p θ (2 * n) * Y ω ^ (2 * n) ∂μ =
      ∫ ω, coshPow p (θ + Y ω) ∂μ := by
    rw [← hHS.tsum_eq, ← hev]
    simp only [hodd, tsum_zero, add_zero]
  show ∫ ω, coshPow p (θ + Y ω) ∂μ ≤ _
  rw [← hev']
  refine Summable.tsum_le_tsum (fun n => ?_) hs1 hsum
  rw [hTj]
  have hcn : 0 ≤ coshTaylorCoeff p θ (2 * n) := coshTaylorCoeff_nonneg p hθ _
  calc coshTaylorCoeff p θ (2 * n) * ∫ ω, Y ω ^ (2 * n) ∂μ
      ≤ coshTaylorCoeff p θ (2 * n) * m n := mul_le_mul_of_nonneg_left (hm n) hcn
    _ = _ := by rw [coshTaylorCoeff_even]; ring

/-! ### (G4) Gaussian case -/

/-- `(2n-1)!! 2^n/(2n)! = 1/n!`. -/
theorem gaussian_coeff_eq (n : ℕ) (v : ℝ) :
    (((2 * n - 1)‼ : ℕ) : ℝ) * v ^ n * 2 ^ n / ((2 * n)! : ℝ) = v ^ n / (n ! : ℝ) := by
  rcases n with _ | k
  · simp
  · have h1 : (2 * (k + 1))! = (2 * (k + 1))‼ * (2 * k + 1)‼ := by
      have := Nat.factorial_eq_mul_doubleFactorial (2 * k + 1)
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring]; exact this
    have h2 : (2 * (k + 1))‼ = 2 ^ (k + 1) * (k + 1)! := Nat.doubleFactorial_two_mul _
    have h3 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    rw [h3, h1, h2]
    have : ((2 * k + 1)‼ : ℝ) ≠ 0 := by exact_mod_cast (Nat.doubleFactorial_pos _).ne'
    push_cast
    field_simp

/-- The Gaussian majorant `(exp(vL) e_p)(A) = Σ_n (v^n/n!) (L^n e_p)(A)`. -/
noncomputable def gaussianMajorant (p : ℕ) (A v : ℝ) : ℝ :=
  ∑' n : ℕ, v ^ n / (n ! : ℝ) * ((coshL ^ n) (X ^ p : ℝ[X])).eval A

/-- **(G4)**: Gaussian moment bounds `E Y^(2n) ≤ (2n-1)!! v^n` give the majorant
`(exp(vL) e_p)(A)`. -/
theorem integral_coshPow_le_gaussian {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Y : Ω → ℝ} (hY : Measurable Y) (hsym : μ.map Y = μ.map (fun ω => -Y ω)) (p : ℕ)
    (hexp : Integrable (fun ω => Real.exp (p * |Y ω|)) μ) (v : ℝ)
    (hm : ∀ n, ∫ ω, Y ω ^ (2 * n) ∂μ ≤ (((2 * n - 1)‼ : ℕ) : ℝ) * v ^ n) {θ : ℝ} (hθ : 0 ≤ θ)
    (hsum : Summable fun n : ℕ =>
      v ^ n / (n ! : ℝ) * ((coshL ^ n) (X ^ p : ℝ[X])).eval (Real.cosh θ - 1)) :
    ∫ ω, (Real.cosh (θ + Y ω) - 1) ^ p ∂μ ≤ gaussianMajorant p (Real.cosh θ - 1) v := by
  have h := integral_coshPow_le hY hsym p hexp
    (fun n => (((2 * n - 1)‼ : ℕ) : ℝ) * v ^ n) hm hθ (by
      simpa only [gaussian_coeff_eq] using hsum)
  simpa only [gaussian_coeff_eq, gaussianMajorant] using h

/-! ### (G5) Proportional scaling -/

theorem coshL_pow_eval_nonneg (n p : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    0 ≤ ((coshL ^ n) (X ^ p : ℝ[X])).eval A :=
  eval_nonneg_of_coeff_nonneg (coshL_pow_nonneg n p) hA

/-- Termwise scaling: if every monomial `A^k v^n` has `k + n ≥ p` (which is (G2)'s degree
statement), then `λ^n (L^n e_p)(λA) ≤ λ^p (L^n e_p)(A)` for `0 ≤ λ ≤ 1`. -/
theorem coshL_pow_eval_scale_le (n p : ℕ) {A l : ℝ} (hA : 0 ≤ A) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    l ^ n * ((coshL ^ n) (X ^ p : ℝ[X])).eval (l * A) ≤
      l ^ p * ((coshL ^ n) (X ^ p : ℝ[X])).eval A := by
  set q := (coshL ^ n) (X ^ p : ℝ[X])
  rw [eval_eq_sum_range, eval_eq_sum_range, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases hk : k + n < p
  · rw [coshL_pow_coeff_eq_zero n p k hk]; simp
  · have h1 : l ^ (n + k) ≤ l ^ p := pow_le_pow_of_le_one hl0 hl1 (by omega)
    have h2 : 0 ≤ q.coeff k := coshL_pow_nonneg n p k
    have h3 : 0 ≤ A ^ k := pow_nonneg hA k
    calc l ^ n * (q.coeff k * (l * A) ^ k) = q.coeff k * A ^ k * l ^ (n + k) := by
          rw [mul_pow, pow_add]; ring
      _ ≤ q.coeff k * A ^ k * l ^ p := mul_le_mul_of_nonneg_left h1 (mul_nonneg h2 h3)
      _ = _ := by ring

/-- **(G5)**: `S(λA, λv) ≤ λ^p S(A, v)` for the Gaussian majorant, `0 ≤ λ ≤ 1`, `A, v ≥ 0`. -/
theorem gaussianMajorant_scale_le (p : ℕ) {A v l : ℝ} (hA : 0 ≤ A) (hv : 0 ≤ v) (hl0 : 0 ≤ l)
    (hl1 : l ≤ 1)
    (hsum : Summable fun n : ℕ =>
      v ^ n / (n ! : ℝ) * ((coshL ^ n) (X ^ p : ℝ[X])).eval A) :
    gaussianMajorant p (l * A) (l * v) ≤ l ^ p * gaussianMajorant p A v := by
  have hterm : ∀ n : ℕ, (l * v) ^ n / (n ! : ℝ) * ((coshL ^ n) (X ^ p : ℝ[X])).eval (l * A) ≤
      l ^ p * (v ^ n / (n ! : ℝ) * ((coshL ^ n) (X ^ p : ℝ[X])).eval A) := fun n => by
    have h := coshL_pow_eval_scale_le n p hA hl0 hl1
    have hv' : 0 ≤ v ^ n / (n ! : ℝ) := by positivity
    calc (l * v) ^ n / (n ! : ℝ) * ((coshL ^ n) (X ^ p : ℝ[X])).eval (l * A)
        = v ^ n / (n ! : ℝ) * (l ^ n * ((coshL ^ n) (X ^ p : ℝ[X])).eval (l * A)) := by
          rw [mul_pow]; ring
      _ ≤ v ^ n / (n ! : ℝ) * (l ^ p * ((coshL ^ n) (X ^ p : ℝ[X])).eval A) :=
          mul_le_mul_of_nonneg_left h hv'
      _ = _ := by ring
  have hnn : ∀ n : ℕ, 0 ≤ (l * v) ^ n / (n ! : ℝ) *
      ((coshL ^ n) (X ^ p : ℝ[X])).eval (l * A) := fun n =>
    mul_nonneg (by positivity) (coshL_pow_eval_nonneg n p (mul_nonneg hl0 hA))
  have hs2 : Summable fun n : ℕ => (l * v) ^ n / (n ! : ℝ) *
      ((coshL ^ n) (X ^ p : ℝ[X])).eval (l * A) :=
    Summable.of_nonneg_of_le hnn hterm (hsum.mul_left _)
  unfold gaussianMajorant
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum hterm hs2 (hsum.mul_left _)

end GMCExplicitDelta.Insertion
