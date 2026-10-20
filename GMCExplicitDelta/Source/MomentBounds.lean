module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Analytic pieces of the all-even source moment lemma

Elementary exponential inequalities, a Stirling-type bound for `(k/e)^k` against the double
factorial, and the moment bound `∫ Z^k ≤ (2k-1)!!/2^k` for a nonnegative variable with
`∫ exp Z ≤ √3` and `∫ Z ≤ 1/2`.
-/

@[expose] public section

namespace GMCExplicitDelta.Source

open Real

/-- For `z ≥ 0`, `z² ≤ exp z - 1`. -/
theorem exp_sub_one_sub_sq_nonneg {z : ℝ} (hz : 0 ≤ z) : z ^ 2 ≤ Real.exp z - 1 := by
  have h := Real.sum_le_exp_of_nonneg hz 4
  simp [Finset.sum_range_succ, Nat.factorial] at h
  nlinarith [mul_nonneg hz (sq_nonneg (z - 3 / 2))]

/-- `z^k ≤ (k/e)^k exp z` for `z ≥ 0`, `k ≥ 1`. -/
theorem pow_le_pow_div_exp_mul_exp {k : ℕ} (hk : 1 ≤ k) {z : ℝ} (hz : 0 ≤ z) :
    z ^ k ≤ ((k : ℝ) / Real.exp 1) ^ k * Real.exp z := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 : z / k ≤ Real.exp (z / k - 1) := by
    have := Real.add_one_le_exp (z / k - 1); linarith
  have h2 : (z / k) ^ k ≤ Real.exp (z / k - 1) ^ k := pow_le_pow_left₀ (by positivity) h1 k
  rw [← Real.exp_nat_mul] at h2
  have h3 : (k : ℝ) * (z / k - 1) = z - k := by field_simp
  rw [h3, Real.exp_sub, div_pow] at h2
  have hek := Real.exp_pos (k : ℝ)
  have hkk : (0 : ℝ) < (k : ℝ) ^ k := by positivity
  have e1 : ((k : ℝ) / Real.exp 1) ^ k = (k : ℝ) ^ k / Real.exp k := by
    rw [div_pow, ← Real.exp_nat_mul, mul_one]
  rw [e1, div_le_div_iff₀ hkk hek] at *
  rw [div_mul_eq_mul_div, le_div_iff₀ hek]
  linarith

/-- `z ≤ k (1 - e^{-z})` on `[0, k-1]`. -/
theorem le_mul_one_sub_exp_neg {k : ℕ} (hk : 2 ≤ k) {z : ℝ} (hz : 0 ≤ z)
    (hzk : z ≤ (k : ℝ) - 1) : z ≤ k * (1 - Real.exp (-z)) := by
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  set w : ℝ := (k : ℝ) - 1 with hw
  have hw0 : 0 < w := by linarith
  set t : ℝ := z / w with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hw0]; exact hzk
  have htw : t * w = z := by rw [ht]; field_simp
  have hc := convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ (-w)) (sub_nonneg.2 ht1) ht0
    (by ring)
  simp only [smul_eq_mul, Real.exp_zero, mul_zero, zero_add, mul_one] at hc
  have hz' : t * -w = -z := by rw [← htw]; ring
  rw [hz'] at hc
  have hew : (k : ℝ) ≤ Real.exp w := by
    have := Real.add_one_le_exp w; rw [hw] at this ⊢; linarith
  have hexp : Real.exp (-w) * k ≤ 1 := by
    have : Real.exp (-w) * Real.exp w = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-w)]
  -- z ≤ t * w * ... : 1 - exp(-z) ≥ t (1 - exp(-w))
  have h1 : t * (1 - Real.exp (-w)) ≤ 1 - Real.exp (-z) := by nlinarith
  have h2 : w ≤ k * (1 - Real.exp (-w)) := by rw [hw]; nlinarith
  calc z = t * w := htw.symm
    _ ≤ t * (k * (1 - Real.exp (-w))) := mul_le_mul_of_nonneg_left h2 ht0
    _ = k * (t * (1 - Real.exp (-w))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)

/-- `z ↦ z^k / (exp z - 1)` is monotone on `(0, k-1]`. -/
theorem monotoneOn_pow_div_exp_sub_one {k : ℕ} (hk : 2 ≤ k) :
    MonotoneOn (fun z : ℝ => z ^ k / (Real.exp z - 1)) (Set.Ioc 0 ((k : ℝ) - 1)) := by
  have hne : ∀ z : ℝ, 0 < z → Real.exp z - 1 ≠ 0 := fun z hz => by
    have := Real.add_one_lt_exp hz.ne'; linarith
  have hd : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun z : ℝ => z ^ k / (Real.exp z - 1))
      ((k * z ^ (k - 1) * (Real.exp z - 1) - z ^ k * Real.exp z) / (Real.exp z - 1) ^ 2) z := by
    intro z hz
    have := ((hasDerivAt_pow k z).div ((Real.hasDerivAt_exp z).sub_const 1) (hne z hz))
    convert this using 1
  apply monotoneOn_of_deriv_nonneg (convex_Ioc _ _)
  · intro z hz
    exact (hd z hz.1).continuousAt.continuousWithinAt
  · intro z hz
    rw [interior_Ioc] at hz
    exact (hd z hz.1).differentiableAt.differentiableWithinAt
  · intro z hz
    rw [interior_Ioc] at hz
    rw [(hd z hz.1).deriv]
    have h := le_mul_one_sub_exp_neg hk hz.1.le hz.2.le
    have hez : Real.exp z * Real.exp (-z) = 1 := by rw [← Real.exp_add]; simp
    have h2 : z * Real.exp z ≤ k * (Real.exp z - 1) := by
      nlinarith [Real.exp_pos z]
    apply div_nonneg _ (sq_nonneg _)
    have hk1 : z ^ k = z ^ (k - 1) * z := by
      rw [← pow_succ]; congr 1; omega
    rw [hk1]
    have : 0 ≤ z ^ (k - 1) := (pow_pos hz.1 _).le
    nlinarith [mul_nonneg this (sub_nonneg.2 h2)]

/-- Pointwise bound with the maximal constant. -/
theorem pow_le_const_mul_exp_sub_one {k : ℕ} (hk : 3 ≤ k) {z : ℝ} (hz : 0 ≤ z) :
    z ^ k ≤ ((k : ℝ) / Real.exp 1) ^ k / (1 - Real.exp (-((k : ℝ) - 1))) *
      (Real.exp z - 1) := by
  have hk2 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  set w : ℝ := (k : ℝ) - 1 with hw
  have hw0 : 2 ≤ w := by linarith
  set A : ℝ := ((k : ℝ) / Real.exp 1) ^ k with hA
  have hA0 : 0 ≤ A := by positivity
  have hewpos := Real.exp_pos w
  have hlt : Real.exp (-w) < 1 := by
    have := Real.exp_lt_exp.2 (show -w < 0 by linarith); simpa using this
  set c : ℝ := 1 - Real.exp (-w) with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  have hexpw : Real.exp w - 1 = Real.exp w * c := by
    rw [hc, mul_sub, mul_one, ← Real.exp_add]; simp
  rw [div_mul_eq_mul_div, le_div_iff₀ hc0]
  rcases le_total w z with hwz | hzw
  · have h1 : Real.exp z * c ≤ Real.exp z - 1 := by
      have : Real.exp z * Real.exp (-w) = Real.exp (z - w) := by
        rw [← Real.exp_add]; ring_nf
      have h3 : 1 ≤ Real.exp (z - w) := Real.one_le_exp (by linarith)
      rw [hc]; nlinarith
    have h2 := pow_le_pow_div_exp_mul_exp (k := k) (by omega) hz
    calc z ^ k * c ≤ A * Real.exp z * c := mul_le_mul_of_nonneg_right h2 hc0.le
      _ = A * (Real.exp z * c) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 hA0
  · rcases hz.eq_or_lt with h0 | h0
    · subst h0; simp [zero_pow (show k ≠ 0 by omega)]
    · have hm := monotoneOn_pow_div_exp_sub_one (k := k) (by omega) ⟨h0, hzw⟩
        ⟨by linarith, le_refl _⟩ hzw
      have hez : 0 < Real.exp z - 1 := by
        have := Real.add_one_lt_exp h0.ne'; linarith
      have hewm : 0 < Real.exp w - 1 := by rw [hexpw]; positivity
      simp only at hm
      rw [div_le_div_iff₀ hez hewm] at hm
      have h2 := pow_le_pow_div_exp_mul_exp (k := k) (by omega) (show 0 ≤ w by linarith)
      have h3 : w ^ k * (Real.exp z - 1) ≤ A * Real.exp w * (Real.exp z - 1) :=
        mul_le_mul_of_nonneg_right h2 hez.le
      rw [hexpw] at hm
      have h4 : (z ^ k * c) * Real.exp w ≤ (A * (Real.exp z - 1)) * Real.exp w := by nlinarith
      exact le_of_mul_le_mul_right h4 hewpos

/-- The double factorial ratio satisfies `b_{k+1} = b_k (k + 1/2)`. -/
theorem doubleFactorial_ratio_succ (k : ℕ) :
    ((2 * (k + 1) - 1).doubleFactorial : ℝ) / 2 ^ (k + 1) =
      ((2 * k - 1).doubleFactorial : ℝ) / 2 ^ k * ((k : ℝ) + 1 / 2) := by
  have h : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  have h' : (2 * k + 1).doubleFactorial = (2 * k + 1) * (2 * k - 1).doubleFactorial :=
    Nat.doubleFactorial_add_one (2 * k)
  rw [h, h']
  push_cast
  field_simp
  ring

/-- Midpoint bound for the integral of `log` on `[k, k+1]`. -/
theorem log_step_le {k : ℕ} (hk : 1 ≤ k) :
    ((k : ℝ) + 1) * Real.log ((k : ℝ) + 1) - k * Real.log k - 1 ≤ Real.log ((k : ℝ) + 1 / 2) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set m : ℝ := (k : ℝ) + 1 / 2 with hm
  have hm0 : 0 < m := by rw [hm]; linarith
  have hI := integral_log (a := (k : ℝ)) (b := (k : ℝ) + 1)
  have hmono : ∫ t in (k : ℝ)..(k + 1), Real.log t ≤
      ∫ t in (k : ℝ)..(k + 1), (Real.log m - 1 + t / m) := by
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact intervalIntegral.intervalIntegrable_log'
    · exact (by fun_prop : Continuous fun t : ℝ => Real.log m - 1 + t / m).intervalIntegrable _ _
    · intro t ht
      have ht0 : 0 < t := by linarith [ht.1]
      have := Real.log_le_sub_one_of_pos (div_pos ht0 hm0)
      rw [Real.log_div ht0.ne' hm0.ne'] at this
      linarith
  have hJ : ∫ t in (k : ℝ)..(k + 1), (Real.log m - 1 + t / m) = Real.log m := by
    rw [intervalIntegral.integral_add (by simp) (by apply Continuous.intervalIntegrable; fun_prop)]
    simp only [intervalIntegral.integral_const, intervalIntegral.integral_div, integral_id,
      smul_eq_mul]
    field_simp
    rw [hm]; ring
  rw [hI, hJ] at hmono
  linarith

/-- `(k/e)^k ≤ (2k-1)!!/2^k` for all `k ≥ 0` (with `(-1)!! = 1`). -/
theorem pow_div_exp_le_doubleFactorial (k : ℕ) :
    ((k : ℝ) / Real.exp 1) ^ k ≤ ((2 * k - 1).doubleFactorial : ℝ) / 2 ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have key : ∀ n : ℕ, 1 ≤ n → (n : ℝ) * Real.log n - n ≤
      Real.log (((2 * n - 1).doubleFactorial : ℝ) / 2 ^ n) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      norm_num
      rw [one_div, Real.log_inv]
      linarith [Real.log_two_lt_d9]
    | succ n hn ih =>
      have hpos : (0 : ℝ) < ((2 * n - 1).doubleFactorial : ℝ) / 2 ^ n := by positivity
      rw [doubleFactorial_ratio_succ, Real.log_mul hpos.ne' (by positivity)]
      have := log_step_le hn
      push_cast
      linarith
  have h := key k hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hpos : (0 : ℝ) < ((2 * k - 1).doubleFactorial : ℝ) / 2 ^ k := by positivity
  calc ((k : ℝ) / Real.exp 1) ^ k = Real.exp ((k : ℝ) * Real.log k - k) := by
        rw [div_pow, ← Real.exp_nat_mul, mul_one, Real.exp_sub, ← Real.log_pow,
          Real.exp_log (by positivity)]
    _ ≤ _ := by
        calc _ ≤ Real.exp (Real.log (((2 * k - 1).doubleFactorial : ℝ) / 2 ^ k)) :=
              Real.exp_le_exp.2 h
          _ = _ := Real.exp_log hpos

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Integrability and integral bound from a pointwise bound by `C (exp Z - 1)`. -/
theorem integrable_pow_of_le {Z : Ω → ℝ} (hZm : Measurable Z)
    (hint : Integrable (fun ω => Real.exp (Z ω)) μ) {k : ℕ} {C : ℝ}
    (hC : ∀ z : ℝ, 0 ≤ z → z ^ k ≤ C * (Real.exp z - 1)) (hZ0 : ∀ ω, 0 ≤ Z ω) :
    Integrable (fun ω => Z ω ^ k) μ ∧
      ∫ ω, Z ω ^ k ∂μ ≤ C * ((∫ ω, Real.exp (Z ω) ∂μ) - 1) := by
  have hint' : Integrable (fun ω => C * (Real.exp (Z ω) - 1)) μ :=
    (hint.sub (integrable_const 1)).const_mul C
  have hle : ∀ ω, Z ω ^ k ≤ C * (Real.exp (Z ω) - 1) := fun ω => hC _ (hZ0 ω)
  have hI : Integrable (fun ω => Z ω ^ k) μ := by
    refine Integrable.mono' hint' (by fun_prop) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hZ0 ω) _)]
    exact hle ω
  refine ⟨hI, ?_⟩
  calc ∫ ω, Z ω ^ k ∂μ ≤ ∫ ω, C * (Real.exp (Z ω) - 1) ∂μ := integral_mono hI hint' hle
    _ = _ := by
      rw [integral_const_mul, integral_sub hint (integrable_const 1)]
      simp

/-- The moment bound `E Z^k ≤ (2k-1)!!/2^k`. -/
theorem integral_pow_le_doubleFactorial {Z : Ω → ℝ} (hZm : Measurable Z)
    (hZ0 : ∀ ω, 0 ≤ Z ω) (hint : Integrable (fun ω => Real.exp (Z ω)) μ)
    (h1 : ∫ ω, Real.exp (Z ω) ∂μ ≤ Real.sqrt 3) (h2 : ∫ ω, Z ω ∂μ ≤ 1 / 2) (k : ℕ) :
    Integrable (fun ω => Z ω ^ k) μ ∧
      ∫ ω, Z ω ^ k ∂μ ≤ ((2 * k - 1).doubleFactorial : ℝ) / 2 ^ k := by
  have hs : Real.sqrt 3 ≤ 7 / 4 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hZi : Integrable (fun ω => Z ω) μ := by
    have := (integrable_pow_of_le hZm hint (k := 1) (C := 2)
      (fun z hz => by
        have := Real.add_one_le_exp z
        have := Real.sum_le_exp_of_nonneg hz 3
        simp [Finset.sum_range_succ, Nat.factorial] at this
        nlinarith) hZ0).1
    simpa using this
  rcases k with _ | _ | _ | k
  · simp
  · simp only [zero_add, pow_one, mul_one]
    refine ⟨hZi, ?_⟩
    norm_num [Nat.doubleFactorial]
    exact h2
  · have := integrable_pow_of_le hZm hint (k := 2) (C := 1)
      (fun z hz => by simpa using exp_sub_one_sub_sq_nonneg hz) hZ0
    refine ⟨this.1, this.2.trans ?_⟩
    norm_num [Nat.doubleFactorial]
    linarith
  · set n : ℕ := k + 3 with hn
    have hn3 : 3 ≤ n := by omega
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    set A : ℝ := ((n : ℝ) / Real.exp 1) ^ n with hA
    set c : ℝ := 1 - Real.exp (-((n : ℝ) - 1)) with hc
    have hexp2 : 5 ≤ Real.exp 2 := by
      have := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num) 3
      simp [Finset.sum_range_succ, Nat.factorial] at this
      linarith
    have he : Real.exp (-((n : ℝ) - 1)) ≤ Real.exp (-2) :=
      Real.exp_le_exp.2 (by linarith)
    have hem : Real.exp (-2) * Real.exp 2 = 1 := by rw [← Real.exp_add]; simp
    have hem0 : Real.exp (-2) ≤ 1 / 5 := by
      nlinarith [Real.exp_pos (-2), Real.exp_pos 2]
    have hc0 : 0 < c := by
      have : Real.exp (-((n : ℝ) - 1)) ≤ 1 / 5 := he.trans hem0
      rw [hc]; linarith
    have hA0 : 0 ≤ A := by positivity
    have hsc : Real.sqrt 3 - 1 ≤ c := by rw [hc]; linarith [he.trans hem0]
    have hmain := integrable_pow_of_le hZm hint (k := n) (C := A / c)
      (fun z hz => pow_le_const_mul_exp_sub_one hn3 hz) hZ0
    refine ⟨hmain.1, hmain.2.trans ?_⟩
    have hint1 : 0 ≤ (∫ ω, Real.exp (Z ω) ∂μ) - 1 := by
      have : (1 : ℝ) ≤ ∫ ω, Real.exp (Z ω) ∂μ := by
        calc (1 : ℝ) = ∫ ω, (1 : ℝ) ∂μ := by simp
          _ ≤ _ := integral_mono (integrable_const 1) hint
            (fun ω => Real.one_le_exp (hZ0 ω))
      linarith
    have hmul : A / c * ((∫ ω, Real.exp (Z ω) ∂μ) - 1) ≤ A := by
      have : (∫ ω, Real.exp (Z ω) ∂μ) - 1 ≤ c := by linarith
      calc A / c * ((∫ ω, Real.exp (Z ω) ∂μ) - 1) ≤ A / c * c :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = A := by field_simp
    exact hmul.trans (pow_div_exp_le_doubleFactorial n)

/-- Rescaled moment bound: `E X^{2k} ≤ (2k-1)!! (δ²/(2α))^k`. -/
theorem integral_pow_two_mul_le {X : Ω → ℝ} (hXm : Measurable X) {α δ : ℝ} (hα : 0 < α)
    (hδ : 0 < δ)
    (hint : Integrable (fun ω => Real.exp (α * X ω ^ 2 / δ ^ 2)) μ)
    (h1 : ∫ ω, Real.exp (α * X ω ^ 2 / δ ^ 2) ∂μ ≤ Real.sqrt 3)
    (h2 : α * ∫ ω, X ω ^ 2 ∂μ ≤ δ ^ 2 / 2) (k : ℕ) :
    Integrable (fun ω => X ω ^ (2 * k)) μ ∧
      ∫ ω, X ω ^ (2 * k) ∂μ ≤ ((2 * k - 1).doubleFactorial : ℝ) * (δ ^ 2 / (2 * α)) ^ k := by
  have hδ2 : 0 < δ ^ 2 := by positivity
  set Z : Ω → ℝ := fun ω => α * X ω ^ 2 / δ ^ 2 with hZ
  have hZm : Measurable Z := by rw [hZ]; fun_prop
  have hZ0 : ∀ ω, 0 ≤ Z ω := fun ω => by rw [hZ]; positivity
  have hZint : ∫ ω, Z ω ∂μ = α / δ ^ 2 * ∫ ω, X ω ^ 2 ∂μ := by
    rw [← integral_const_mul]; congr 1; ext ω; rw [hZ]; ring
  have h2' : ∫ ω, Z ω ∂μ ≤ 1 / 2 := by
    rw [hZint, div_mul_eq_mul_div, div_le_iff₀ hδ2]; linarith
  obtain ⟨hi, hb⟩ := integral_pow_le_doubleFactorial hZm hZ0 hint h1 h2' k
  have hpt : ∀ ω, X ω ^ (2 * k) = (δ ^ 2 / α) ^ k * Z ω ^ k := fun ω => by
    rw [hZ]; simp only
    rw [← mul_pow, pow_mul]
    congr 1; field_simp
  simp_rw [hpt]
  refine ⟨hi.const_mul _, ?_⟩
  rw [integral_const_mul]
  calc (δ ^ 2 / α) ^ k * ∫ ω, Z ω ^ k ∂μ
      ≤ (δ ^ 2 / α) ^ k * (((2 * k - 1).doubleFactorial : ℝ) / 2 ^ k) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by
        rw [show δ ^ 2 / (2 * α) = (δ ^ 2 / α) / 2 by field_simp, div_pow (δ ^ 2 / α) 2 k]
        ring

end GMCExplicitDelta.Source
