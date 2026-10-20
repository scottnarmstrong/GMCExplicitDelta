module

public import GMCExplicitDelta.Source.EndpointStripReal
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Deterministic real-analysis lemmas for the source variance bound

Pointwise inequalities on `[0,1]` for a `C^{1,1}` path `G` (derivative `G'` Lipschitz): the trapezoid
error, the integration by parts bound `∫ G'² - [G G'] ≤ a c`, a Cauchy-Schwarz inequality, the
two-sided Lipschitz envelope bound `K ≥ (1 + √2) r`, and a local-to-global integral increment lemma.
-/

@[expose] public section

namespace GMCExplicitDelta.Source

open MeasureTheory intervalIntegral

/-- Cauchy-Schwarz on `[0,h]`. -/
theorem sq_integral_le {f : ℝ → ℝ} (hf : Continuous f) {h : ℝ} (hh : 0 ≤ h) :
    (∫ t in (0:ℝ)..h, f t) ^ 2 ≤ h * ∫ t in (0:ℝ)..h, f t ^ 2 := by
  rcases hh.eq_or_lt with rfl | hpos
  · simp
  set m := ∫ t in (0:ℝ)..h, f t with hm
  set q := ∫ t in (0:ℝ)..h, f t ^ 2 with hq
  have hnn : 0 ≤ ∫ t in (0:ℝ)..h, (f t - m / h) ^ 2 :=
    intervalIntegral.integral_nonneg hh (fun t _ => sq_nonneg _)
  have i1 : IntervalIntegrable (fun t => f t ^ 2) volume 0 h := (hf.pow 2).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun t => 2 * (m / h) * f t) volume 0 h :=
    (continuous_const.mul hf).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun _ : ℝ => (m / h) ^ 2) volume 0 h := intervalIntegrable_const
  have hexp : ∫ t in (0:ℝ)..h, (f t - m / h) ^ 2 = q - 2 * (m / h) * m + (m / h) ^ 2 * h := by
    have : ∀ t, (f t - m / h) ^ 2 = (f t ^ 2 - 2 * (m / h) * f t) + (m / h) ^ 2 := fun t => by ring
    simp_rw [this]
    rw [integral_add (i1.sub i2) i3, integral_sub i1 i2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    simp only [smul_eq_mul, sub_zero]
    rw [← hm, ← hq]; ring
  rw [hexp] at hnn
  have : q - 2 * (m / h) * m + (m / h) ^ 2 * h = q - m ^ 2 / h := by field_simp; ring
  rw [this, sub_nonneg, div_le_iff₀ hpos] at hnn
  linarith

theorem integral_affine (α β a b : ℝ) :
    ∫ t in a..b, (α + β * t) = α * (b - a) + β * (b ^ 2 - a ^ 2) / 2 := by
  have i : IntervalIntegrable (fun t : ℝ => β * t) volume a b :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  rw [integral_add intervalIntegrable_const i, intervalIntegral.integral_const_mul, integral_id,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul]; ring


/-- The Lipschitz envelope bound: `R(0) = r`, `R(1) = 0`, `∫₀¹ R = 0`, `R` is `K`-Lipschitz, so
`K ≥ (1 + √2) r`. -/
theorem envelope_lower {R : ℝ → ℝ} {K r : ℝ} (hr : 0 ≤ r) (hc : ContinuousOn R (Set.Icc 0 1))
    (hlip : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1, |R s - R t| ≤ K * |s - t|)
    (h0 : R 0 = r) (h1 : R 1 = 0) (hint : ∫ t in (0:ℝ)..1, R t = 0) :
    (1 + Real.sqrt 2) * r ≤ K := by
  have h0m : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1m : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hrK : r ≤ K := by
    have := hlip 0 h0m 1 h1m
    rw [h0, h1] at this
    simpa [abs_of_nonneg hr] using this
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hs0 := Real.sqrt_nonneg 2
  rcases (hr.trans hrK).eq_or_lt with hK0 | hK
  · have : r = 0 := by linarith
    rw [← hK0, this]; simp
  set τ : ℝ := (r + K) / (2 * K) with hτdef
  have hτ : 2 * K * τ = r + K := by rw [hτdef]; field_simp
  have hτ0 : 0 ≤ τ := by positivity
  have hτ1 : τ ≤ 1 := by
    rw [hτdef, div_le_one (by positivity)]; linarith
  have hτm : τ ∈ Set.Icc (0:ℝ) 1 := ⟨hτ0, hτ1⟩
  have hint' : ∀ a b : ℝ, a ∈ Set.Icc (0:ℝ) 1 → b ∈ Set.Icc (0:ℝ) 1 →
      IntervalIntegrable R volume a b := fun a b ha hb =>
    (hc.mono (Set.uIcc_subset_Icc ha hb)).intervalIntegrable
  have hA : ∀ t ∈ Set.Icc (0:ℝ) 1, r + (-K) * t ≤ R t := by
    intro t ht
    have h := (abs_le.1 (hlip t ht 0 h0m)).1
    have e : |t - 0| = t := by rw [sub_zero]; exact abs_of_nonneg ht.1
    rw [e, h0] at h
    linarith
  have hB : ∀ t ∈ Set.Icc (0:ℝ) 1, -K + K * t ≤ R t := by
    intro t ht
    have h := (abs_le.1 (hlip t ht 1 h1m)).1
    have e : |t - 1| = 1 - t := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith [ht.2])
    rw [e, h1] at h
    linarith
  have i1 : ∫ t in (0:ℝ)..τ, (r + (-K) * t) ≤ ∫ t in (0:ℝ)..τ, R t :=
    intervalIntegral.integral_mono_on hτ0
      (by exact (continuous_const.add (continuous_const.mul continuous_id)).intervalIntegrable _ _)
      (hint' _ _ h0m hτm) (fun t ht => hA t ⟨ht.1, ht.2.trans hτ1⟩)
  have i2 : ∫ t in τ..1, (-K + K * t) ≤ ∫ t in τ..1, R t :=
    intervalIntegral.integral_mono_on hτ1
      (by exact (continuous_const.add (continuous_const.mul continuous_id)).intervalIntegrable _ _)
      (hint' _ _ hτm h1m) (fun t ht => hB t ⟨hτ0.trans ht.1, ht.2⟩)
  rw [integral_affine] at i1 i2
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hint' _ _ h0m hτm) (hint' _ _ hτm h1m)
  rw [hint] at hsplit
  have hE : r * (τ - 0) + (-K) * (τ ^ 2 - 0 ^ 2) / 2 + ((-K) * (1 - τ) + K * (1 ^ 2 - τ ^ 2) / 2) ≤ 0 := by
    linarith
  have hE2 : (r + K) ^ 2 ≤ 2 * K ^ 2 := by
    have h2K : 0 ≤ 2 * K := by linarith
    have := mul_le_mul_of_nonneg_left hE h2K
    have key : 2 * K * (r * (τ - 0) + (-K) * (τ ^ 2 - 0 ^ 2) / 2 +
        ((-K) * (1 - τ) + K * (1 ^ 2 - τ ^ 2) / 2)) = (r + K) ^ 2 / 2 - K ^ 2 := by
      linear_combination (-(2 * K * τ - (r + K)) / 2) * hτ
    nlinarith
  have hle : r + K ≤ Real.sqrt 2 * K := by
    have : (r + K) ^ 2 ≤ (Real.sqrt 2 * K) ^ 2 := by rw [mul_pow, hs]; linarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 this
  have h3 : r ≤ (Real.sqrt 2 - 1) * K := by linarith
  have h4 : (1 + Real.sqrt 2) * (Real.sqrt 2 - 1) = 1 := by nlinarith
  calc (1 + Real.sqrt 2) * r ≤ (1 + Real.sqrt 2) * ((Real.sqrt 2 - 1) * K) := by gcongr
    _ = K := by rw [← mul_assoc, h4, one_mul]

/-- A function whose increments satisfy a local lower bound has a global one. -/
theorem neg_le_sub_of_local {f : ℝ → ℝ} {c e : ℝ} (he : 0 ≤ e)
    (h : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 → -c * (t - s) - e * (t - s) ^ 2 ≤ f t - f s) :
    -c ≤ f 1 - f 0 := by
  have key : ∀ N : ℕ, 0 < N → ∀ k : ℕ, k ≤ N →
      -c * ((k:ℝ) / N) - e * ((k:ℝ) / N) * (1 / N) ≤ f ((k:ℝ) / N) - f 0 := by
    intro N hN k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hk' : k ≤ N := Nat.le_of_succ_le hk
      have h1 := ih hk'
      have hNpos : (0:ℝ) < N := by exact_mod_cast hN
      have hs : (0:ℝ) ≤ (k:ℝ) / N := by positivity
      have hst : (k:ℝ) / N ≤ ((k + 1 : ℕ) : ℝ) / N := by
        gcongr; push_cast; linarith
      have ht1 : ((k + 1 : ℕ) : ℝ) / N ≤ 1 := by
        rw [div_le_one hNpos]; exact_mod_cast hk
      have h2 := h _ _ hs hst ht1
      have hd : ((k + 1 : ℕ) : ℝ) / N - (k:ℝ) / N = 1 / N := by push_cast; ring
      rw [hd] at h2
      have e1 : ((k + 1 : ℕ) : ℝ) / N = (k:ℝ) / N + 1 / N := by push_cast; ring
      rw [e1] at h2 ⊢
      nlinarith
  by_contra hcon
  push Not at hcon
  have hδ : 0 < -c - (f 1 - f 0) := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (e / (-c - (f 1 - f 0)))
  have hNpos : (0:ℝ) < N := lt_of_le_of_lt (div_nonneg he hδ.le) hN
  have := key N (by exact_mod_cast hNpos) N le_rfl
  rw [div_self hNpos.ne'] at this
  have h3 : e / N < -c - (f 1 - f 0) := by
    rw [div_lt_iff₀ hNpos]; rw [div_lt_iff₀ hδ] at hN; linarith
  have h5 : e * 1 * (1 / (N:ℝ)) = e / N := by ring
  linarith

end GMCExplicitDelta.Source
