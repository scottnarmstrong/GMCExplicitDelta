module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Deterministic pieces of the endpoint-strip argument
-/

@[expose] public section

namespace GMCExplicitDelta.Source

open MeasureTheory intervalIntegral

/-- Endpoint-strip quadrature for a Lipschitz function on `[0,1]`. -/
theorem strip_quadrature {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1)) {B C r : ℝ}
    (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (hB : ∀ t ∈ Set.Icc (0:ℝ) 1, |f t| ≤ B)
    (hC : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1, |f s - f t| ≤ C * |s - t|) :
    |(∫ t in (0:ℝ)..1, f t) - r * (f 0 + f 1)| ≤ (1 - 2 * r) * B + r ^ 2 * C := by
  have hint : ∀ a b : ℝ, a ∈ Set.Icc (0:ℝ) 1 → b ∈ Set.Icc (0:ℝ) 1 → IntervalIntegrable f volume a b := by
    intro a b ha hb
    refine (hf.mono ?_).intervalIntegrable
    exact Set.uIcc_subset_Icc ha hb
  have h0r : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_refl _, zero_le_one⟩
  have hrI : r ∈ Set.Icc (0:ℝ) 1 := ⟨hr0, by linarith⟩
  have h1rI : 1 - r ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  have h1I : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨zero_le_one, le_refl _⟩
  have hsplit : (∫ t in (0:ℝ)..1, f t) =
      (∫ t in (0:ℝ)..r, f t) + (∫ t in r..(1 - r), f t) + ∫ t in (1 - r)..1, f t := by
    rw [integral_add_adjacent_intervals (hint _ _ h0r hrI) (hint _ _ hrI h1rI),
      integral_add_adjacent_intervals (hint _ _ h0r h1rI) (hint _ _ h1rI h1I)]
  -- first strip
  have hs1 : |(∫ t in (0:ℝ)..r, f t) - r * f 0| ≤ C * r ^ 2 / 2 := by
    have : (∫ t in (0:ℝ)..r, f t) - r * f 0 = ∫ t in (0:ℝ)..r, (f t - f 0) := by
      rw [integral_sub (hint _ _ h0r hrI) intervalIntegrable_const]; simp
    rw [this]
    have := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := 0) (b := r) (f := fun t => f t - f 0)
      (g := fun t => C * t) hr0 ?_ ?_
    · have e : (∫ t in (0:ℝ)..r, C * t) = C * r ^ 2 / 2 := by
        rw [intervalIntegral.integral_const_mul, integral_id]; ring
      rw [e, Real.norm_eq_abs] at this
      exact this
    · refine Filter.Eventually.of_forall fun t ht => ?_
      rw [Real.norm_eq_abs]
      have := hC t ⟨ht.1.le, by linarith [ht.2]⟩ 0 h0r
      simpa [abs_of_pos ht.1] using this
    · exact (continuous_const.mul continuous_id).intervalIntegrable _ _
  have hs3 : |(∫ t in (1 - r)..1, f t) - r * f 1| ≤ C * r ^ 2 / 2 := by
    have : (∫ t in (1 - r)..1, f t) - r * f 1 = ∫ t in (1 - r)..1, (f t - f 1) := by
      rw [integral_sub (hint _ _ h1rI h1I) intervalIntegrable_const]; simp
    rw [this]
    have := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := 1 - r) (b := 1)
      (f := fun t => f t - f 1) (g := fun t => C * (1 - t)) (by linarith) ?_ ?_
    · have e : (∫ t in (1 - r)..1, C * (1 - t)) = C * r ^ 2 / 2 := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_left (fun t => t) 1]
        simp only [sub_self, sub_sub_cancel]
        rw [integral_id]; ring
      rw [e, Real.norm_eq_abs] at this
      exact this
    · refine Filter.Eventually.of_forall fun t ht => ?_
      rw [Real.norm_eq_abs]
      have ht' : t ∈ Set.Ioc (1 - r) 1 := ht
      have := hC t ⟨by linarith [ht'.1], ht'.2⟩ 1 h1I
      rw [abs_sub_comm t 1, abs_of_nonneg (by linarith [ht'.2] : (0:ℝ) ≤ 1 - t)] at this
      exact this
    · exact (continuous_const.mul (continuous_const.sub continuous_id)).intervalIntegrable _ _
  have hs2 : |∫ t in r..(1 - r), f t| ≤ (1 - 2 * r) * B := by
    have := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := r) (b := 1 - r) (f := f)
      (g := fun _ => B) (by linarith) ?_ ?_
    · simp only [intervalIntegral.integral_const, smul_eq_mul] at this
      rw [Real.norm_eq_abs] at this
      refine this.trans (le_of_eq ?_); ring
    · refine Filter.Eventually.of_forall fun t ht => ?_
      rw [Real.norm_eq_abs]
      have ht' : t ∈ Set.Ioc r (1 - r) := ht
      exact hB t ⟨by linarith [ht'.1], by linarith [ht'.2]⟩
    · exact intervalIntegrable_const
  have : (∫ t in (0:ℝ)..1, f t) - r * (f 0 + f 1) =
      ((∫ t in (0:ℝ)..r, f t) - r * f 0) + (∫ t in r..(1 - r), f t) +
        ((∫ t in (1 - r)..1, f t) - r * f 1) := by rw [hsplit]; ring
  rw [this]
  calc _ ≤ |((∫ t in (0:ℝ)..r, f t) - r * f 0) + (∫ t in r..(1 - r), f t)| +
        |(∫ t in (1 - r)..1, f t) - r * f 1| := abs_add_le _ _
    _ ≤ (|(∫ t in (0:ℝ)..r, f t) - r * f 0| + |∫ t in r..(1 - r), f t|) +
        |(∫ t in (1 - r)..1, f t) - r * f 1| := by gcongr; exact abs_add_le _ _
    _ ≤ _ := by linarith


/-- The strip constant `r = √2 - 1`. -/
noncomputable def stripR : ℝ := Real.sqrt 2 - 1

/-- The strip constant `K = 3 + 2√2 = 1/r²`. -/
noncomputable def stripK : ℝ := 3 + 2 * Real.sqrt 2

theorem stripR_pos : 0 < stripR := by
  unfold stripR
  have : (1:ℝ) < Real.sqrt 2 := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

theorem stripR_le_half : stripR ≤ 1 / 2 := by
  unfold stripR
  have : Real.sqrt 2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  linarith

theorem stripR_sq : stripR ^ 2 = 3 - 2 * Real.sqrt 2 := by
  unfold stripR
  have := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  nlinarith

theorem one_sub_two_stripR : 1 - 2 * stripR = stripR ^ 2 := by
  rw [stripR_sq]; unfold stripR; ring

theorem stripK_mul_sq : stripK * stripR ^ 2 = 1 := by
  rw [stripR_sq]; unfold stripK
  have := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  nlinarith

theorem stripK_pos : 0 < stripK := by
  unfold stripK; positivity

/-- The pointwise endpoint-strip bound for a `C^{1,1}` function on `[0,1]`. -/
theorem endpoint_strip_bound {G G' : ℝ → ℝ} {A B C : ℝ} (hG : ∀ t, HasDerivAt G (G' t) t)
    (hG'c : Continuous G') (hA : ∀ t ∈ Set.Icc (0:ℝ) 1, |G t| ≤ A)
    (hB : ∀ t ∈ Set.Icc (0:ℝ) 1, |G' t| ≤ B)
    (hC : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1, |G' s - G' t| ≤ C * |s - t|) :
    max |G 0| |G 1| + stripK * |(G 1 - G 0) - stripR * (G' 0 + G' 1)| ≤ A + B + C := by
  have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hm : max |G 0| |G 1| ≤ A := max_le (hA _ h0) (hA _ h1)
  have hC0 : 0 ≤ C := by
    have := hC 0 h0 1 h1
    have h2 : 0 ≤ C * |(0:ℝ) - 1| := (abs_nonneg _).trans this
    simpa using h2
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 h0)
  have hftc : (∫ t in (0:ℝ)..1, G' t) = G 1 - G 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hG t)
      (hG'c.intervalIntegrable _ _)
  have hq := strip_quadrature (f := G') hG'c.continuousOn (r := stripR) stripR_pos.le
    stripR_le_half hB hC
  rw [hftc, one_sub_two_stripR] at hq
  have : stripK * |(G 1 - G 0) - stripR * (G' 0 + G' 1)| ≤ B + C := by
    have := mul_le_mul_of_nonneg_left hq stripK_pos.le
    calc _ ≤ stripK * (stripR ^ 2 * B + stripR ^ 2 * C) := this
      _ = (stripK * stripR ^ 2) * (B + C) := by ring
      _ = B + C := by rw [stripK_mul_sq, one_mul]
  linarith

end GMCExplicitDelta.Source
