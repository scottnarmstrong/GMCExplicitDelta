module

public import GMCExplicitDelta.Source.VarianceReal

/-!
# Pointwise bounds for a `C^{1,1}` path on `[0,1]`

The trapezoid error, the increment bound, and the integration by parts bound
`∫₀¹ G'² - G(1) G'(1) + G(0) G'(0) ≤ a c`, where `|G| ≤ a` and `G'` is `c`-Lipschitz.
-/

@[expose] public section

namespace GMCExplicitDelta.Source

open MeasureTheory intervalIntegral

section
variable {G G' : ℝ → ℝ} {a b c : ℝ}

theorem ftc_diag (hG : ∀ t, HasDerivAt G (G' t) t) (hG'c : Continuous G') (s t : ℝ) :
    ∫ τ in s..t, G' τ = G t - G s :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hG x) (hG'c.intervalIntegrable _ _)

/-- Trapezoid error for a path with Lipschitz derivative. -/
theorem trapezoid_bound (hG : ∀ t, HasDerivAt G (G' t) t) (hG'c : Continuous G')
    (hb : ∀ t ∈ Set.Icc (0:ℝ) 1, |G' t| ≤ b)
    (hc : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1, |G' s - G' t| ≤ c * |s - t|) :
    |(G 1 - G 0) - (G' 0 + G' 1) / 2| ≤ c / 4 := by
  have := strip_quadrature (f := G') hG'c.continuousOn (r := 1 / 2) (by norm_num) le_rfl hb hc
  rw [ftc_diag hG hG'c] at this
  norm_num at this
  have e : G 1 - G 0 - (G' 0 + G' 1) / 2 = G 1 - G 0 - 2⁻¹ * (G' 0 + G' 1) := by ring
  rw [e]
  linarith

/-- Increment bound. -/
theorem abs_sub_le_of_deriv (hG : ∀ t, HasDerivAt G (G' t) t) (hG'c : Continuous G')
    (hb : ∀ t ∈ Set.Icc (0:ℝ) 1, |G' t| ≤ b) : |G 1 - G 0| ≤ b := by
  rw [← ftc_diag hG hG'c, ← Real.norm_eq_abs]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (f := G') (C := b)
    (fun x hx => by
      rw [Set.uIoc_of_le zero_le_one] at hx
      rw [Real.norm_eq_abs]
      exact hb x ⟨hx.1.le, hx.2⟩)
  simpa using this

/-- Integration by parts bound. -/
theorem ibp_bound (hG : ∀ t, HasDerivAt G (G' t) t) (hG'c : Continuous G')
    (ha : ∀ t ∈ Set.Icc (0:ℝ) 1, |G t| ≤ a) (hb : ∀ t ∈ Set.Icc (0:ℝ) 1, |G' t| ≤ b)
    (hc : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1, |G' s - G' t| ≤ c * |s - t|) :
    (∫ t in (0:ℝ)..1, G' t ^ 2) - G 1 * G' 1 + G 0 * G' 0 ≤ a * c := by
  have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hc0 : 0 ≤ c := by
    have := (abs_nonneg _).trans (hc 0 h0 1 h1)
    simpa using this
  have hb0 : 0 ≤ b := (abs_nonneg _).trans (hb 0 h0)
  have ha0 : 0 ≤ a := (abs_nonneg _).trans (ha 0 h0)
  have hsq : Continuous fun t => G' t ^ 2 := hG'c.pow 2
  have hloc : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 →
      -(a * c) * (t - s) - (b * c) * (t - s) ^ 2 ≤
        (G t * G' t - ∫ τ in (0:ℝ)..t, G' τ ^ 2) - (G s * G' s - ∫ τ in (0:ℝ)..s, G' τ ^ 2) := by
    intro s t hs hst ht
    have hsm : s ∈ Set.Icc (0:ℝ) 1 := ⟨hs, hst.trans ht⟩
    have htm : t ∈ Set.Icc (0:ℝ) 1 := ⟨hs.trans hst, ht⟩
    have hI : (∫ τ in (0:ℝ)..t, G' τ ^ 2) - (∫ τ in (0:ℝ)..s, G' τ ^ 2) = ∫ τ in s..t, G' τ ^ 2 :=
      intervalIntegral.integral_interval_sub_left (hsq.intervalIntegrable _ _) (hsq.intervalIntegrable _ _)
    set I := ∫ τ in s..t, G' τ ^ 2 with hIdef
    set K0 := ∫ τ in s..t, G' τ * (G' τ - G' s) with hK0
    have hK0e : K0 = I - G' s * (G t - G s) := by
      have i1 : IntervalIntegrable (fun τ => G' τ ^ 2) volume s t := hsq.intervalIntegrable _ _
      have i2 : IntervalIntegrable (fun τ => G' s * G' τ) volume s t :=
        (continuous_const.mul hG'c).intervalIntegrable _ _
      rw [hK0, hIdef, ← ftc_diag hG hG'c s t, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_sub i1 i2]
      congr 1; ext τ; ring
    have hK0b : |K0| ≤ b * (c * (t - s)) * |t - s| := by
      rw [← Real.norm_eq_abs]
      refine intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => ?_)
      rw [Set.uIoc_of_le hst] at hx
      have hxm : x ∈ Set.Icc (0:ℝ) 1 := ⟨hs.trans hx.1.le, hx.2.trans ht⟩
      rw [Real.norm_eq_abs, abs_mul]
      have e1 := hb x hxm
      have e2 := hc x hxm s hsm
      rw [abs_of_nonneg (by linarith [hx.1] : 0 ≤ x - s)] at e2
      have e3 : c * (x - s) ≤ c * (t - s) := mul_le_mul_of_nonneg_left (by linarith [hx.2]) hc0
      exact mul_le_mul e1 (e2.trans e3) (abs_nonneg _) hb0
    have hT : |G t * (G' t - G' s)| ≤ a * (c * (t - s)) := by
      rw [abs_mul]
      have e2 := hc t htm s hsm
      rw [abs_of_nonneg (by linarith : 0 ≤ t - s)] at e2
      exact mul_le_mul (ha t htm) e2 (abs_nonneg _) ha0
    have hid : (G t * G' t - ∫ τ in (0:ℝ)..t, G' τ ^ 2) - (G s * G' s - ∫ τ in (0:ℝ)..s, G' τ ^ 2) =
        G t * (G' t - G' s) - K0 := by
      rw [hK0e]; linear_combination (-1 : ℝ) * hI
    rw [hid]
    rw [abs_of_nonneg (by linarith : 0 ≤ t - s)] at hK0b
    have e4 := (abs_le.1 hT).1
    have e5 := (abs_le.1 hK0b).2
    nlinarith
  have := neg_le_sub_of_local (f := fun t => G t * G' t - ∫ τ in (0:ℝ)..t, G' τ ^ 2)
    (c := a * c) (e := b * c) (mul_nonneg hb0 hc0) hloc
  simp only [intervalIntegral.integral_same] at this
  linarith

end

end GMCExplicitDelta.Source
