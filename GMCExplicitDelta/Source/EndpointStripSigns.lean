module

public import GMCExplicitDelta.Source.EndpointStripReal
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Convex.Deriv

/-!
# Elementary inequalities for the sign-averaging step
-/

@[expose] public section

namespace GMCExplicitDelta.Source

/-- The endpoint envelope `max(|x|,|y|) + K|y - x|`. -/
noncomputable def envelope (x y : ℝ) : ℝ := max |x| |y| + stripK * |y - x|

theorem one_le_stripK : 1 ≤ stripK := by
  unfold stripK
  have : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  linarith

theorem abs_sub_of_mul_nonpos {x y : ℝ} (h : x * y ≤ 0) : |y - x| = |x| + |y| := by
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
  · have : x = 0 ∨ y = 0 := by
      rcases hx.eq_or_lt with h0 | h0
      · exact Or.inl h0.symm
      · right; nlinarith
    rcases this with rfl | rfl <;> simp [abs_of_nonneg hx, abs_of_nonneg hy]
  · rw [abs_of_nonneg hx, abs_of_nonpos hy, abs_of_nonpos (by linarith)]; ring
  · rw [abs_of_nonpos hx, abs_of_nonneg hy, abs_of_nonneg (by linarith)]; ring
  · have : x = 0 ∨ y = 0 := by
      rcases hx.eq_or_lt with h0 | h0
      · exact Or.inl h0
      · right; nlinarith
    rcases this with rfl | rfl <;> simp [abs_of_nonpos hx, abs_of_nonpos hy]

theorem abs_sub_of_mul_nonneg {x y : ℝ} (h : 0 ≤ x * y) : |y - x| = |(|y| - |x|)| := by
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hx, abs_of_nonneg hy]
  · have : x = 0 ∨ y = 0 := by
      rcases hx.eq_or_lt with h0 | h0
      · exact Or.inl h0.symm
      · right; nlinarith
    rcases this with rfl | rfl <;> simp [abs_of_nonneg hx, abs_of_nonpos hy]
  · have : x = 0 ∨ y = 0 := by
      rcases hx.eq_or_lt with h0 | h0
      · exact Or.inl h0
      · right; nlinarith
    rcases this with rfl | rfl <;> simp [abs_of_nonpos hx, abs_of_nonneg hy]
  · rw [abs_of_nonpos hx, abs_of_nonpos hy, show -y - -x = -(y - x) by ring, abs_neg]

/-- Opposite signs: the envelope squared dominates `(1+K)²(x²+y²)`. -/
theorem envelope_sq_ge_opposite {x y : ℝ} (h : x * y ≤ 0) :
    (1 + stripK) ^ 2 * (x ^ 2 + y ^ 2) ≤ envelope x y ^ 2 := by
  unfold envelope
  rw [abs_sub_of_mul_nonpos h]
  have hK := one_le_stripK
  set K := stripK
  set a := |x| with ha
  set b := |y| with hb
  have ha0 : 0 ≤ a := abs_nonneg _
  have hb0 : 0 ≤ b := abs_nonneg _
  have hx2 : x ^ 2 = a ^ 2 := (sq_abs x).symm
  have hy2 : y ^ 2 = b ^ 2 := (sq_abs y).symm
  rw [hx2, hy2]
  rcases le_total b a with hab | hab
  · rw [max_eq_left hab]
    nlinarith [mul_nonneg ha0 hb0, mul_nonneg (sub_nonneg.2 hab) hb0, sq_nonneg b,
      mul_nonneg (sub_nonneg.2 hK) (sq_nonneg b), mul_nonneg (sub_nonneg.2 hK) (mul_nonneg (sub_nonneg.2 hab) hb0)]
  · rw [max_eq_right hab]
    nlinarith [mul_nonneg ha0 hb0, mul_nonneg (sub_nonneg.2 hab) ha0, sq_nonneg a,
      mul_nonneg (sub_nonneg.2 hK) (sq_nonneg a), mul_nonneg (sub_nonneg.2 hK) (mul_nonneg (sub_nonneg.2 hab) ha0)]

theorem envelope_nonneg (x y : ℝ) : 0 ≤ envelope x y := by
  unfold envelope
  have := one_le_stripK
  exact add_nonneg ((abs_nonneg _).trans (le_max_left _ _)) (by positivity)

/-- The exponential sign-averaging inequality. -/
theorem exp_envelope_sum {δ : ℝ} (hδ : 0 < δ) (x y : ℝ) :
    1 + Real.exp ((1 + stripK) ^ 2 * x ^ 2 / δ ^ 2) * Real.exp ((1 + stripK) ^ 2 * y ^ 2 / δ ^ 2) ≤
      Real.exp (envelope x y ^ 2 / δ ^ 2) + Real.exp (envelope x (-y) ^ 2 / δ ^ 2) := by
  have hone : ∀ x y : ℝ, 1 ≤ Real.exp (envelope x y ^ 2 / δ ^ 2) := fun x y =>
    Real.one_le_exp (by positivity)
  have hopp : ∀ x y : ℝ, x * y ≤ 0 →
      Real.exp ((1 + stripK) ^ 2 * x ^ 2 / δ ^ 2) * Real.exp ((1 + stripK) ^ 2 * y ^ 2 / δ ^ 2) ≤
        Real.exp (envelope x y ^ 2 / δ ^ 2) := by
    intro x y h
    rw [← Real.exp_add, Real.exp_le_exp, ← add_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have := envelope_sq_ge_opposite h
    linarith
  rcases le_total (x * y) 0 with h | h
  · have := hopp x y h
    have := hone x (-y)
    linarith
  · have h' : x * (-y) ≤ 0 := by linarith
    have := hopp x (-y) h'
    have := hone x y
    simp only [neg_sq] at *
    linarith

theorem pair_sq_ge {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ((1 + stripK) ^ 2 + stripK ^ 2) * (a ^ 2 + b ^ 2) ≤
      (max a b + stripK * (a + b)) ^ 2 + (max a b + stripK * |a - b|) ^ 2 := by
  have hK := one_le_stripK
  set K := stripK
  rcases le_total b a with hab | hab
  · rw [max_eq_left hab, abs_of_nonneg (sub_nonneg.2 hab)]
    nlinarith [mul_nonneg (sub_nonneg.2 hab) (add_nonneg ha hb), sq_nonneg a, sq_nonneg b]
  · rw [max_eq_right hab, abs_of_nonpos (sub_nonpos.2 hab)]
    nlinarith [mul_nonneg (sub_nonneg.2 hab) (add_nonneg ha hb), sq_nonneg a, sq_nonneg b]

/-- The squared sign-averaging inequality. -/
theorem envelope_sq_sum (x y : ℝ) :
    ((1 + stripK) ^ 2 + stripK ^ 2) * (x ^ 2 + y ^ 2) ≤ envelope x y ^ 2 + envelope x (-y) ^ 2 := by
  have key : ∀ x y : ℝ, x * y ≤ 0 →
      ((1 + stripK) ^ 2 + stripK ^ 2) * (x ^ 2 + y ^ 2) ≤
        envelope x y ^ 2 + envelope x (-y) ^ 2 := by
    intro x y h
    have h2 : 0 ≤ x * (-y) := by linarith
    have e1 : envelope x y = max |x| |y| + stripK * (|x| + |y|) := by
      unfold envelope; rw [abs_sub_of_mul_nonpos h]
    have e2 : envelope x (-y) = max |x| |y| + stripK * |(|x| - |y|)| := by
      unfold envelope
      rw [abs_sub_of_mul_nonneg h2, abs_neg, abs_sub_comm]
    rw [e1, e2, ← sq_abs x, ← sq_abs y]
    exact pair_sq_ge (abs_nonneg _) (abs_nonneg _)
  rcases le_total (x * y) 0 with h | h
  · exact key x y h
  · have := key x (-y) (by linarith)
    simpa [neg_neg, neg_sq, add_comm] using this

end GMCExplicitDelta.Source
