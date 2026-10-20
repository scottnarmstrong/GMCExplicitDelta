module

public import GMCExplicitDelta.Proofs.Scaling.Fresh

/-!
# R4(b)–(d), part 1: scalar monotonicity lemmas

The prefactor `Φ_{log(1+2x)}(a x)/x` is nondecreasing in `x`, the suprema `M₁, M₂` are bounded and
nonincreasing in `b_g`, and the history terms `z/(1-z)²`, `z(1+z)/(1-z)³` scale.
-/

@[expose] public section

open Real

namespace GMCExplicitDelta.Assembly

open Contract

/-! ### The prefactor of the bad charge -/

theorem phiLog_closed {a x : ℝ} (hx : 0 < x) :
    PhiMap (Real.log (1 + 2 * x)) (a * x) / x =
      a * (1 + 2 * x ^ 2 / (1 + 2 * x)) + 2 * x / (1 + 2 * x) +
        2 * (1 + x) / (1 + 2 * x) * √(a * x * (a * x + 2)) := by
  have h12 : (0 : ℝ) < 1 + 2 * x := by positivity
  have hc : Real.cosh (Real.log (1 + 2 * x)) = (1 + 2 * x + 2 * x ^ 2) / (1 + 2 * x) := by
    rw [Real.cosh_eq, Real.exp_neg, Real.exp_log h12]
    field_simp; ring
  have hs : Real.sinh (Real.log (1 + 2 * x)) = 2 * x * (1 + x) / (1 + 2 * x) := by
    rw [Real.sinh_eq, Real.exp_neg, Real.exp_log h12]
    field_simp; ring
  unfold PhiMap
  rw [hc, hs]
  field_simp
  ring

theorem g_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    (1 + x) ^ 2 / (1 + 2 * x) ^ 2 * x ≤ (1 + y) ^ 2 / (1 + 2 * y) ^ 2 * y := by
  have hy : 0 ≤ y := hx.trans hxy
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have : (1 + y) ^ 2 * y * (1 + 2 * x) ^ 2 - (1 + x) ^ 2 * x * (1 + 2 * y) ^ 2 =
      (y - x) * (4 * x ^ 2 * y ^ 2 + 4 * x ^ 2 * y + x ^ 2 + 4 * x * y ^ 2 + 5 * x * y + 2 * x +
        y ^ 2 + 2 * y + 1) := by ring
  have h2 : 0 ≤ (y - x) * (4 * x ^ 2 * y ^ 2 + 4 * x ^ 2 * y + x ^ 2 + 4 * x * y ^ 2 + 5 * x * y +
      2 * x + y ^ 2 + 2 * y + 1) := mul_nonneg (by linarith) (by positivity)
  nlinarith

theorem prefactor_mono {a x y : ℝ} (ha : 0 ≤ a) (hx : 0 < x) (hxy : x ≤ y) :
    PhiMap (Real.log (1 + 2 * x)) (a * x) / x ≤ PhiMap (Real.log (1 + 2 * y)) (a * y) / y := by
  have hy : 0 < y := hx.trans_le hxy
  rw [phiLog_closed hx, phiLog_closed hy]
  have t1 : 2 * x ^ 2 / (1 + 2 * x) ≤ 2 * y ^ 2 / (1 + 2 * y) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.2 hxy) (by positivity : 0 ≤ y + x + 2 * x * y)]
  have t2 : 2 * x / (1 + 2 * x) ≤ 2 * y / (1 + 2 * y) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have t3 : 2 * (1 + x) / (1 + 2 * x) * √(a * x * (a * x + 2)) ≤
      2 * (1 + y) / (1 + 2 * y) * √(a * y * (a * y + 2)) := by
    have hu : ∀ z : ℝ, 0 ≤ z → 2 * (1 + z) / (1 + 2 * z) * √(a * z * (a * z + 2)) =
        √((2 * (1 + z) / (1 + 2 * z)) ^ 2 * (a * z * (a * z + 2))) := by
      intro z hz
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
    rw [hu x hx.le, hu y hy.le]
    apply Real.sqrt_le_sqrt
    have hg := g_mono hx.le hxy
    have e : ∀ z : ℝ, (2 * (1 + z) / (1 + 2 * z)) ^ 2 * (a * z * (a * z + 2)) =
        4 * a * ((1 + z) ^ 2 / (1 + 2 * z) ^ 2 * z) * (a * z + 2) := by
      intro z; rw [div_pow]; ring
    rw [e, e]
    have hgx : 0 ≤ (1 + x) ^ 2 / (1 + 2 * x) ^ 2 * x := by positivity
    have hxa : a * x + 2 ≤ a * y + 2 := by nlinarith
    have h4 : 0 ≤ 4 * a := by positivity
    calc 4 * a * ((1 + x) ^ 2 / (1 + 2 * x) ^ 2 * x) * (a * x + 2)
        ≤ 4 * a * ((1 + y) ^ 2 / (1 + 2 * y) ^ 2 * y) * (a * x + 2) := by
          have := mul_le_mul_of_nonneg_left hg h4
          exact mul_le_mul_of_nonneg_right this (by positivity)
      _ ≤ 4 * a * ((1 + y) ^ 2 / (1 + 2 * y) ^ 2 * y) * (a * y + 2) :=
          mul_le_mul_of_nonneg_left hxa (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left t1 ha]

/-! ### The suprema `M₁`, `M₂` -/

theorem M1_term_bdd {b c A : ℝ} (hb : 0 < b) (hc : 0 ≤ c) (hA : 0 ≤ A) (t : ℝ) (ht : 1 ≤ t) :
    (c * √t + A) ^ 2 * Real.exp (-(b * t)) ≤ 2 * c ^ 2 / b + 2 * A ^ 2 := by
  have ht0 : 0 < t := by linarith
  have hs : √t ^ 2 = t := Real.sq_sqrt ht0.le
  have h1 : (c * √t + A) ^ 2 ≤ 2 * c ^ 2 * t + 2 * A ^ 2 := by
    nlinarith [sq_nonneg (c * √t - A)]
  have he : Real.exp (-(b * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have he0 : 0 < Real.exp (-(b * t)) := Real.exp_pos _
  have h2 : t * Real.exp (-(b * t)) ≤ 1 / b := by
    have hge : b * t + 1 ≤ Real.exp (b * t) := Real.add_one_le_exp _
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) hb]
    nlinarith
  calc (c * √t + A) ^ 2 * Real.exp (-(b * t))
      ≤ (2 * c ^ 2 * t + 2 * A ^ 2) * Real.exp (-(b * t)) :=
        mul_le_mul_of_nonneg_right h1 he0.le
    _ = 2 * c ^ 2 * (t * Real.exp (-(b * t))) + 2 * A ^ 2 * Real.exp (-(b * t)) := by ring
    _ ≤ 2 * c ^ 2 * (1 / b) + 2 * A ^ 2 * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left h2 (by positivity))
          (mul_le_mul_of_nonneg_left he (by positivity))
    _ = _ := by ring

theorem M2_term_bdd {b : ℝ} (hb : 0 < b) (t : ℝ) (ht : 1 ≤ t) :
    t ^ 2 * Real.exp (-(b * t)) ≤ 2 / b ^ 2 := by
  have ht0 : 0 < t := by linarith
  have hbt : 0 < b * t := by positivity
  have hge : (b * t) ^ 2 / 2 ≤ Real.exp (b * t) := by
    have := Real.quadratic_le_exp_of_nonneg hbt.le
    nlinarith
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
  nlinarith

end GMCExplicitDelta.Assembly
