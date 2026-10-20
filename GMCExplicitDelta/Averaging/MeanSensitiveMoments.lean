module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Interpolation and centered moments (A1)

For `X ≥ 0` with `E X ≤ F`, `E X^p ≤ D^p`, `ϖ = min (F/D) 1`:
`E X^r ≤ F^((p-r)/(p-1)) D^(p(r-1)/(p-1))`, `E X^r ≤ D^r`, and for `r ≥ 2`
`E |X - E X|^r ≤ E X^r - (E X)^r ≤ D^r ϖ^((p-r)/(p-1))`.
-/

@[expose] public section

namespace GMCExplicitDelta.Averaging

open MeasureTheory

/-- Superadditivity of `x ↦ x^r` around a base point, `x ≥ μ` case. -/
theorem pow_add_ge (s : ℕ) {m h : ℝ} (hm : 0 ≤ m) (hh : 0 ≤ h) :
    m ^ (s + 2) + (s + 2 : ℝ) * m ^ (s + 1) * h + h ^ (s + 2) ≤ (m + h) ^ (s + 2) := by
  induction s with
  | zero => apply le_of_eq; push_cast; ring
  | succ s ih =>
    have h1 := mul_le_mul_of_nonneg_left ih (add_nonneg hm hh)
    have h2 : 0 ≤ m * (h ^ (s + 1) * h) := mul_nonneg hm (mul_nonneg (pow_nonneg hh _) hh)
    have h3 : 0 ≤ m ^ (s + 1) * (h * h) := mul_nonneg (pow_nonneg hm _) (mul_nonneg hh hh)
    have h4 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
    have e1 : (m + h) ^ (s + 1 + 2) = (m + h) * (m + h) ^ (s + 2) := by ring
    have e2 : m ^ (s + 1 + 2) = m ^ (s + 1) * m * m := by ring
    have e3 : m ^ (s + 2) = m ^ (s + 1) * m := by ring
    have e4 : m ^ (s + 1 + 1) = m ^ (s + 1) * m := by ring
    have e5 : h ^ (s + 1 + 2) = h ^ (s + 1) * h * h := by ring
    have e6 : h ^ (s + 2) = h ^ (s + 1) * h := by ring
    rw [e1, e2, e4, e5]
    rw [e3, e6] at h1
    push_cast
    nlinarith [mul_nonneg h4 h3]

/-- The case `0 ≤ h ≤ m`: `(m - h)^r ≥ m^r - r m^(r-1) h + h^r`. -/
theorem pow_sub_ge (s : ℕ) {m h : ℝ} (hh : 0 ≤ h) (hhm : h ≤ m) :
    m ^ (s + 2) - (s + 2 : ℝ) * m ^ (s + 1) * h + h ^ (s + 2) ≤ (m - h) ^ (s + 2) := by
  have hm : 0 ≤ m := hh.trans hhm
  induction s with
  | zero => apply le_of_eq; push_cast; ring
  | succ s ih =>
    have h1 := mul_le_mul_of_nonneg_left ih (sub_nonneg.2 hhm)
    have h2 : 0 ≤ (m - h) * (h ^ (s + 1) * h) :=
      mul_nonneg (sub_nonneg.2 hhm) (mul_nonneg (pow_nonneg hh _) hh)
    have h3 : h ^ (s + 1) ≤ m ^ (s + 1) := pow_le_pow_left₀ hh hhm _
    have h3' : h ^ (s + 1) * (h * h) ≤ m ^ (s + 1) * (h * h) :=
      mul_le_mul_of_nonneg_right h3 (mul_nonneg hh hh)
    have h4 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
    have e1 : (m - h) ^ (s + 1 + 2) = (m - h) * (m - h) ^ (s + 2) := by ring
    have e2 : m ^ (s + 1 + 2) = m ^ (s + 1) * m * m := by ring
    have e3 : m ^ (s + 2) = m ^ (s + 1) * m := by ring
    have e4 : m ^ (s + 1 + 1) = m ^ (s + 1) * m := by ring
    have e5 : h ^ (s + 1 + 2) = h ^ (s + 1) * h * h := by ring
    have e6 : h ^ (s + 2) = h ^ (s + 1) * h := by ring
    rw [e1, e2, e4, e5]
    rw [e3, e6] at h1
    push_cast
    have h5 : 0 ≤ (s : ℝ) * (m ^ (s + 1) * (h * h)) :=
      mul_nonneg h4 (mul_nonneg (pow_nonneg hm _) (mul_nonneg hh hh))
    have h6 : 0 ≤ m ^ (s + 1) * (h * h) := mul_nonneg (pow_nonneg hm _) (mul_nonneg hh hh)
    nlinarith

/-- Pointwise lemma: `x^r ≥ μ^r + r μ^(r-1) (x - μ) + |x - μ|^r` for `r ≥ 2`. -/
theorem pow_ge_pointwise {r : ℕ} (hr : 2 ≤ r) {x m : ℝ} (hx : 0 ≤ x) (hm : 0 ≤ m) :
    m ^ r + (r : ℝ) * m ^ (r - 1) * (x - m) + |x - m| ^ r ≤ x ^ r := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 2 := ⟨r - 2, by omega⟩
  simp only [show s + 2 - 1 = s + 1 from rfl]
  push_cast
  rcases le_total m x with hmx | hxm
  · have := pow_add_ge s hm (sub_nonneg.2 hmx)
    rw [abs_of_nonneg (sub_nonneg.2 hmx)]
    simpa using this
  · have := pow_sub_ge s (sub_nonneg.2 hxm) (show m - x ≤ m by linarith)
    rw [abs_of_nonpos (sub_nonpos.2 hxm), neg_sub]
    have e : m - (m - x) = x := by ring
    rw [e] at this
    nlinarith [this]

/-- Weighted AM-GM in the form used for interpolation. -/
theorem pow_le_amgm {x F G θ : ℝ} (hx : 0 ≤ x) (hF : 0 < F) (hG : 0 < G) (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) (a b r : ℕ) (hr1 : 1 ≤ r) (hr : (r : ℝ) = θ * a + (1 - θ) * b) :
    x ^ r ≤ F ^ θ * G ^ (1 - θ) * (θ * (x ^ a / F) + (1 - θ) * (x ^ b / G)) := by
  have hamgm := Real.geom_mean_le_arith_mean2_weighted hθ0 (sub_nonneg.2 hθ1)
    (div_nonneg (pow_nonneg hx a) hF.le) (div_nonneg (pow_nonneg hx b) hG.le) (by ring)
  have hsum : (r : ℝ) = a * θ + b * (1 - θ) := by rw [hr]; ring
  have hr1' : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hne : (a : ℝ) * θ + b * (1 - θ) ≠ 0 := by rw [← hsum]; linarith
  have hmul : x ^ ((a : ℝ) * θ) * x ^ ((b : ℝ) * (1 - θ)) = x ^ r := by
    rw [← Real.rpow_add' hx hne, ← hsum, Real.rpow_natCast]
  have hFp : 0 < F ^ θ := Real.rpow_pos_of_pos hF θ
  have hGp : 0 < G ^ (1 - θ) := Real.rpow_pos_of_pos hG _
  have hxr : x ^ r = F ^ θ * G ^ (1 - θ) *
      ((x ^ a / F) ^ θ * (x ^ b / G) ^ (1 - θ)) := by
    rw [Real.div_rpow (pow_nonneg hx a) hF.le, Real.div_rpow (pow_nonneg hx b) hG.le,
      ← Real.rpow_natCast x a, ← Real.rpow_natCast x b, ← Real.rpow_mul hx, ← Real.rpow_mul hx,
      ← hmul]
    field_simp
  rw [hxr]
  exact mul_le_mul_of_nonneg_left hamgm (mul_nonneg hFp.le hGp.le)

section Integral

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}

/-- A nonnegative measurable `X` with integrable `X^p` has integrable `X^r` for `r ≤ p`. -/
theorem integrable_pow_of_le {p r : ℕ} (hrp : r ≤ p) (hX0 : ∀ ω, 0 ≤ X ω) (hm : Measurable X)
    (hint : Integrable (fun ω => X ω ^ p) μ) : Integrable (fun ω => X ω ^ r) μ := by
  refine Integrable.mono' ((integrable_const (1 : ℝ)).add hint)
    (hm.pow_const r).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  have h0 := hX0 ω
  rw [Real.norm_of_nonneg (pow_nonneg h0 r)]
  rcases le_total (X ω) 1 with h1 | h1
  · have := pow_le_one₀ h0 h1 (n := r)
    have := pow_nonneg h0 p
    simp only [Pi.add_apply]; linarith
  · have := pow_le_pow_right₀ h1 hrp
    simp only [Pi.add_apply]; linarith

/-- A1, interpolation: `E X^r ≤ F^((p-r)/(p-1)) D^(p(r-1)/(p-1))`. -/
theorem moment_interp {p r : ℕ} (hp : 2 ≤ p) (hr1 : 1 ≤ r) (hrp : r ≤ p) {F D : ℝ}
    (hF : 0 < F) (hD : 0 < D) (hX0 : ∀ ω, 0 ≤ X ω) (hm : Measurable X)
    (hint : Integrable (fun ω => X ω ^ p) μ)
    (hEF : ∫ ω, X ω ∂μ ≤ F) (hED : ∫ ω, X ω ^ p ∂μ ≤ D ^ p) :
    ∫ ω, X ω ^ r ∂μ ≤
      F ^ (((p : ℝ) - r) / ((p : ℝ) - 1)) * D ^ ((p : ℝ) * ((r : ℝ) - 1) / ((p : ℝ) - 1)) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hr1' : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hrp' : (r : ℝ) ≤ p := by exact_mod_cast hrp
  have hpos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  set θ : ℝ := ((p : ℝ) - r) / ((p : ℝ) - 1) with hθ
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hpos.le
  have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one hpos]; linarith
  have hG : 0 < D ^ p := pow_pos hD p
  have hrθ : (r : ℝ) = θ * (1 : ℕ) + (1 - θ) * p := by
    rw [hθ]; push_cast; field_simp; ring
  have hpt : ∀ ω, X ω ^ r ≤ F ^ θ * (D ^ p) ^ (1 - θ) *
      (θ * (X ω ^ 1 / F) + (1 - θ) * (X ω ^ p / D ^ p)) := fun ω =>
    pow_le_amgm (hX0 ω) hF hG hθ0 hθ1 1 p r hr1 hrθ
  have i1 : Integrable (fun ω => X ω) μ := by
    simpa using integrable_pow_of_le (r := 1) (by omega) hX0 hm hint
  have i2 := integrable_pow_of_le hrp hX0 hm hint
  have hrhs : Integrable (fun ω => F ^ θ * (D ^ p) ^ (1 - θ) *
      (θ * (X ω ^ 1 / F) + (1 - θ) * (X ω ^ p / D ^ p))) μ := by
    simp only [pow_one]
    exact ((((i1.div_const F).const_mul θ).add ((hint.div_const _).const_mul (1 - θ))).const_mul _)
  refine (integral_mono i2 hrhs hpt).trans ?_
  have hcalc : ∫ ω, F ^ θ * (D ^ p) ^ (1 - θ) *
      (θ * (X ω ^ 1 / F) + (1 - θ) * (X ω ^ p / D ^ p)) ∂μ =
      F ^ θ * (D ^ p) ^ (1 - θ) *
        (θ * ((∫ ω, X ω ∂μ) / F) + (1 - θ) * ((∫ ω, X ω ^ p ∂μ) / D ^ p)) := by
    simp only [pow_one]
    rw [integral_const_mul, integral_add ((i1.div_const F).const_mul θ)
      ((hint.div_const _).const_mul (1 - θ)), integral_const_mul, integral_const_mul,
      integral_div, integral_div]
  rw [hcalc]
  have hC : 0 ≤ F ^ θ * (D ^ p) ^ (1 - θ) :=
    mul_nonneg (Real.rpow_nonneg hF.le _) (Real.rpow_nonneg hG.le _)
  have hb1 : (∫ ω, X ω ∂μ) / F ≤ 1 := (div_le_one hF).2 hEF
  have hb2 : (∫ ω, X ω ^ p ∂μ) / D ^ p ≤ 1 := (div_le_one hG).2 hED
  have hsum : θ * ((∫ ω, X ω ∂μ) / F) + (1 - θ) * ((∫ ω, X ω ^ p ∂μ) / D ^ p) ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_left hb1 hθ0,
      mul_le_mul_of_nonneg_left hb2 (sub_nonneg.2 hθ1)]
  have hexp : (D ^ p) ^ (1 - θ) = D ^ ((p : ℝ) * ((r : ℝ) - 1) / ((p : ℝ) - 1)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hD.le]
    congr 1; rw [hθ]; field_simp; ring
  calc _ ≤ F ^ θ * (D ^ p) ^ (1 - θ) * 1 := mul_le_mul_of_nonneg_left hsum hC
    _ = _ := by rw [mul_one, hexp]

/-- A1: `E X^r ≤ D^r` for `1 ≤ r ≤ p`. -/
theorem moment_le {p r : ℕ} (hp : 2 ≤ p) (hr1 : 1 ≤ r) (hrp : r ≤ p) {D : ℝ}
    (hD : 0 < D) (hX0 : ∀ ω, 0 ≤ X ω) (hm : Measurable X)
    (hint : Integrable (fun ω => X ω ^ p) μ) (hED : ∫ ω, X ω ^ p ∂μ ≤ D ^ p) :
    ∫ ω, X ω ^ r ∂μ ≤ D ^ r := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hrp' : (r : ℝ) ≤ p := by exact_mod_cast hrp
  set θ : ℝ := 1 - (r : ℝ) / p with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ, sub_nonneg, div_le_one hp0]; exact hrp'
  have hθ1 : θ ≤ 1 := by rw [hθ]; have : 0 ≤ (r : ℝ) / p := by positivity
                         linarith
  have hG : 0 < D ^ p := pow_pos hD p
  have hrθ : (r : ℝ) = θ * (0 : ℕ) + (1 - θ) * p := by
    rw [hθ]; push_cast; field_simp; ring
  have hpt : ∀ ω, X ω ^ r ≤ (1 : ℝ) ^ θ * (D ^ p) ^ (1 - θ) *
      (θ * (X ω ^ 0 / 1) + (1 - θ) * (X ω ^ p / D ^ p)) := fun ω =>
    pow_le_amgm (hX0 ω) one_pos hG hθ0 hθ1 0 p r hr1 hrθ
  have i2 := integrable_pow_of_le hrp hX0 hm hint
  have hrhs : Integrable (fun ω => (1 : ℝ) ^ θ * (D ^ p) ^ (1 - θ) *
      (θ * (X ω ^ 0 / 1) + (1 - θ) * (X ω ^ p / D ^ p))) μ := by
    simp only [pow_zero, div_one, mul_one]
    exact (((integrable_const θ).add ((hint.div_const _).const_mul (1 - θ))).const_mul _)
  refine (integral_mono i2 hrhs hpt).trans ?_
  have hcalc : ∫ ω, (1 : ℝ) ^ θ * (D ^ p) ^ (1 - θ) *
      (θ * (X ω ^ 0 / 1) + (1 - θ) * (X ω ^ p / D ^ p)) ∂μ =
      (1 : ℝ) ^ θ * (D ^ p) ^ (1 - θ) *
        (θ + (1 - θ) * ((∫ ω, X ω ^ p ∂μ) / D ^ p)) := by
    simp only [pow_zero, div_one, mul_one]
    rw [integral_const_mul, integral_add (integrable_const θ)
      ((hint.div_const _).const_mul (1 - θ)), integral_const_mul, integral_div]
    simp
  rw [hcalc]
  have hC : 0 ≤ (1 : ℝ) ^ θ * (D ^ p) ^ (1 - θ) :=
    mul_nonneg (Real.rpow_nonneg zero_le_one _) (Real.rpow_nonneg hG.le _)
  have hb2 : (∫ ω, X ω ^ p ∂μ) / D ^ p ≤ 1 := (div_le_one hG).2 hED
  have hsum : θ + (1 - θ) * ((∫ ω, X ω ^ p ∂μ) / D ^ p) ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_left hb2 (sub_nonneg.2 hθ1)]
  have hexp : (D ^ p) ^ (1 - θ) = D ^ r := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hD.le, ← Real.rpow_natCast]
    congr 1; rw [hθ]; field_simp; ring
  calc _ ≤ (1 : ℝ) ^ θ * (D ^ p) ^ (1 - θ) * 1 := mul_le_mul_of_nonneg_left hsum hC
    _ = _ := by rw [mul_one, hexp, Real.one_rpow, one_mul]

/-- Integrability of the centered `r`-th absolute moment, `2 ≤ r ≤ p`. -/
theorem integrable_centered_pow {p r : ℕ} (hr2 : 2 ≤ r) (hrp : r ≤ p)
    (hX0 : ∀ ω, 0 ≤ X ω) (hm : Measurable X) (hint : Integrable (fun ω => X ω ^ p) μ) :
    Integrable (fun ω => |X ω - ∫ ω', X ω' ∂μ| ^ r) μ := by
  have hm0 : 0 ≤ ∫ ω, X ω ∂μ := integral_nonneg hX0
  set m : ℝ := ∫ ω, X ω ∂μ with hmdef
  have i1 : Integrable (fun ω => X ω) μ := by
    simpa using integrable_pow_of_le (r := 1) (by omega) hX0 hm hint
  have ir := integrable_pow_of_le hrp hX0 hm hint
  have hpt : ∀ ω, |X ω - m| ^ r ≤ X ω ^ r - m ^ r - (r : ℝ) * m ^ (r - 1) * (X ω - m) := by
    intro ω; have := pow_ge_pointwise hr2 (hX0 ω) hm0 (m := m); linarith
  have hrhs : Integrable (fun ω => X ω ^ r - m ^ r - (r : ℝ) * m ^ (r - 1) * (X ω - m)) μ :=
    (ir.sub (integrable_const _)).sub ((i1.sub (integrable_const _)).const_mul _)
  refine Integrable.mono' hrhs
    ((continuous_abs.measurable.comp (hm.sub_const m)).pow_const r).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (pow_nonneg (abs_nonneg _) _)]
  exact hpt ω

/-- A1, centered moments: `E |X - E X|^r ≤ E X^r - (E X)^r` for `r ≥ 2`. -/
theorem centered_moment_le_sub {p r : ℕ} (hr2 : 2 ≤ r) (hrp : r ≤ p)
    (hX0 : ∀ ω, 0 ≤ X ω) (hm : Measurable X) (hint : Integrable (fun ω => X ω ^ p) μ) :
    ∫ ω, |X ω - ∫ ω', X ω' ∂μ| ^ r ∂μ ≤ ∫ ω, X ω ^ r ∂μ - (∫ ω, X ω ∂μ) ^ r := by
  have hm0 : 0 ≤ ∫ ω, X ω ∂μ := integral_nonneg hX0
  set m : ℝ := ∫ ω, X ω ∂μ with hmdef
  have i1 : Integrable (fun ω => X ω) μ := by
    simpa using integrable_pow_of_le (r := 1) (by omega) hX0 hm hint
  have ir := integrable_pow_of_le hrp hX0 hm hint
  have hpt : ∀ ω, |X ω - m| ^ r ≤ X ω ^ r - m ^ r - (r : ℝ) * m ^ (r - 1) * (X ω - m) := by
    intro ω; have := pow_ge_pointwise hr2 (hX0 ω) hm0 (m := m); linarith
  have hrhs : Integrable (fun ω => X ω ^ r - m ^ r - (r : ℝ) * m ^ (r - 1) * (X ω - m)) μ :=
    (ir.sub (integrable_const _)).sub ((i1.sub (integrable_const _)).const_mul _)
  have hlhs : Integrable (fun ω => |X ω - m| ^ r) μ :=
    integrable_centered_pow hr2 hrp hX0 hm hint
  refine (integral_mono hlhs hrhs hpt).trans (le_of_eq ?_)
  have A : Integrable (fun ω => X ω ^ r - m ^ r) μ := ir.sub (integrable_const _)
  have B : Integrable (fun ω => (r : ℝ) * m ^ (r - 1) * (X ω - m)) μ :=
    (i1.sub (integrable_const _)).const_mul _
  rw [integral_sub (f := fun ω => X ω ^ r - m ^ r)
    (g := fun ω => (r : ℝ) * m ^ (r - 1) * (X ω - m)) A B,
    integral_sub (f := fun ω => X ω ^ r) (g := fun _ => m ^ r) ir (integrable_const _),
    integral_const_mul, integral_sub i1 (integrable_const _)]
  simp [hmdef]

/-- A1, centered moments with the mean-sensitive cap:
`E X^r - (E X)^r ≤ D^r ϖ^((p-r)/(p-1))`, `ϖ = min (F/D) 1`. -/
theorem sub_moment_le {p r : ℕ} (hp : 2 ≤ p) (hr2 : 2 ≤ r) (hrp : r ≤ p) {F D : ℝ}
    (hF : 0 < F) (hD : 0 < D) (hX0 : ∀ ω, 0 ≤ X ω) (hm : Measurable X)
    (hint : Integrable (fun ω => X ω ^ p) μ)
    (hEF : ∫ ω, X ω ∂μ ≤ F) (hED : ∫ ω, X ω ^ p ∂μ ≤ D ^ p) :
    ∫ ω, X ω ^ r ∂μ - (∫ ω, X ω ∂μ) ^ r ≤
      D ^ r * (min (F / D) 1) ^ (((p : ℝ) - r) / ((p : ℝ) - 1)) := by
  have hm0 : 0 ≤ ∫ ω, X ω ∂μ := integral_nonneg hX0
  have hsub : ∫ ω, X ω ^ r ∂μ - (∫ ω, X ω ∂μ) ^ r ≤ ∫ ω, X ω ^ r ∂μ := by
    have := pow_nonneg hm0 r; linarith
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hr1' : (1 : ℝ) ≤ r := by exact_mod_cast (by omega : 1 ≤ r)
  have hpos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  refine hsub.trans ?_
  rcases le_total D F with hDF | hFD
  · have h1 : (1 : ℝ) ≤ F / D := (one_le_div hD).2 hDF
    rw [min_eq_right h1, Real.one_rpow, mul_one]
    exact moment_le hp (by omega) hrp hD hX0 hm hint hED
  · have h1 : F / D ≤ 1 := (div_le_one hD).2 hFD
    rw [min_eq_left h1]
    refine (moment_interp hp (by omega) hrp hF hD hX0 hm hint hEF hED).trans (le_of_eq ?_)
    set θ : ℝ := ((p : ℝ) - r) / ((p : ℝ) - 1) with hθ
    rw [Real.div_rpow hF.le hD.le, ← mul_div_assoc, eq_div_iff (Real.rpow_pos_of_pos hD θ).ne']
    have : D ^ ((p : ℝ) * ((r : ℝ) - 1) / ((p : ℝ) - 1)) * D ^ θ = D ^ r := by
      rw [← Real.rpow_add hD, ← Real.rpow_natCast]
      congr 1; rw [hθ]; field_simp; ring
    rw [mul_assoc, this]; ring

/-- A1 in the form used for averaging: with `T ≥ ϖ^(p/(p-1))`, `T > 0`,
`E |X - E X|^r ≤ D^r T^((p-r)/p)` for `2 ≤ r ≤ p`. -/
theorem centered_moment_le_T {p r : ℕ} (hp : 2 ≤ p) (hr2 : 2 ≤ r) (hrp : r ≤ p) {F D T : ℝ}
    (hF : 0 < F) (hD : 0 < D) (hX0 : ∀ ω, 0 ≤ X ω) (hm : Measurable X)
    (hint : Integrable (fun ω => X ω ^ p) μ)
    (hEF : ∫ ω, X ω ∂μ ≤ F) (hED : ∫ ω, X ω ^ p ∂μ ≤ D ^ p)
    (hT : (min (F / D) 1) ^ ((p : ℝ) / ((p : ℝ) - 1)) ≤ T) :
    ∫ ω, |X ω - ∫ ω', X ω' ∂μ| ^ r ∂μ ≤ D ^ r * T ^ (((p : ℝ) - r) / p) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hrp' : (r : ℝ) ≤ p := by exact_mod_cast hrp
  have hpos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hp0 : (0 : ℝ) < p := by linarith
  have hϖ : 0 ≤ min (F / D) 1 := le_min (div_nonneg hF.le hD.le) zero_le_one
  have h1 := (centered_moment_le_sub (p := p) hr2 hrp hX0 hm hint).trans
    (sub_moment_le hp hr2 hrp hF hD hX0 hm hint hEF hED)
  refine h1.trans ?_
  gcongr
  have he : 0 ≤ ((p : ℝ) - r) / p := div_nonneg (by linarith) hp0.le
  calc (min (F / D) 1) ^ (((p : ℝ) - r) / ((p : ℝ) - 1))
      = ((min (F / D) 1) ^ ((p : ℝ) / ((p : ℝ) - 1))) ^ (((p : ℝ) - r) / p) := by
        rw [← Real.rpow_mul hϖ]; congr 1; field_simp
    _ ≤ T ^ (((p : ℝ) - r) / p) := Real.rpow_le_rpow (Real.rpow_nonneg hϖ _) hT he

end Integral

end GMCExplicitDelta.Averaging
