module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Convex.Deriv

/-!
# The scalar functions `𝗑` and `Φ` (C6, C7)

`xfun θ = 1 + θ + √(θ(θ+2))` is the larger root of `y + y⁻¹ = 2 + 2θ`;
`phi t j = (1+j) cosh t - 1 + √(j(j+2)) sinh t`.
-/

@[expose] public section

open Real

namespace GMCExplicitDelta.Coarse

/-- `𝗑(θ) = 1 + θ + √(θ(θ+2))`. -/
noncomputable def xfun (θ : ℝ) : ℝ := 1 + θ + √(θ * (θ + 2))

/-- `Φ_t(j) = (1+j) cosh t - 1 + √(j(j+2)) sinh t`. -/
noncomputable def phi (t j : ℝ) : ℝ := (1 + j) * cosh t - 1 + √(j * (j + 2)) * sinh t

/-! ### `𝗑` -/

@[simp] theorem xfun_zero : xfun 0 = 1 := by simp [xfun]

theorem one_le_xfun {θ : ℝ} (hθ : 0 ≤ θ) : 1 ≤ xfun θ := by
  unfold xfun
  have := Real.sqrt_nonneg (θ * (θ + 2))
  linarith

theorem xfun_pos {θ : ℝ} (hθ : 0 ≤ θ) : 0 < xfun θ := lt_of_lt_of_le one_pos (one_le_xfun hθ)

theorem xfun_mul_inv_form {θ : ℝ} (hθ : 0 ≤ θ) :
    xfun θ * (1 + θ - √(θ * (θ + 2))) = 1 := by
  unfold xfun
  have h : √(θ * (θ + 2)) ^ 2 = θ * (θ + 2) := Real.sq_sqrt (by positivity)
  nlinarith [h]

theorem xfun_add_inv {θ : ℝ} (hθ : 0 ≤ θ) : xfun θ + (xfun θ)⁻¹ = 2 + 2 * θ := by
  have h := xfun_mul_inv_form hθ
  have hinv : (xfun θ)⁻¹ = 1 + θ - √(θ * (θ + 2)) := inv_eq_of_mul_eq_one_right h
  rw [hinv]; unfold xfun; ring

theorem le_of_add_inv_le {y M : ℝ} (hy : 1 ≤ y) (hM : 1 ≤ M) (h : y + y⁻¹ ≤ M + M⁻¹) :
    y ≤ M := by
  by_contra hlt
  rw [not_le] at hlt
  have hy0 : 0 < y := by linarith
  have hM0 : 0 < M := by linarith
  have e : y + y⁻¹ - (M + M⁻¹) = (y - M) * (y * M - 1) / (y * M) := by
    field_simp
    ring
  have : 0 < (y - M) * (y * M - 1) / (y * M) := by
    apply div_pos _ (by positivity)
    apply mul_pos (by linarith)
    nlinarith
  linarith

/-- If `s + s⁻¹ ≤ 2 + 2θ` then `𝗑(θ)⁻¹ ≤ s ≤ 𝗑(θ)`. -/
theorem xfun_bounds {θ s : ℝ} (hθ : 0 ≤ θ) (hs : 0 < s) (h : s + s⁻¹ ≤ 2 + 2 * θ) :
    (xfun θ)⁻¹ ≤ s ∧ s ≤ xfun θ := by
  have key : ∀ s : ℝ, 0 < s → s + s⁻¹ ≤ 2 + 2 * θ → s ≤ xfun θ := by
    intro s hs h
    by_cases hs1 : 1 ≤ s
    · apply le_of_add_inv_le hs1 (one_le_xfun hθ)
      rw [xfun_add_inv hθ]; exact h
    · exact le_trans (not_le.mp hs1).le (one_le_xfun hθ)
  refine ⟨?_, key s hs h⟩
  have h2 := key s⁻¹ (inv_pos.mpr hs) (by simpa [add_comm] using h)
  have h3 := inv_anti₀ (inv_pos.mpr hs) h2
  simpa using h3

theorem xfun_monotoneOn : MonotoneOn xfun (Set.Ici 0) := by
  intro a ha b hb hab
  have ha' : 0 ≤ a := ha
  unfold xfun
  have : √(a * (a + 2)) ≤ √(b * (b + 2)) := Real.sqrt_le_sqrt (by nlinarith)
  linarith

/-- Tangent-line bound for `g θ = √(θ(θ+2))`. -/
theorem sqrt_mul_sqrt_le {θ θ0 : ℝ} (hθ : 0 ≤ θ) (hθ0 : 0 ≤ θ0) :
    √(θ * (θ + 2)) * √(θ0 * (θ0 + 2)) ≤ (θ0 + 1) * (θ + 1) - 1 := by
  rw [← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_iff.mpr
  constructor
  · nlinarith [mul_nonneg hθ hθ0]
  · nlinarith [sq_nonneg (θ - θ0)]

theorem xfun_concaveOn : ConcaveOn ℝ (Set.Ici (0 : ℝ)) xfun := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx' : 0 ≤ x := hx
  have hy' : 0 ≤ y := hy
  set w := a * x + b * y with hw
  have hw0 : 0 ≤ w := by positivity
  simp only [smul_eq_mul]
  have hxf : ∀ θ : ℝ, xfun θ = 1 + θ + √(θ * (θ + 2)) := fun _ => rfl
  rw [hxf, hxf, hxf]
  have hlin : a * (1 + x) + b * (1 + y) = 1 + w := by rw [hw]; nlinarith
  suffices h : a * √(x * (x + 2)) + b * √(y * (y + 2)) ≤ √(w * (w + 2)) by nlinarith
  set gw := √(w * (w + 2)) with hgw
  have hgw0 : 0 ≤ gw := Real.sqrt_nonneg _
  have hgw2 : gw * gw = w * (w + 2) := Real.mul_self_sqrt (by positivity)
  by_cases hpos : 0 < gw
  · have t1 := sqrt_mul_sqrt_le hx' hw0
    have t2 := sqrt_mul_sqrt_le hy' hw0
    have hsum : (a * √(x * (x + 2)) + b * √(y * (y + 2))) * gw ≤ gw * gw := by
      have := mul_le_mul_of_nonneg_left t1 ha
      have := mul_le_mul_of_nonneg_left t2 hb
      nlinarith
    exact le_of_mul_le_mul_right (by linarith) hpos
  · have hz : gw = 0 := le_antisymm (not_lt.mp hpos) hgw0
    have hw00 : w * (w + 2) = 0 := by rw [← hgw2, hz]; ring
    have hw1 : w = 0 := by nlinarith
    have hax : a * x = 0 := by nlinarith [mul_nonneg ha hx', mul_nonneg hb hy']
    have hby : b * y = 0 := by nlinarith [mul_nonneg ha hx', mul_nonneg hb hy']
    have hx0 : a = 0 ∨ x = 0 := mul_eq_zero.mp hax
    have hy0 : b = 0 ∨ y = 0 := mul_eq_zero.mp hby
    rw [hz]
    rcases hx0 with h | h <;> rcases hy0 with h' | h' <;> simp [h, h']

theorem xfun_theta (R : ℝ) (hR : 1 ≤ R) : xfun ((R + R⁻¹ - 2) / 2) = R := by
  have hR0 : 0 < R := by linarith
  have hθ : 0 ≤ (R + R⁻¹ - 2) / 2 := by
    have : R⁻¹ ≥ 2 - R := by
      have := mul_inv_cancel₀ hR0.ne'
      nlinarith [inv_pos.mpr hR0, sq_nonneg (R - 1)]
    linarith
  have hsq : (R + R⁻¹ - 2) / 2 * ((R + R⁻¹ - 2) / 2 + 2) = ((R - R⁻¹) / 2) ^ 2 := by
    have : R * R⁻¹ = 1 := mul_inv_cancel₀ hR0.ne'
    nlinarith [this]
  have hge : 0 ≤ (R - R⁻¹) / 2 := by
    have : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR
    linarith
  unfold xfun
  rw [hsq, Real.sqrt_sq hge]
  ring

theorem xfun_theta_mul_le {R q : ℝ} (hR : 1 ≤ R) (hq : 1 ≤ q) :
    xfun ((R + R⁻¹ - 2) / 2 * q) ≤ R * q := by
  have hR0 : 0 < R := by linarith
  have hq0 : 0 < q := by linarith
  have hθ : 0 ≤ (R + R⁻¹ - 2) / 2 := by
    have : R⁻¹ ≥ 2 - R := by
      have := mul_inv_cancel₀ hR0.ne'
      nlinarith [inv_pos.mpr hR0, sq_nonneg (R - 1)]
    linarith
  have hθq : 0 ≤ (R + R⁻¹ - 2) / 2 * q := by positivity
  have hRq : 1 ≤ R * q := by nlinarith
  apply le_of_add_inv_le (one_le_xfun hθq) hRq
  rw [xfun_add_inv hθq]
  have e : R * q + (R * q)⁻¹ - (2 + 2 * ((R + R⁻¹ - 2) / 2 * q)) =
      (q - 1) * (2 * R * q - 1 - q) / (R * q) := by
    field_simp
    ring
  have : 0 ≤ (q - 1) * (2 * R * q - 1 - q) / (R * q) := by
    apply div_nonneg _ (by positivity)
    apply mul_nonneg (by linarith)
    nlinarith
  linarith

/-! ### `Φ` -/

theorem phi_zero_right (t : ℝ) : phi t 0 = cosh t - 1 := by simp [phi]

theorem phi_mono_j {t : ℝ} (ht : 0 ≤ t) : MonotoneOn (phi t) (Set.Ici 0) := by
  intro a ha b hb hab
  have ha' : 0 ≤ a := ha
  unfold phi
  have h1 : √(a * (a + 2)) ≤ √(b * (b + 2)) := Real.sqrt_le_sqrt (by nlinarith)
  have hc : 0 ≤ cosh t := (Real.cosh_pos t).le
  have hs : 0 ≤ sinh t := Real.sinh_nonneg_iff.mpr ht
  nlinarith [mul_le_mul_of_nonneg_right h1 hs, mul_le_mul_of_nonneg_right hab hc]

theorem phi_mono_t {j : ℝ} (hj : 0 ≤ j) : MonotoneOn (fun t => phi t j) (Set.Ici 0) := by
  intro a ha b hb hab
  have ha' : 0 ≤ a := ha
  have hc : cosh a ≤ cosh b := Real.cosh_le_cosh.mpr (by
    rw [abs_of_nonneg ha', abs_of_nonneg (le_trans ha' hab)]; exact hab)
  have hs : sinh a ≤ sinh b := Real.sinh_le_sinh.mpr hab
  have hK : 0 ≤ √(j * (j + 2)) := Real.sqrt_nonneg _
  show phi a j ≤ phi b j
  unfold phi
  nlinarith [mul_le_mul_of_nonneg_left hc (by linarith : (0 : ℝ) ≤ 1 + j),
    mul_le_mul_of_nonneg_left hs hK]

theorem phi_nonneg {t j : ℝ} (hj : 0 ≤ j) (ht : 0 ≤ t) : 0 ≤ phi t j := by
  unfold phi
  have hc : 1 ≤ cosh t := Real.one_le_cosh t
  have hs : 0 ≤ sinh t := Real.sinh_nonneg_iff.mpr ht
  have hK : 0 ≤ √(j * (j + 2)) := Real.sqrt_nonneg _
  nlinarith [mul_nonneg hK hs]

/-- Convexity bound `cosh(λ t) - 1 ≤ λ (cosh t - 1)`. -/
theorem cosh_mul_sub_one_le {l t : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    cosh (l * t) - 1 ≤ l * (cosh t - 1) := by
  have h1 := convexOn_exp.2 (Set.mem_univ t) (Set.mem_univ 0) hl0 (by linarith : 0 ≤ 1 - l)
    (by ring)
  have h2 := convexOn_exp.2 (Set.mem_univ (-t)) (Set.mem_univ 0) hl0 (by linarith : 0 ≤ 1 - l)
    (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at h1 h2
  rw [Real.cosh_eq, Real.cosh_eq]
  have e1 : l * -t = -(l * t) := by ring
  rw [e1] at h2
  nlinarith

/-- `sinh(λ t) ≤ λ sinh t` for `t ≥ 0`, `λ ∈ [0,1]`. -/
theorem sinh_mul_le {l t : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (ht : 0 ≤ t) :
    sinh (l * t) ≤ l * sinh t := by
  let f : ℝ → ℝ := fun s => l * sinh s - sinh (l * s)
  have hd : ∀ s, HasDerivAt f (l * cosh s - cosh (l * s) * l) s := by
    intro s
    have h1 : HasDerivAt (fun s => l * sinh s) (l * cosh s) s :=
      (Real.hasDerivAt_sinh s).const_mul l
    have h2 : HasDerivAt (fun s => sinh (l * s)) (cosh (l * s) * l) s := by
      have := ((hasDerivAt_id s).const_mul l).sinh
      simpa using this
    exact h1.sub h2
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact (fun s _ => (hd s).continuousAt.continuousWithinAt)
    · exact (fun s _ => (hd s).differentiableAt.differentiableWithinAt)
    · intro s hs
      rw [interior_Ici] at hs
      have hs0 : 0 ≤ s := le_of_lt hs
      rw [(hd s).deriv]
      have : cosh (l * s) ≤ cosh s := Real.cosh_le_cosh.mpr (by
        rw [abs_of_nonneg (by positivity), abs_of_nonneg hs0]; nlinarith)
      nlinarith
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  simp [f] at this
  linarith

theorem phi_scale {l t j : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (ht : 0 ≤ t) (hj : 0 ≤ j) :
    phi (l * t) (l * j) ≤ l * phi t j := by
  have hlt : 0 ≤ l * t := by positivity
  have hlj : 0 ≤ l * j := by positivity
  have hc := cosh_mul_sub_one_le (t := t) hl0 hl1
  have hs := sinh_mul_le hl0 hl1 ht
  have hcm : cosh (l * t) ≤ cosh t := Real.cosh_le_cosh.mpr (by
    rw [abs_of_nonneg hlt, abs_of_nonneg ht]; nlinarith)
  have hK : √(l * j * (l * j + 2)) ≤ √(j * (j + 2)) :=
    Real.sqrt_le_sqrt (by
      have h1 : 0 ≤ j * j * (1 - l * l) := mul_nonneg (mul_self_nonneg j) (by nlinarith)
      have h2 : 0 ≤ j * (1 - l) := mul_nonneg hj (by linarith)
      nlinarith [h1, h2])
  have hK0 : 0 ≤ √(l * j * (l * j + 2)) := Real.sqrt_nonneg _
  have hK1 : 0 ≤ √(j * (j + 2)) := Real.sqrt_nonneg _
  have hs0 : 0 ≤ sinh t := Real.sinh_nonneg_iff.mpr ht
  have hs1 : 0 ≤ sinh (l * t) := Real.sinh_nonneg_iff.mpr hlt
  unfold phi
  have a1 : √(l * j * (l * j + 2)) * sinh (l * t) ≤ √(j * (j + 2)) * (l * sinh t) :=
    mul_le_mul hK hs hs1 hK1
  have a2 : l * j * cosh (l * t) ≤ l * j * cosh t :=
    mul_le_mul_of_nonneg_left hcm hlj
  nlinarith [a1, a2]

/-- The two-point rescaling bound: `½(e^c α + e^{-c} β) - 1 ≤ Φ_{|c|}(½(α+β) - 1)` when `αβ ≥ 1`. -/
theorem half_exp_le_phi {α β : ℝ} (hαβ : 1 ≤ α * β) (c : ℝ) :
    (1 / 2) * (exp c * α + exp (-c) * β) - 1 ≤ phi |c| ((α + β) / 2 - 1) := by
  set j := (α + β) / 2 - 1 with hj
  have hK2 : ((α - β) / 2) ^ 2 ≤ j * (j + 2) := by rw [hj]; nlinarith [sq_nonneg (α - β)]
  have hu : |(α - β) / 2| ≤ √(j * (j + 2)) := Real.abs_le_sqrt hK2
  have hcosh : cosh |c| = cosh c := Real.cosh_abs c
  have hsinh : |sinh c| = sinh |c| := by
    rcases le_total 0 c with h | h
    · rw [abs_of_nonneg h, abs_of_nonneg (Real.sinh_nonneg_iff.mpr h)]
    · rw [abs_of_nonpos h, Real.sinh_neg, abs_of_nonpos (Real.sinh_nonpos_iff.mpr h)]
  have e : (1 / 2) * (exp c * α + exp (-c) * β) - 1 =
      (1 + j) * cosh c - 1 + (α - β) / 2 * sinh c := by
    rw [hj, Real.cosh_eq, Real.sinh_eq]; ring
  rw [e]; unfold phi; rw [hcosh]
  have : (α - β) / 2 * sinh c ≤ √(j * (j + 2)) * sinh |c| := by
    calc _ ≤ |(α - β) / 2 * sinh c| := le_abs_self _
      _ = |(α - β) / 2| * |sinh c| := abs_mul _ _
      _ ≤ √(j * (j + 2)) * |sinh c| := by gcongr
      _ = _ := by rw [hsinh]
  linarith

end GMCExplicitDelta.Coarse
