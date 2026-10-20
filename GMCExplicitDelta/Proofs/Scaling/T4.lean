module

public import GMCExplicitDelta.Contract.DerivedBarrier
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# T4: the planar all-λ derivative test

Calculus part: derivatives of `𝗋(λu)`, `𝗊(λu)` and `√((v₀+λv₁)/𝗋(λu))`.
-/

@[expose] public section

open Real

namespace GMCExplicitDelta.Contract

theorem rMatch_pos {μ : ℝ} (h : 0 ≤ μ) : 0 < rMatch μ := by unfold rMatch; positivity

theorem cMatch_pos (μ : ℝ) : 0 < cMatch μ := by unfold cMatch; nlinarith [sq_nonneg (μ + 1)]

theorem qMatch_pos {μ : ℝ} (h : 0 ≤ μ) : 0 < qMatch μ := by
  unfold qMatch; exact div_pos (cMatch_pos μ) (rMatch_pos h)

theorem hasDerivAt_rMatch (μ : ℝ) : HasDerivAt rMatch (3 / 2 + μ) μ := by
  unfold rMatch
  have h := ((hasDerivAt_id μ).const_add 1).mul (((hasDerivAt_id μ).div_const 2).const_add 1)
  refine h.congr_deriv ?_
  simp; ring

theorem hasDerivAt_cMatch (μ : ℝ) : HasDerivAt cMatch (1 + μ) μ := by
  unfold cMatch
  have h := (((hasDerivAt_id μ).const_add 1).add (((hasDerivAt_id μ).pow 2).div_const 2))
  refine h.congr_deriv ?_
  simp

theorem hasDerivAt_qMatch (μ : ℝ) (hr : rMatch μ ≠ 0) :
    HasDerivAt qMatch (-(1 - μ ^ 2 / 2) / (2 * rMatch μ ^ 2)) μ := by
  have h := HasDerivAt.fun_div (hasDerivAt_cMatch μ) (hasDerivAt_rMatch μ) hr
  refine h.congr_deriv ?_
  unfold rMatch cMatch
  have : (1 + μ) * ((1 + μ) * (1 + μ / 2)) = (1 + μ) * ((1 + μ) * (1 + μ / 2)) := rfl
  field_simp
  ring

/-! ### Monotone ingredients -/

theorem t4_Nh_mono {u l v0 v1 : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) (hl0 : 0 < l) (hl1 : l ≤ 1)
    (h0 : 0 ≤ v0) (hn : 0 ≤ v1 * (1 - u ^ 2 / 2) - v0 * u * (3 / 2 + u)) :
    (v1 * (1 - u ^ 2 / 2) - v0 * u * (3 / 2 + u)) / (1 - u ^ 2 / 2) ≤
      (v1 * (1 - (l * u) ^ 2 / 2) - v0 * u * (3 / 2 + l * u)) / (1 - (l * u) ^ 2 / 2) := by
  have hz : l * u ≤ u := by nlinarith
  have hz0 : 0 ≤ l * u := by positivity
  have hh1 : 0 < 1 - u ^ 2 / 2 := by nlinarith
  have hh : 0 < 1 - (l * u) ^ 2 / 2 := by nlinarith
  have e1 : ∀ w : ℝ, 0 < 1 - w ^ 2 / 2 →
      (v1 * (1 - w ^ 2 / 2) - v0 * u * (3 / 2 + w)) / (1 - w ^ 2 / 2) =
        v1 - v0 * u * ((3 / 2 + w) / (1 - w ^ 2 / 2)) := by
    intro w hw
    rw [sub_div, mul_div_cancel_right₀ _ hw.ne']; ring
  rw [e1 u hh1, e1 (l * u) hh]
  have hK : (3 / 2 + l * u) / (1 - (l * u) ^ 2 / 2) ≤ (3 / 2 + u) / (1 - u ^ 2 / 2) := by
    rw [div_le_div_iff₀ hh hh1]
    have : (3 / 2 + u) * (1 - (l * u) ^ 2 / 2) - (3 / 2 + l * u) * (1 - u ^ 2 / 2) =
        (u - l * u) * (1 + 3 * (u + l * u) / 4 + u * (l * u) / 2) := by ring
    have h2 : 0 ≤ (u - l * u) * (1 + 3 * (u + l * u) / 4 + u * (l * u) / 2) :=
      mul_nonneg (by linarith) (by positivity)
    nlinarith
  have := mul_le_mul_of_nonneg_left hK (mul_nonneg h0 hu0.le)
  linarith

theorem t4_ratio_mono {u l v0 v1 : ℝ} (hu0 : 0 < u) (hl1 : l ≤ 1) (hl0 : 0 < l)
    (h0 : 0 ≤ v0) (h1 : 0 ≤ v1) (hn : 0 ≤ v1 * (1 - u ^ 2 / 2) - v0 * u * (3 / 2 + u)) :
    (v0 + l * v1) / rMatch (l * u) ≤ (v0 + v1) / rMatch u := by
  have hr1 : 0 < rMatch u := rMatch_pos hu0.le
  have hr : 0 < rMatch (l * u) := rMatch_pos (by positivity)
  rw [div_le_div_iff₀ hr hr1]
  unfold rMatch
  have : (v0 + v1) * ((1 + l * u) * (1 + l * u / 2)) - (v0 + l * v1) * ((1 + u) * (1 + u / 2)) =
      (1 - l) * ((v1 * (1 - u ^ 2 / 2) - v0 * u * (3 / 2 + u)) +
        (1 - l) * u ^ 2 * (v0 + v1) / 2) := by ring
  have h2 : 0 ≤ (1 - l) * ((v1 * (1 - u ^ 2 / 2) - v0 * u * (3 / 2 + u)) +
        (1 - l) * u ^ 2 * (v0 + v1) / 2) :=
    mul_nonneg (by linarith) (by
      have : 0 ≤ (1 - l) * u ^ 2 * (v0 + v1) / 2 :=
        div_nonneg (mul_nonneg (mul_nonneg (by linarith) (sq_nonneg u)) (by linarith)) (by norm_num)
      linarith)
  nlinarith

theorem t4_q_anti {u l : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) (hl1 : l ≤ 1) (hl0 : 0 < l) :
    qMatch u ≤ qMatch (l * u) := by
  have hr1 : 0 < rMatch u := rMatch_pos hu0.le
  have hr : 0 < rMatch (l * u) := rMatch_pos (by positivity)
  unfold qMatch
  rw [div_le_div_iff₀ hr1 hr]
  unfold rMatch cMatch
  have : (1 + l * u + (l * u) ^ 2 / 2) * ((1 + u) * (1 + u / 2)) -
      (1 + u + u ^ 2 / 2) * ((1 + l * u) * (1 + l * u / 2)) =
      u / 2 * ((1 - l) * (1 - l * u ^ 2 / 2)) := by ring
  have h2 : 0 ≤ u / 2 * ((1 - l) * (1 - l * u ^ 2 / 2)) :=
    mul_nonneg (by positivity) (mul_nonneg (by linarith) (by nlinarith))
  nlinarith

theorem t4_W1_eq {sr sVt sVf r h u a b c L nt nf sq : ℝ} (hr : r = sr ^ 2) (hsr : 0 < sr)
    (hVt : 0 < sVt) (hVf : 0 < sVf) (hh : 0 < h) (hsq : 0 < sq) :
    b * (nt / h) / (sVt / sr) + c * (nf / h) / (sVf / sr) - a * u / (2 * sq) - L * u =
      2 * r ^ 2 / h * (b * (nt / (2 * sVt * (r * sr))) + c * (nf / (2 * sVf * (r * sr))) -
        h / r ^ 2 * (a * u / (4 * sq) + L * u / 2)) := by
  subst hr
  field_simp
  ring

/-! ### Derivatives -/

theorem t4_hasDerivAt_q {u l : ℝ} (hl : 0 < l) (hu : 0 ≤ u) :
    HasDerivAt (fun x => qMatch (x * u)) (-(u * (1 - (l * u) ^ 2 / 2)) / (2 * rMatch (l * u) ^ 2)) l := by
  have hr : rMatch (l * u) ≠ 0 := (rMatch_pos (by positivity)).ne'
  have := (hasDerivAt_qMatch (l * u) hr).comp l ((hasDerivAt_id l).mul_const u)
  refine this.congr_deriv ?_
  ring

theorem t4_hasDerivAt_s {u l v0 v1 : ℝ} (hl : 0 < l) (hu : 0 ≤ u) (hV : 0 < v0 + l * v1) :
    HasDerivAt (fun x => √((v0 + x * v1) / rMatch (x * u)))
      ((v1 * (1 - (l * u) ^ 2 / 2) - v0 * u * (3 / 2 + l * u)) / rMatch (l * u) ^ 2 /
        (2 * √((v0 + l * v1) / rMatch (l * u)))) l := by
  have hr0 : 0 < rMatch (l * u) := rMatch_pos (by positivity)
  have hV' : HasDerivAt (fun x => v0 + x * v1) v1 l := by
    simpa using ((hasDerivAt_id l).mul_const v1).const_add v0
  have hR : HasDerivAt (fun x => rMatch (x * u)) ((3 / 2 + l * u) * u) l := by
    have := (hasDerivAt_rMatch (l * u)).comp l ((hasDerivAt_id l).mul_const u)
    refine this.congr_deriv ?_
    ring
  have hD := HasDerivAt.fun_div hV' hR hr0.ne'
  have hS := hD.sqrt (div_pos hV hr0).ne'
  refine hS.congr_deriv ?_
  congr 1
  unfold rMatch
  ring

/-! ### The derivative is nonnegative -/

theorem t4_nMatch_eq (v0 v1 u : ℝ) :
    nMatch v0 v1 u = v1 * (1 - u ^ 2 / 2) - v0 * u * (3 / 2 + u) := by
  unfold nMatch; ring

/-- The nonnegativity of `W'` at `λ = 1`, from the derivative test (S). -/
theorem t4_W1_nonneg {u a b c L v0t v1t v0f v1f : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hL : 0 ≤ L)
    (hpt : 0 < v0t + v1t) (hpf : 0 < v0f + v1f)
    (hS : (1 - u ^ 2 / 2) / rMatch u ^ 2 * (a * u / (4 * √(qMatch u)) + L * u / 2) ≤
      b * mMatch v0t v1t u + c * mMatch v0f v1f u) :
    0 ≤ b * (nMatch v0t v1t u / (1 - u ^ 2 / 2)) / √((v0t + v1t) / rMatch u) +
      c * (nMatch v0f v1f u / (1 - u ^ 2 / 2)) / √((v0f + v1f) / rMatch u) -
      a * u / (2 * √(qMatch u)) - L * u := by
  have hr1 : 0 < rMatch u := rMatch_pos hu0.le
  have hh1 : 0 < 1 - u ^ 2 / 2 := by nlinarith
  have hq1 : 0 < √(qMatch u) := Real.sqrt_pos.mpr (qMatch_pos hu0.le)
  have hsr : 0 < √(rMatch u) := Real.sqrt_pos.mpr hr1
  have hVt : 0 < √(v0t + v1t) := Real.sqrt_pos.mpr hpt
  have hVf : 0 < √(v0f + v1f) := Real.sqrt_pos.mpr hpf
  rw [Real.sqrt_div hpt.le, Real.sqrt_div hpf.le]
  have key := t4_W1_eq (sr := √(rMatch u)) (sVt := √(v0t + v1t)) (sVf := √(v0f + v1f))
    (r := rMatch u) (h := 1 - u ^ 2 / 2) (u := u) (a := a) (b := b) (c := c) (L := L)
    (nt := nMatch v0t v1t u) (nf := nMatch v0f v1f u) (sq := √(qMatch u))
    (Real.sq_sqrt hr1.le).symm hsr hVt hVf hh1 hq1
  rw [key]
  apply mul_nonneg (by positivity)
  unfold mMatch at hS
  have : (1 - u ^ 2 / 2) / rMatch u ^ 2 * (a * u / (4 * √(qMatch u)) + L * u / 2) ≤
      b * (nMatch v0t v1t u / (2 * √(v0t + v1t) * (rMatch u * √(rMatch u)))) +
        c * (nMatch v0f v1f u / (2 * √(v0f + v1f) * (rMatch u * √(rMatch u)))) := hS
  linarith

theorem t4_E_nonneg {u l a b c L v0t v1t v0f v1f : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1)
    (hl0 : 0 < l) (hl1 : l ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hL : 0 ≤ L)
    (h0t : 0 ≤ v0t) (h1t : 0 ≤ v1t) (h0f : 0 ≤ v0f) (h1f : 0 ≤ v1f)
    (hpt : 0 < v0t + v1t) (hpf : 0 < v0f + v1f)
    (hnt : 0 ≤ nMatch v0t v1t u) (hnf : 0 ≤ nMatch v0f v1f u)
    (hS : (1 - u ^ 2 / 2) / rMatch u ^ 2 * (a * u / (4 * √(qMatch u)) + L * u / 2) ≤
      b * mMatch v0t v1t u + c * mMatch v0f v1f u) :
    0 ≤ a * (-(u * (1 - (l * u) ^ 2 / 2)) / (2 * rMatch (l * u) ^ 2) /
          (2 * √(qMatch (l * u)))) +
      b * ((v1t * (1 - (l * u) ^ 2 / 2) - v0t * u * (3 / 2 + l * u)) / rMatch (l * u) ^ 2 /
        (2 * √((v0t + l * v1t) / rMatch (l * u)))) +
      c * ((v1f * (1 - (l * u) ^ 2 / 2) - v0f * u * (3 / 2 + l * u)) / rMatch (l * u) ^ 2 /
        (2 * √((v0f + l * v1f) / rMatch (l * u)))) +
      L * (-(u * (1 - (l * u) ^ 2 / 2)) / (2 * rMatch (l * u) ^ 2)) := by
  have hz0 : 0 ≤ l * u := by positivity
  have hz1 : l * u ≤ 1 := by nlinarith
  have hr : 0 < rMatch (l * u) := rMatch_pos hz0
  have hr1 : 0 < rMatch u := rMatch_pos hu0.le
  have hh : 0 < 1 - (l * u) ^ 2 / 2 := by nlinarith
  have hh1 : 0 < 1 - u ^ 2 / 2 := by nlinarith
  have hq : 0 < √(qMatch (l * u)) := Real.sqrt_pos.mpr (qMatch_pos hz0)
  have hq1 : 0 < √(qMatch u) := Real.sqrt_pos.mpr (qMatch_pos hu0.le)
  have hVt : 0 < v0t + l * v1t := by nlinarith
  have hVf : 0 < v0f + l * v1f := by nlinarith
  have hst : 0 < √((v0t + l * v1t) / rMatch (l * u)) := Real.sqrt_pos.mpr (div_pos hVt hr)
  have hsf : 0 < √((v0f + l * v1f) / rMatch (l * u)) := Real.sqrt_pos.mpr (div_pos hVf hr)
  have hst1 : 0 < √((v0t + v1t) / rMatch u) := Real.sqrt_pos.mpr (div_pos hpt hr1)
  have hsf1 : 0 < √((v0f + v1f) / rMatch u) := Real.sqrt_pos.mpr (div_pos hpf hr1)
  set Nt := v1t * (1 - (l * u) ^ 2 / 2) - v0t * u * (3 / 2 + l * u) with hNt
  set Nf := v1f * (1 - (l * u) ^ 2 / 2) - v0f * u * (3 / 2 + l * u) with hNf
  have hnt' := t4_nMatch_eq v0t v1t u
  have hnf' := t4_nMatch_eq v0f v1f u
  rw [hnt'] at hnt
  rw [hnf'] at hnf
  have mt := t4_Nh_mono hu0 hu1 hl0 hl1 h0t hnt
  have mf := t4_Nh_mono hu0 hu1 hl0 hl1 h0f hnf
  have n0t : 0 ≤ (v1t * (1 - u ^ 2 / 2) - v0t * u * (3 / 2 + u)) / (1 - u ^ 2 / 2) :=
    div_nonneg hnt hh1.le
  have n0f : 0 ≤ (v1f * (1 - u ^ 2 / 2) - v0f * u * (3 / 2 + u)) / (1 - u ^ 2 / 2) :=
    div_nonneg hnf hh1.le
  have st_le := Real.sqrt_le_sqrt (t4_ratio_mono hu0 hl1 hl0 h0t h1t hnt)
  have sf_le := Real.sqrt_le_sqrt (t4_ratio_mono hu0 hl1 hl0 h0f h1f hnf)
  have tt : (v1t * (1 - u ^ 2 / 2) - v0t * u * (3 / 2 + u)) / (1 - u ^ 2 / 2) /
        √((v0t + v1t) / rMatch u) ≤ Nt / (1 - (l * u) ^ 2 / 2) / √((v0t + l * v1t) / rMatch (l * u)) :=
    div_le_div₀ (n0t.trans mt) mt hst st_le
  have tf : (v1f * (1 - u ^ 2 / 2) - v0f * u * (3 / 2 + u)) / (1 - u ^ 2 / 2) /
        √((v0f + v1f) / rMatch u) ≤ Nf / (1 - (l * u) ^ 2 / 2) / √((v0f + l * v1f) / rMatch (l * u)) :=
    div_le_div₀ (n0f.trans mf) mf hsf sf_le
  have qq : √(qMatch u) ≤ √(qMatch (l * u)) :=
    Real.sqrt_le_sqrt (t4_q_anti hu0 hu1 hl1 hl0)
  have aa : a * u / (2 * √(qMatch (l * u))) ≤ a * u / (2 * √(qMatch u)) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have W1 := t4_W1_nonneg (a := a) (b := b) (c := c) (L := L) hu0 hu1 ha hb hc hL hpt hpf hS
  rw [hnt', hnf'] at W1
  have mul_b := mul_le_mul_of_nonneg_left tt hb
  have mul_c := mul_le_mul_of_nonneg_left tf hc
  have Wl : 0 ≤ b * (Nt / (1 - (l * u) ^ 2 / 2)) / √((v0t + l * v1t) / rMatch (l * u)) +
      c * (Nf / (1 - (l * u) ^ 2 / 2)) / √((v0f + l * v1f) / rMatch (l * u)) -
      a * u / (2 * √(qMatch (l * u))) - L * u := by
    rw [mul_div_assoc, mul_div_assoc]
    rw [mul_div_assoc, mul_div_assoc] at W1
    linarith
  have eq : a * (-(u * (1 - (l * u) ^ 2 / 2)) / (2 * rMatch (l * u) ^ 2) /
          (2 * √(qMatch (l * u)))) +
      b * (Nt / rMatch (l * u) ^ 2 / (2 * √((v0t + l * v1t) / rMatch (l * u)))) +
      c * (Nf / rMatch (l * u) ^ 2 / (2 * √((v0f + l * v1f) / rMatch (l * u)))) +
      L * (-(u * (1 - (l * u) ^ 2 / 2)) / (2 * rMatch (l * u) ^ 2)) =
      (1 - (l * u) ^ 2 / 2) / (2 * rMatch (l * u) ^ 2) *
      (b * (Nt / (1 - (l * u) ^ 2 / 2)) / √((v0t + l * v1t) / rMatch (l * u)) +
      c * (Nf / (1 - (l * u) ^ 2 / 2)) / √((v0f + l * v1f) / rMatch (l * u)) -
      a * u / (2 * √(qMatch (l * u))) - L * u) := by
    generalize √(qMatch (l * u)) = A at hq ⊢
    generalize √((v0t + l * v1t) / rMatch (l * u)) = B at hst ⊢
    generalize √((v0f + l * v1f) / rMatch (l * u)) = C at hsf ⊢
    generalize rMatch (l * u) = R at hr ⊢
    generalize hH : 1 - (l * u) ^ 2 / 2 = H at hh ⊢
    field_simp
    ring
  rw [eq]
  exact mul_nonneg (by positivity) Wl

/-- T4's function `𝓡(λ)` with free parameters. -/
noncomputable def t4Fun (u a b c L v0t v1t v0f v1f l : ℝ) : ℝ :=
  a * √(qMatch (l * u)) + b * √((v0t + l * v1t) / rMatch (l * u)) +
    c * √((v0f + l * v1f) / rMatch (l * u)) + L * qMatch (l * u)

theorem t4_mono {u a b c L v0t v1t v0f v1f : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hL : 0 ≤ L)
    (h0t : 0 ≤ v0t) (h1t : 0 ≤ v1t) (h0f : 0 ≤ v0f) (h1f : 0 ≤ v1f)
    (hpt : 0 < v0t + v1t) (hpf : 0 < v0f + v1f)
    (hnt : 0 ≤ nMatch v0t v1t u) (hnf : 0 ≤ nMatch v0f v1f u)
    (hS : (1 - u ^ 2 / 2) / rMatch u ^ 2 * (a * u / (4 * √(qMatch u)) + L * u / 2) ≤
      b * mMatch v0t v1t u + c * mMatch v0f v1f u) :
    MonotoneOn (t4Fun u a b c L v0t v1t v0f v1f) (Set.Ioc 0 1) := by
  have hd : ∀ l : ℝ, 0 < l → l ≤ 1 → HasDerivAt (t4Fun u a b c L v0t v1t v0f v1f)
      (a * (-(u * (1 - (l * u) ^ 2 / 2)) / (2 * rMatch (l * u) ^ 2) /
          (2 * √(qMatch (l * u)))) +
      b * ((v1t * (1 - (l * u) ^ 2 / 2) - v0t * u * (3 / 2 + l * u)) / rMatch (l * u) ^ 2 /
        (2 * √((v0t + l * v1t) / rMatch (l * u)))) +
      c * ((v1f * (1 - (l * u) ^ 2 / 2) - v0f * u * (3 / 2 + l * u)) / rMatch (l * u) ^ 2 /
        (2 * √((v0f + l * v1f) / rMatch (l * u)))) +
      L * (-(u * (1 - (l * u) ^ 2 / 2)) / (2 * rMatch (l * u) ^ 2))) l := by
    intro l hl0 hl1
    have hVt : 0 < v0t + l * v1t := by nlinarith
    have hVf : 0 < v0f + l * v1f := by nlinarith
    have hq := t4_hasDerivAt_q hl0 hu0.le
    have hqs := hq.sqrt (qMatch_pos (by positivity)).ne'
    exact (((hqs.const_mul a).add ((t4_hasDerivAt_s hl0 hu0.le hVt).const_mul b)).add
      ((t4_hasDerivAt_s hl0 hu0.le hVf).const_mul c)).add (hq.const_mul L)
  have hE := fun l hl0 hl1 => t4_E_nonneg hu0 hu1 hl0 hl1 ha hb hc hL h0t h1t h0f h1f hpt hpf
    hnt hnf hS (l := l)
  refine monotoneOn_of_deriv_nonneg (convex_Ioc 0 1) ?_ ?_ ?_
  · intro l hl
    exact (hd l hl.1 hl.2).continuousAt.continuousWithinAt
  · rw [interior_Ioc]
    intro l hl
    exact (hd l hl.1 hl.2.le).differentiableAt.differentiableWithinAt
  · rw [interior_Ioc]
    intro l hl
    rw [(hd l hl.1 hl.2.le).deriv]
    exact hE l hl.1 hl.2.le

end GMCExplicitDelta.Contract
