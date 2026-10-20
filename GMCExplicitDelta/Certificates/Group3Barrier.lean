module

public import GMCExplicitDelta.Certificates.Group3Common

/-!
# Numeric obligations, group 3: barrier and planar derivative test

Monotone bounds for the contraction coefficients and for `Cbar`, the barrier inequality from
numeric majorants, and the planar identities `𝓡(1) = C(t_⋆) + 𝓛 𝗊_⋆` used by O.bar.2.
-/

@[expose] public section

open Real

namespace GMCExplicitDelta.Certificates.G3

open GMCExplicitDelta.Contract GMCExplicitDelta.Haar

variable {d : ℕ}

theorem Sb_nonneg (row : Row d) : 0 ≤ row.Sb := tsum_nonneg (haarB_nonneg row)

theorem Sd_nonneg (row : Row d) : 0 ≤ row.Sd :=
  tsum_nonneg fun _ => mul_nonneg (haarB_nonneg row _) (Real.sqrt_nonneg _)

theorem coefA_enc (row : Row d) {F cl σu Au : ℝ} (hcl : 0 < cl) (hc : cl ≤ row.cNu)
    (hσ0 : 0 ≤ sigmaA d F) (hσ : sigmaA d F ≤ σu) (hε : 0 ≤ (row.epsilon : ℝ))
    (hR : 0 ≤ (row.R : ℝ)) (hAu : (1 + (row.epsilon : ℝ)) * (row.R : ℝ) / cl * σu ≤ Au) :
    0 ≤ row.coefA F ∧ row.coefA F ≤ Au := by
  have hc0 : 0 < row.cNu := lt_of_lt_of_le hcl hc
  have hn : 0 ≤ (1 + (row.epsilon : ℝ)) * (row.R : ℝ) := by positivity
  unfold Row.coefA
  refine ⟨by positivity, le_trans ?_ hAu⟩
  exact mul_le_mul (div_le_div_of_nonneg_left hn hcl hc) hσ hσ0 (by positivity)

theorem coefAv_enc (row : Row d) {cl s2R σu Avu : ℝ} (hcl : 0 < cl) (hc : cl ≤ row.cNu)
    (hs : √(2 * (row.R : ℝ)) ≤ s2R) (hσ0 : 0 ≤ sigmaV d) (hσ : sigmaV d ≤ σu)
    (hε : 0 ≤ (row.epsilon : ℝ))
    (hAv : (1 + (row.epsilon : ℝ)) * s2R / (2 * cl) * σu ≤ Avu) :
    0 ≤ row.coefAv ∧ row.coefAv ≤ Avu := by
  have hc0 : 0 < row.cNu := lt_of_lt_of_le hcl hc
  have hn : 0 ≤ (1 + (row.epsilon : ℝ)) * √(2 * (row.R : ℝ)) := by positivity
  have hn' : 0 ≤ (1 + (row.epsilon : ℝ)) * s2R :=
    mul_nonneg (by positivity) ((Real.sqrt_nonneg _).trans hs)
  unfold Row.coefAv
  refine ⟨by positivity, le_trans ?_ hAv⟩
  have h1 : (1 + (row.epsilon : ℝ)) * √(2 * (row.R : ℝ)) / (2 * row.cNu) ≤
      (1 + (row.epsilon : ℝ)) * s2R / (2 * cl) := by
    refine div_le_div₀ hn' (mul_le_mul_of_nonneg_left hs (by positivity)) (by positivity) ?_
    linarith
  exact mul_le_mul h1 hσ hσ0 (by positivity)

theorem coefAv_lower (row : Row d) {cu s2Rl σl Avl : ℝ} (hcu : row.cNu ≤ cu)
    (hc0 : 0 < row.cNu) (hs : s2Rl ≤ √(2 * (row.R : ℝ))) (hσ0 : 0 ≤ σl)
    (hσ : σl ≤ sigmaV d) (hε : 0 ≤ (row.epsilon : ℝ))
    (hAv : Avl ≤ (1 + (row.epsilon : ℝ)) * s2Rl / (2 * cu) * σl) : Avl ≤ row.coefAv := by
  refine le_trans hAv ?_
  unfold Row.coefAv
  have hcu0 : 0 < cu := lt_of_lt_of_le hc0 hcu
  have h1 : (1 + (row.epsilon : ℝ)) * s2Rl / (2 * cu) ≤
      (1 + (row.epsilon : ℝ)) * √(2 * (row.R : ℝ)) / (2 * row.cNu) := by
    refine div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hs (by positivity))
      (by positivity) ?_
    linarith
  exact mul_le_mul h1 hσ hσ0 (by positivity)

theorem coefB_enc (row : Row d) {F cl σu Bu : ℝ} (hcl : 0 < cl) (hc : cl ≤ row.cNu)
    (hσ0 : 0 ≤ sigmaB d F) (hσ : sigmaB d F ≤ σu) (hε : 0 < (row.epsilon : ℝ))
    (hB : (1 + (row.epsilon : ℝ)⁻¹) / cl * σu ≤ Bu) :
    0 ≤ row.coefB F ∧ row.coefB F ≤ Bu := by
  have hc0 : 0 < row.cNu := lt_of_lt_of_le hcl hc
  have hn : 0 ≤ 1 + (row.epsilon : ℝ)⁻¹ := by positivity
  unfold Row.coefB
  refine ⟨by positivity, le_trans ?_ hB⟩
  exact mul_le_mul (div_le_div_of_nonneg_left hn hcl hc) hσ hσ0 (by positivity)

theorem Cbar_le (row : Row d) (D F : ℝ) {Au Sdu s1 s2 Avu ri Sbu sx Btu sy : ℝ}
    (hA0 : 0 ≤ row.coefA F) (hA : row.coefA F ≤ Au)
    (hSd : row.Sd ≤ Sdu) (h1 : √(1 - row.tStar) ≤ s1) (h2 : √(row.qStar F) ≤ s2)
    (hAv0 : 0 ≤ row.coefAv) (hAv : row.coefAv ≤ Avu)
    (hri : (√(row.rStar F))⁻¹ ≤ ri) (hSb : row.Sb ≤ Sbu)
    (hx : √(row.Qt0 D F + row.Qfor F * (1 - row.tStar ^ 2)) ≤ sx)
    (hBt0 : 0 ≤ row.Btail) (hBt : row.Btail ≤ Btu)
    (hy : √(row.Qf0 D F + row.Qfor F * (1 - row.tStar ^ 2)) ≤ sy) :
    0 ≤ row.Cbar D F ∧
      row.Cbar D F ≤ Au * Sdu * s1 * s2 + Avu * ri * (Sbu * sx + Btu * sy) := by
  have hSd0 := Sd_nonneg row
  have hSb0 := Sb_nonneg row
  have hri0 : 0 ≤ ri := le_trans (inv_nonneg.2 (Real.sqrt_nonneg _)) hri
  have hs1 : 0 ≤ s1 := le_trans (Real.sqrt_nonneg _) h1
  have hs2 : 0 ≤ s2 := le_trans (Real.sqrt_nonneg _) h2
  have hsx : 0 ≤ sx := le_trans (Real.sqrt_nonneg _) hx
  have hsy : 0 ≤ sy := le_trans (Real.sqrt_nonneg _) hy
  have hSdu : 0 ≤ Sdu := hSd0.trans hSd
  have hSbu : 0 ≤ Sbu := hSb0.trans hSb
  have hAu : 0 ≤ Au := hA0.trans hA
  have hAvu : 0 ≤ Avu := hAv0.trans hAv
  have hBtu : 0 ≤ Btu := hBt0.trans hBt
  unfold Row.Cbar
  rw [div_eq_mul_inv]
  constructor
  · positivity
  · have e1 : row.coefA F * row.Sd * √(1 - row.tStar) * √(row.qStar F) ≤ Au * Sdu * s1 * s2 := by
      gcongr
    have e2 : row.coefAv * (√(row.rStar F))⁻¹ *
        (row.Sb * √(row.Qt0 D F + row.Qfor F * (1 - row.tStar ^ 2)) +
          row.Btail * √(row.Qf0 D F + row.Qfor F * (1 - row.tStar ^ 2))) ≤
        Avu * ri * (Sbu * sx + Btu * sy) := by
      gcongr
    linarith

theorem barrier_ge (row : Row d) (D F : ℝ) {τu Cu zu Bu : ℝ} (hZ : 0 ≤ (row.Z : ℝ))
    (hτ : row.tauAbs ≤ τu) (hC0 : 0 ≤ row.Cbar D F) (hC : row.Cbar D F ≤ Cu)
    (hz : √(row.Z : ℝ) ≤ zu) (hB : row.coefB F ≤ Bu) (ht : row.tStar ≤ 1)
    (hq : 0 ≤ row.qStar F) :
    (1 - τu) * (row.Z : ℝ) - Cu * zu - (row.nu : ℝ) * Bu * (1 - row.tStar) * row.qStar F -
        (row.Mwin : ℝ) * (row.badBudget : ℝ) ≤ row.barrier D F := by
  unfold Row.barrier
  have h1 : (1 - τu) * (row.Z : ℝ) ≤ (1 - row.tauAbs) * (row.Z : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith) hZ
  have hCu : 0 ≤ Cu := hC0.trans hC
  have h2 : row.Cbar D F * √(row.Z : ℝ) ≤ Cu * zu :=
    mul_le_mul hC hz (Real.sqrt_nonneg _) hCu
  have h3 : (row.nu : ℝ) * row.coefB F * (1 - row.tStar) * row.qStar F ≤
      (row.nu : ℝ) * Bu * (1 - row.tStar) * row.qStar F := by
    have h1t : 0 ≤ 1 - row.tStar := by linarith
    gcongr
  linarith

/-! ### Planar matching -/

theorem rMatch_pos {u : ℝ} (hu : 0 ≤ u) : 0 < rMatch u := by unfold rMatch; positivity

theorem qMatch_pos {u : ℝ} (hu : 0 ≤ u) : 0 < qMatch u := by
  have := rMatch_pos hu
  unfold qMatch cMatch; unfold rMatch at this ⊢; positivity

theorem mMatch_nonneg {v0 v1 u : ℝ} (hn : 0 ≤ nMatch v0 v1 u) (hu : 0 ≤ u) :
    0 ≤ mMatch v0 v1 u := by
  have := rMatch_pos hu
  unfold mMatch
  positivity

theorem mMatch_ge {v0 v1 u sx sr : ℝ} (hn : 0 ≤ nMatch v0 v1 u) (hv : 0 < v0 + v1)
    (hu : 0 ≤ u) (hsx : √(v0 + v1) ≤ sx) (hsr : √(rMatch u) ≤ sr) :
    nMatch v0 v1 u / (2 * sx * (rMatch u * sr)) ≤ mMatch v0 v1 u := by
  have hr := rMatch_pos hu
  have hs0 : 0 < √(v0 + v1) := Real.sqrt_pos.2 hv
  have hr0 : 0 < √(rMatch u) := Real.sqrt_pos.2 hr
  unfold mMatch
  apply div_le_div_of_nonneg_left hn (by positivity)
  have : 0 ≤ rMatch u := hr.le
  have hsx0 : 0 ≤ sx := le_trans hs0.le hsx
  gcongr

theorem t4a_le (row : Row d) (F : ℝ) {Au Sdu s1 : ℝ} (hA0 : 0 ≤ row.coefA F)
    (hA : row.coefA F ≤ Au) (hSd : row.Sd ≤ Sdu) (h1 : √(1 - row.tStar) ≤ s1) :
    row.t4a F ≤ Au * Sdu * s1 := by
  have hSd0 := Sd_nonneg row
  have := Real.sqrt_nonneg (1 - row.tStar)
  have hAu : 0 ≤ Au := hA0.trans hA
  have hSdu : 0 ≤ Sdu := hSd0.trans hSd
  unfold Row.t4a
  gcongr

theorem t4L_le (row : Row d) (F : ℝ) {Bu zl : ℝ} (hB0 : 0 ≤ row.coefB F)
    (hB : row.coefB F ≤ Bu) (ht : row.tStar ≤ 1) (hz : 0 < zl) (hzl : zl ≤ √(row.Z : ℝ)) :
    0 ≤ row.t4L F ∧ row.t4L F ≤ (row.nu : ℝ) * Bu * (1 - row.tStar) / zl := by
  have h1t : 0 ≤ 1 - row.tStar := by linarith
  have hz0 : 0 < √(row.Z : ℝ) := lt_of_lt_of_le hz hzl
  unfold Row.t4L
  refine ⟨by positivity, ?_⟩
  have h1 : (row.nu : ℝ) * row.coefB F * (1 - row.tStar) ≤ (row.nu : ℝ) * Bu * (1 - row.tStar) := by
    gcongr
  calc (row.nu : ℝ) * row.coefB F * (1 - row.tStar) / √(row.Z : ℝ)
      ≤ (row.nu : ℝ) * Bu * (1 - row.tStar) / √(row.Z : ℝ) :=
        div_le_div_of_nonneg_right h1 hz0.le
    _ ≤ _ := div_le_div_of_nonneg_left (by have := h1.trans' (by positivity); positivity) hz hzl

theorem t4Loss_le (row : Row d) (F : ℝ) {au Lq ql : ℝ} (hu0 : 0 ≤ row.uStar F)
    (hu1 : row.uStar F ^ 2 / 2 ≤ 1) (ha0 : 0 ≤ row.t4a F) (ha : row.t4a F ≤ au)
    (hL : row.t4L F ≤ Lq) (hql : 0 < ql)
    (hq : ql ≤ √(qMatch (row.uStar F))) :
    row.t4Loss F ≤ (1 - row.uStar F ^ 2 / 2) / rMatch (row.uStar F) ^ 2 *
      (au * row.uStar F / (4 * ql) + Lq * row.uStar F / 2) := by
  have hr := rMatch_pos hu0
  have h1 : 0 ≤ 1 - row.uStar F ^ 2 / 2 := by linarith
  unfold Row.t4Loss
  have e1 : row.t4a F * row.uStar F / (4 * √(qMatch (row.uStar F))) ≤ au * row.uStar F / (4 * ql) := by
    have hq0 : 0 < √(qMatch (row.uStar F)) := lt_of_lt_of_le hql hq
    calc row.t4a F * row.uStar F / (4 * √(qMatch (row.uStar F)))
        ≤ au * row.uStar F / (4 * √(qMatch (row.uStar F))) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ha hu0) (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (by have := ha0.trans ha; positivity) (by positivity)
          (by linarith)
  have e2 : row.t4L F * row.uStar F / 2 ≤ Lq * row.uStar F / 2 := by
    have := mul_le_mul_of_nonneg_right hL hu0
    linarith
  gcongr

/-- At `λ = 1` the planar quantity `𝓡` is `C(t_⋆)` plus the localization term. -/
theorem t4R_one (row : Row 2) (D F : ℝ)
    (hX : 0 ≤ row.Qt0 D F + row.Qfor F * (1 - row.tStar ^ 2))
    (hY : 0 ≤ row.Qf0 D F + row.Qfor F * (1 - row.tStar ^ 2)) :
    row.t4R D F 1 = row.Cbar D F + row.t4L F * row.qStar F := by
  have e1 : row.vT0 + row.vT1 D F = row.Qt0 D F + row.Qfor F * (1 - row.tStar ^ 2) := by
    unfold Row.vT1; ring
  have e2 : row.vF0 + row.vF1 D F = row.Qf0 D F + row.Qfor F * (1 - row.tStar ^ 2) := by
    unfold Row.vF1; ring
  unfold Row.t4R Row.Cbar Row.t4a Row.t4b Row.t4c Row.rStar Row.qStar
  simp only [one_mul, ↓reduceIte]
  rw [e1, e2, Real.sqrt_div hX, Real.sqrt_div hY]
  ring

theorem bar2_margin (row : Row 2) (D F : ℝ) (hZ : 0 < (row.Z : ℝ))
    (hX : 0 ≤ row.Qt0 D F + row.Qfor F * (1 - row.tStar ^ 2))
    (hY : 0 ≤ row.Qf0 D F + row.Qfor F * (1 - row.tStar ^ 2))
    (hb : 0 < row.barrier D F) :
    0 < (1 - row.tauAbs) * √(row.Z : ℝ) - row.t4R D F 1 -
      (row.Mwin : ℝ) * (row.badBudget : ℝ) / √(row.Z : ℝ) := by
  rw [t4R_one row D F hX hY]
  have hz : 0 < √(row.Z : ℝ) := Real.sqrt_pos.2 hZ
  have hzz : √(row.Z : ℝ) * √(row.Z : ℝ) = (row.Z : ℝ) := Real.mul_self_sqrt hZ.le
  have key : ((1 - row.tauAbs) * √(row.Z : ℝ) - (row.Cbar D F + row.t4L F * row.qStar F) -
      (row.Mwin : ℝ) * (row.badBudget : ℝ) / √(row.Z : ℝ)) * √(row.Z : ℝ) = row.barrier D F := by
    unfold Row.barrier Row.t4L
    field_simp
    linear_combination (1 - row.tauAbs) * hzz
  by_contra hcon
  have hcon := not_lt.1 hcon
  have : (((1 - row.tauAbs) * √(row.Z : ℝ) - (row.Cbar D F + row.t4L F * row.qStar F) -
      (row.Mwin : ℝ) * (row.badBudget : ℝ) / √(row.Z : ℝ)) * √(row.Z : ℝ)) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hcon hz.le
  linarith

end GMCExplicitDelta.Certificates.G3
