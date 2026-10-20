module

public import GMCExplicitDelta.Certificates.Group2History
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Numeric obligations, group 2: `U_grid`, `H`, `e_⋆` and the bad charge

Generic upper bounds, composed from the bounds of the ingredients.
-/

@[expose] public section

open Real

namespace GMCExplicitDelta.Certificates

open GMCExplicitDelta.Contract

theorem Ugrid_le {d : ℕ} (row : Row d) {δ wu su hu xl eu Pu M1u M2u : ℝ}
    (hes : 0 < (row.epsSub : ℝ))
    (hw0 : 0 ≤ row.wHaar) (hw : row.wHaar ≤ wu)
    (hs : varsigma ≤ su) (hh0 : 0 ≤ row.hbar) (hh : row.hbar ≤ hu)
    (hxl : 0 < xl) (hx : xl ≤ row.xHist) (he : Real.exp (32 * row.Ag ^ 2 * δ ^ 2) ≤ eu)
    (hP : P32 ≤ Pu) (hM1 : row.M1 δ ≤ M1u) (hM2 : row.M2 δ ≤ M2u) :
    row.Ugrid δ ≤ wu * su * hu / (2 * xl) * eu *
      (if d = 2 then Pu * δ ^ 2 * M1u
       else (1 + (row.epsSub : ℝ)) * Pu * δ ^ 2 * M1u +
         (1 + (row.epsSub : ℝ)⁻¹) * kappaH d ^ 2 * δ ^ 4 * M2u) := by
  have hς0 := varsigma_nonneg
  have hP0 := P32_nonneg
  have hM10 := M1_nonneg row δ
  have hM20 := M2_nonneg row δ
  have hE0 : 0 ≤ Real.exp (32 * row.Ag ^ 2 * δ ^ 2) := (Real.exp_pos _).le
  have hwu : 0 ≤ wu := hw0.trans hw
  have hsu : 0 ≤ su := hς0.trans hs
  have hhu : 0 ≤ hu := hh0.trans hh
  have heu : 0 ≤ eu := hE0.trans he
  have hPu : 0 ≤ Pu := hP0.trans hP
  have hM1u : 0 ≤ M1u := hM10.trans hM1
  have hM2u : 0 ≤ M2u := hM20.trans hM2
  have hx0 : 0 < row.xHist := lt_of_lt_of_le hxl hx
  have hB : (0 ≤ (if d = 2 then P32 * δ ^ 2 * row.M1 δ
       else (1 + (row.epsSub : ℝ)) * P32 * δ ^ 2 * row.M1 δ +
         (1 + (row.epsSub : ℝ)⁻¹) * kappaH d ^ 2 * δ ^ 4 * row.M2 δ)) ∧
      (if d = 2 then P32 * δ ^ 2 * row.M1 δ
       else (1 + (row.epsSub : ℝ)) * P32 * δ ^ 2 * row.M1 δ +
         (1 + (row.epsSub : ℝ)⁻¹) * kappaH d ^ 2 * δ ^ 4 * row.M2 δ) ≤
      (if d = 2 then Pu * δ ^ 2 * M1u
       else (1 + (row.epsSub : ℝ)) * Pu * δ ^ 2 * M1u +
         (1 + (row.epsSub : ℝ)⁻¹) * kappaH d ^ 2 * δ ^ 4 * M2u) := by
    split_ifs
    · exact ⟨by positivity, by gcongr⟩
    · exact ⟨by positivity, by gcongr⟩
  obtain ⟨hB0, hBB⟩ := hB
  unfold Row.Ugrid
  gcongr

theorem sphereFactor_nonneg (d : ℕ) : 0 ≤ sphereFactor d := by
  unfold sphereFactor
  refine Real.rpow_nonneg ?_ _
  unfold sphereFactorPow
  split_ifs <;> positivity

theorem Hhist_le {d : ℕ} (row : Row d) {δ D C1u βu Fu Gu Uu : ℝ} (hη : 0 < (row.eta : ℝ))
    (hD : 0 ≤ D) (hC1 : row.C1 ≤ C1u) (hβ0 : 0 ≤ sphereFactor d) (hβ : sphereFactor d ≤ βu)
    (hF0 : 0 ≤ row.Fbar δ) (hF : row.Fbar δ ≤ Fu) (hG0 : 0 ≤ row.Gbar δ)
    (hG : row.Gbar δ ≤ Gu) (hU : row.Ugrid δ ≤ Uu) :
    row.Hhist δ D ≤ (1 + (row.eta : ℝ)) * C1u * D +
      βu * (1 + D) * (Fu / (2 * (row.eta : ℝ)) + Gu) + Uu := by
  unfold Row.Hhist
  have hβu : 0 ≤ βu := hβ0.trans hβ
  gcongr

theorem Sinf_nonneg {d : ℕ} (row : Row d) {D F : ℝ} (hD : 0 < D) (hF : 0 ≤ F)
    (hx : 0 < row.xHist) : 0 ≤ row.Sinf D F := by
  unfold Row.Sinf
  exact tsum_nonneg fun ℓ =>
    mul_nonneg (frakU_nonneg d ℓ hD hF) (pow_nonneg (inv_pos.2 hx).le _)

theorem eStar_le {d : ℕ} (row : Row d) {δ D F wl xu Su Hu : ℝ} (hwl : wl ≤ row.wHaar)
    (hw1 : row.wHaar ≤ 1) (hD : 0 ≤ D) (hx0 : 0 < row.xHist) (hxx : row.xHist ≤ xu)
    (hS0 : 0 ≤ row.Sinf D F) (hS : row.Sinf D F ≤ Su) (hH : row.Hhist δ D ≤ Hu)
    (hHu : 0 ≤ Hu) :
    row.eStar δ D F ≤ (1 - wl) * D * xu ^ row.g * Su + xu ^ row.g * Hu := by
  unfold Row.eStar
  have h1 : 0 ≤ 1 - row.wHaar := by linarith
  have h2 : 1 - row.wHaar ≤ 1 - wl := by linarith
  have h3 : 0 ≤ row.xHist ^ row.g := by positivity
  have h4 : row.xHist ^ row.g ≤ xu ^ row.g := by gcongr
  have hSu : 0 ≤ Su := hS0.trans hS
  have h5 : 0 ≤ 1 - wl := h1.trans h2
  have hxu : 0 ≤ xu := hx0.le.trans hxx
  have e1 : (1 - row.wHaar) * D * row.xHist ^ row.g * row.Sinf D F ≤
      (1 - wl) * D * xu ^ row.g * Su := by gcongr
  have e2 : row.xHist ^ row.g * row.Hhist δ D ≤ xu ^ row.g * Hu :=
    calc row.xHist ^ row.g * row.Hhist δ D ≤ row.xHist ^ row.g * Hu :=
          mul_le_mul_of_nonneg_left hH h3
      _ ≤ xu ^ row.g * Hu := mul_le_mul_of_nonneg_right h4 hHu
  linarith

/-! ### The native cap and `Φ` -/

theorem nativeCap_nonneg {d k : ℕ} {D F : ℝ} (hD : 0 < D) (hF : 0 ≤ F) :
    0 ≤ nativeCap d k D F := by
  unfold nativeCap
  refine le_min hD.le ?_
  have := Bbar32_nonneg' (3 ^ (d * (k - 1))) hD hF
  have := sigmaNorm_nonneg d
  positivity

theorem nativeCap_le {d k : ℕ} {D F r : ℝ} (hD : 0 < D) (_hF : 0 ≤ F)
    (hB : Bbar32 (3 ^ (d * (k - 1))) D F ≤ r) :
    nativeCap d k D F ≤ F + (sigmaNorm d : ℝ) * D * r := by
  unfold nativeCap
  refine (min_le_right _ _).trans ?_
  have := sigmaNorm_nonneg d
  gcongr

theorem PhiMap_nonneg {t j : ℝ} (ht : 0 ≤ t) (hj : 0 ≤ j) : 0 ≤ PhiMap t j := by
  unfold PhiMap
  have h1 := one_le_cosh t
  have h2 := Real.sinh_nonneg_iff.2 ht
  have h3 : 0 ≤ √(j * (j + 2)) * Real.sinh t := by positivity
  nlinarith

theorem PhiMap_log_le {F j Ju q : ℝ} (hF : 0 < F) (hj0 : 0 ≤ j) (hjJ : j ≤ Ju) (hq0 : 0 ≤ q)
    (hq : Ju * (Ju + 2) ≤ q ^ 2) :
    PhiMap (Real.log (1 + 2 * F)) j ≤
      (1 + Ju) * ((1 + 2 * F) + (1 + 2 * F)⁻¹) / 2 - 1 +
        q * ((1 + 2 * F) - (1 + 2 * F)⁻¹) / 2 := by
  unfold PhiMap
  have hβ : (0 : ℝ) < 1 + 2 * F := by linarith
  rw [Real.cosh_log hβ, Real.sinh_log hβ]
  have hs : √(j * (j + 2)) ≤ q := Real.sqrt_le_iff.2 ⟨hq0, by nlinarith⟩
  have hinv : (1 + 2 * F)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hb : 0 ≤ ((1 + 2 * F) + (1 + 2 * F)⁻¹) / 2 := by
    have : 0 < (1 + 2 * F)⁻¹ := inv_pos.2 hβ
    linarith
  have hc : 0 ≤ ((1 + 2 * F) - (1 + 2 * F)⁻¹) / 2 := by linarith
  have h1 := mul_le_mul_of_nonneg_right hs hc
  have h2 := mul_le_mul_of_nonneg_right (by linarith : 1 + j ≤ 1 + Ju) hb
  nlinarith

theorem bad_lt {F θ e eu j Ju q b : ℝ} (hF : 0 < F) (hFθ : F < θ) (hj0 : 0 ≤ j) (hjJ : j ≤ Ju)
    (hq0 : 0 ≤ q) (hq : Ju * (Ju + 2) ≤ q ^ 2) (he : e ≤ eu) (heu : 0 < eu)
    (hnum : ((1 + Ju) * ((1 + 2 * F) + (1 + 2 * F)⁻¹) / 2 - 1 +
        q * ((1 + 2 * F) - (1 + 2 * F)⁻¹) / 2) / F * (eu / (θ - F)) ^ 31 < b) :
    PhiMap (Real.log (1 + 2 * F)) j / F * (e / (θ - F)) ^ 31 < b := by
  have hθF : 0 < θ - F := by linarith
  have hΦ := PhiMap_log_le hF hj0 hjJ hq0 hq
  have hΦ0 : 0 ≤ PhiMap (Real.log (1 + 2 * F)) j :=
    PhiMap_nonneg (Real.log_nonneg (by linarith)) hj0
  have hA : PhiMap (Real.log (1 + 2 * F)) j / F ≤
      ((1 + Ju) * ((1 + 2 * F) + (1 + 2 * F)⁻¹) / 2 - 1 +
        q * ((1 + 2 * F) - (1 + 2 * F)⁻¹) / 2) / F := by gcongr
  have hA0 : 0 ≤ PhiMap (Real.log (1 + 2 * F)) j / F := by positivity
  have hAu : 0 ≤ ((1 + Ju) * ((1 + 2 * F) + (1 + 2 * F)⁻¹) / 2 - 1 +
        q * ((1 + 2 * F) - (1 + 2 * F)⁻¹) / 2) / F := hA0.trans hA
  have hBB : (e / (θ - F)) ^ 31 ≤ (eu / (θ - F)) ^ 31 :=
    (Odd.strictMono_pow (by decide : Odd 31)).monotone (div_le_div_of_nonneg_right he hθF.le)
  have hBu : 0 ≤ (eu / (θ - F)) ^ 31 := by positivity
  rcases le_or_gt 0 ((e / (θ - F)) ^ 31) with hB | hB
  · calc PhiMap (Real.log (1 + 2 * F)) j / F * (e / (θ - F)) ^ 31
        ≤ _ * (e / (θ - F)) ^ 31 := mul_le_mul_of_nonneg_right hA hB
      _ ≤ _ * (eu / (θ - F)) ^ 31 := mul_le_mul_of_nonneg_left hBB hAu
      _ < b := hnum
  · have : PhiMap (Real.log (1 + 2 * F)) j / F * (e / (θ - F)) ^ 31 ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hA0 hB.le
    have : 0 ≤ ((1 + Ju) * ((1 + 2 * F) + (1 + 2 * F)⁻¹) / 2 - 1 +
        q * ((1 + 2 * F) - (1 + 2 * F)⁻¹) / 2) / F * (eu / (θ - F)) ^ 31 :=
      mul_nonneg hAu hBu
    linarith

/-- The group 2 fields of `Row.Obligations`, verbatim. -/
structure Group2 {d : ℕ} (row : Row d) : Prop where
  hist1 : row.zG row.deltaStar < row.zF row.deltaStar ∧ row.zF row.deltaStar < 1
  hist2 : 0 < row.bg row.deltaStar
  avg4 : (3 : ℝ) ^ (-((d : ℝ) / 2)) < row.xHist
  avg5 : frakU d row.historyCutoff row.D row.F < 1
  bad1 : (row.F : ℝ) < row.thetaR
  bad2 : row.badCharge row.deltaStar row.D row.F < row.badBudget

end GMCExplicitDelta.Certificates
