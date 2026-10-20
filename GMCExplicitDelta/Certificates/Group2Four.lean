module

public import GMCExplicitDelta.Certificates.Group2Bad
public import GMCExplicitDelta.Contract.Rows

/-!
# Numeric obligations, group 2, for the row `rowFour`

O.hist.1, O.hist.2, O.avg.4, O.avg.5, O.bad.1, O.bad.2 (generated numerals; checked by `norm_num`).
-/

@[expose] public section

open Real

namespace GMCExplicitDelta.Certificates

open GMCExplicitDelta.Contract

theorem rowFour_x : (0.916567142693 : ℝ) ≤ rowFour.xHist ∧ rowFour.xHist ≤ (0.916567142694 : ℝ) := by
  have hq : -(2 * (rowFour.s : ℝ)) + ((4 : ℕ) : ℝ) / 32 = (-0.0793 : ℝ) := by norm_num [rowFour]
  rw [xHist_eq rowFour hq]
  have : (0.916567142693 : ℝ) ≤ Real.exp (-0.087119954491382 : ℝ) := exp_lb' (by norm_num) (by norm_num [GMCNumerics.expPoly, GMCNumerics.expErr, Finset.sum_range_succ, Nat.factorial])
  have hl := this
  have : Real.exp (-0.087119954491381 : ℝ) ≤ (0.916567142694 : ℝ) := exp_ub' (by norm_num) (by norm_num [GMCNumerics.expPoly, GMCNumerics.expErr, Finset.sum_range_succ, Nat.factorial])
  have hu := this
  exact three_rpow_neg_enclosure (cl := (-0.087119954491382 : ℝ)) (cu := (-0.087119954491381 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num) hl hu

theorem rowFour_w : (0.798958327356 : ℝ) ≤ rowFour.wHaar ∧ rowFour.wHaar ≤ (0.798958327357 : ℝ) := by
  have hq : -(2 * (rowFour.s : ℝ)) = (-0.2043 : ℝ) := by norm_num [rowFour]
  rw [wHaar_eq rowFour hq]
  have : (0.798958327356 : ℝ) ≤ Real.exp (-0.224446490574896 : ℝ) := exp_lb' (by norm_num) (by norm_num [GMCNumerics.expPoly, GMCNumerics.expErr, Finset.sum_range_succ, Nat.factorial])
  have hl := this
  have : Real.exp (-0.224446490574894 : ℝ) ≤ (0.798958327357 : ℝ) := exp_ub' (by norm_num) (by norm_num [GMCNumerics.expPoly, GMCNumerics.expErr, Finset.sum_range_succ, Nat.factorial])
  have hu := this
  exact three_rpow_neg_enclosure (cl := (-0.224446490574896 : ℝ)) (cu := (-0.224446490574894 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num) hl hu

theorem rowFour_bg : (0.070163104719 : ℝ) ≤ rowFour.bg rowFour.deltaStar := by
  have hq : -(2 * (rowFour.s : ℝ)) + ((4 : ℕ) : ℝ) / 32 = (-0.0793 : ℝ) := by norm_num [rowFour]
  refine bg_ge rowFour (c := (0.0169568497715213868 : ℝ)) hq (by norm_num) ?_ (by norm_num)
  rw [kappaH_ne_two (by norm_num)]
  norm_num [rowFour, proxyA, kappaQ1]

theorem rowFour_zF : rowFour.zF rowFour.deltaStar ≤ (0.948184424585 : ℝ) := by
  obtain ⟨hxl, hxu⟩ := rowFour_x
  have hx0 : 0 < rowFour.xHist := lt_of_lt_of_le (by norm_num) hxl
  have : Real.exp (0.0339136995430427736 : ℝ) ≤ (1.034495325457 : ℝ) := exp_ub' (by norm_num) (by norm_num [GMCNumerics.expPoly, GMCNumerics.expErr, Finset.sum_range_succ, Nat.factorial])
  refine zF_le rowFour (c := (0.0339136995430427736 : ℝ)) (xu := (0.916567142694 : ℝ)) (eu := (1.034495325457 : ℝ)) ?_ hx0 hxu this (by norm_num)
  rw [kappaH_ne_two (by norm_num)]
  norm_num [rowFour, proxyA, kappaQ1]

theorem rowFour_zG : rowFour.zG rowFour.deltaStar ≤ (0.92439190867 : ℝ) := by
  obtain ⟨hxl, hxu⟩ := rowFour_x
  have hx0 : 0 < rowFour.xHist := lt_of_lt_of_le (by norm_num) hxl
  have : Real.exp (0.0085008008085606188 : ℝ) ≤ (1.008537035217 : ℝ) := exp_ub' (by norm_num) (by norm_num [GMCNumerics.expPoly, GMCNumerics.expErr, Finset.sum_range_succ, Nat.factorial])
  refine zG_le rowFour (c := (0.0085008008085606188 : ℝ)) (xu := (0.916567142694 : ℝ)) (eu := (1.008537035217 : ℝ)) ?_ hx0 hxu this (by norm_num)
  rw [kappaH_ne_two (by norm_num)]
  norm_num [rowFour, proxyA, kappaQ1]

theorem rowFour_hist1 : rowFour.zG rowFour.deltaStar < rowFour.zF rowFour.deltaStar ∧
    rowFour.zF rowFour.deltaStar < 1 := by
  obtain ⟨hxl, hxu⟩ := rowFour_x
  have hx0 : 0 < rowFour.xHist := lt_of_lt_of_le (by norm_num) hxl
  exact ⟨zG_lt_zF rowFour hx0 (by norm_num [rowFour]), lt_of_le_of_lt rowFour_zF (by norm_num)⟩

theorem rowFour_hist2 : 0 < rowFour.bg rowFour.deltaStar :=
  lt_of_lt_of_le (by norm_num) rowFour_bg

theorem rowFour_avg4 : (3 : ℝ) ^ (-(((4 : ℕ) : ℝ) / 2)) < rowFour.xHist := by
  obtain ⟨hxl, hxu⟩ := rowFour_x
  calc (3 : ℝ) ^ (-(((4 : ℕ) : ℝ) / 2)) ≤ (3 : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ = 3⁻¹ := Real.rpow_neg_one 3
    _ < rowFour.xHist := lt_of_lt_of_le (by norm_num) hxl


theorem rowFour_avg5 : frakU 4 rowFour.historyCutoff (rowFour.D : ℝ) (rowFour.F : ℝ) < 1 := by
  have h : rowFour.historyCutoff = 12 := rfl
  rw [h]
  exact frakU_twelve_lt_one (by norm_num [rowFour]) (by norm_num [rowFour]) (by norm_num [sigmaNorm])
    (by norm_num)

theorem rowFour_bad1 : (rowFour.F : ℝ) < rowFour.thetaR := by
  norm_num [Row.thetaR, rowFour]

set_option exponentiation.threshold 1024 in
theorem rowFour_bad2 : rowFour.badCharge rowFour.deltaStar rowFour.D rowFour.F < rowFour.badBudget := by
  have hD : (0 : ℝ) < (rowFour.D : ℝ) := by norm_num [rowFour]
  have hF0 : (0 : ℝ) < (rowFour.F : ℝ) := by norm_num [rowFour]
  have hFD : (rowFour.F : ℝ) ≤ (rowFour.D : ℝ) := by norm_num [rowFour]
  have hδ : (0 : ℝ) ≤ (rowFour.deltaStar : ℝ) := by norm_num [rowFour]
  have hη : (0 : ℝ) < (rowFour.eta : ℝ) := by norm_num [rowFour]
  have hes : (0 : ℝ) < (rowFour.epsSub : ℝ) := by norm_num [rowFour]
  obtain ⟨hxl, hxu⟩ := rowFour_x
  obtain ⟨hwl, hwu⟩ := rowFour_w
  have hx0 : 0 < rowFour.xHist := lt_of_lt_of_le (by norm_num) hxl
  have hw0 : 0 ≤ rowFour.wHaar := by unfold Row.wHaar; positivity
  have hw1 : rowFour.wHaar ≤ 1 := hwu.trans (by norm_num)
  have hzF := rowFour_zF
  have hzG := rowFour_zG
  have hzF0 := zF_nonneg rowFour ((rowFour.deltaStar : ℚ) : ℝ) hx0
  have hzG0 := zG_nonneg rowFour ((rowFour.deltaStar : ℚ) : ℝ) hx0
  have hAF0 := AF_nonneg (d := 4) hδ
  have hAG0 := AG_nonneg (d := 4) hδ
  have hAF : AF 4 ((rowFour.deltaStar : ℚ) : ℝ) ≤ (0.00001033457154 : ℝ) :=
    (AF_le (by norm_num) hδ).trans (by norm_num [rowFour, kappaQ1])
  have hAG : AG 4 ((rowFour.deltaStar : ℚ) : ℝ) ≤ (0.00001044713707 : ℝ) :=
    (AG_le (by norm_num) hδ).trans (by norm_num [rowFour, kappaQ1])
  have hFb : rowFour.Fbar rowFour.deltaStar ≤ (0.9738086651 : ℝ) := by
    unfold Row.Fbar
    exact (bracket_le (wl := (0.798958327356 : ℝ)) hwl hw1 hzF0 hzF (by norm_num) Ch_nonneg Ch_le hAF0 hAF).trans
      (by norm_num [rowFour])
  have hGb : rowFour.Gbar rowFour.deltaStar ≤ (0.4418955342 : ℝ) := by
    unfold Row.Gbar
    exact (bracket_le (wl := (0.798958327356 : ℝ)) hwl hw1 hzG0 hzG (by norm_num) Ch_nonneg Ch_le hAG0 hAG).trans
      (by norm_num [rowFour])
  have hFb0 : 0 ≤ rowFour.Fbar rowFour.deltaStar := by
    unfold Row.Fbar
    exact bracket_nonneg hw1 hzF0 (lt_of_le_of_lt hzF (by norm_num)) Ch_nonneg hAF0
  have hGb0 : 0 ≤ rowFour.Gbar rowFour.deltaStar := by
    unfold Row.Gbar
    exact bracket_nonneg hw1 hzG0 (lt_of_le_of_lt hzG (by norm_num)) Ch_nonneg hAG0
  have hC1 : rowFour.C1 ≤ (2.20858061689 : ℝ) :=
    (C1_le rowFour hwl hw1 hx0 hxu (by norm_num)).trans (by norm_num)
  have hbg := rowFour_bg
  have hhb : rowFour.hbar ≤ (1.108485759 : ℝ) :=
    hbar_le rowFour (by norm_num) (by norm_num [Row.gridCount, rowFour])
  have hbt : sphereFactor 4 ≤ (1.198926358 : ℝ) :=
    sphereFactor_le 4 (by norm_num) (by norm_num [sphereFactorPow, Nat.choose_eq_factorial_div_factorial, Nat.factorial])
  have hAg : rowFour.Ag = (1/36 : ℝ) := by norm_num [Row.Ag, rowFour]
  have hM1 : rowFour.M1 rowFour.deltaStar ≤ ((0.371732405 : ℝ) + rowFour.Ag) ^ 2 :=
    M1_le rowFour _ (by norm_num) hbg (by norm_num) (cg_nonneg _)
      ((cg_sq_le rowFour hhb).trans (by norm_num [proxyA])) (Ag_nonneg _)
  have hM2 : rowFour.M2 rowFour.deltaStar ≤ (109.987540313 : ℝ) :=
    M2_le rowFour _ (by norm_num) hbg (by norm_num)
  have hexp0 : Real.exp (61606801/101250000000 : ℝ) ≤ (1.000608647383 : ℝ) := exp_ub' (by norm_num) (by norm_num [GMCNumerics.expPoly, GMCNumerics.expErr, Finset.sum_range_succ, Nat.factorial])
  have hexp : Real.exp (32 * rowFour.Ag ^ 2 * ((rowFour.deltaStar : ℚ) : ℝ) ^ 2) ≤ (1.000608647383 : ℝ) := by
    have e : 32 * rowFour.Ag ^ 2 * ((rowFour.deltaStar : ℚ) : ℝ) ^ 2 = (61606801/101250000000 : ℝ) := by
      norm_num [Row.Ag, rowFour]
    rw [e]; exact hexp0
  have hU : rowFour.Ugrid rowFour.deltaStar ≤ (0.048432383167 : ℝ) := by
    refine (Ugrid_le rowFour hes hw0 hwu varsigma_le (hbar_nonneg _) hhb (xl := (0.916567142693 : ℝ)) (by norm_num) hxl hexp
      P32_le hM1 hM2).trans ?_
    rw [hAg]
    rw [kappaH_ne_two (show (4 : ℕ) ≠ 2 by norm_num)]
    norm_num [rowFour, kappaQ1]
  have hH : rowFour.Hhist rowFour.deltaStar rowFour.D ≤ (13.473532044 : ℝ) :=
    (Hhist_le rowFour hη hD.le hC1 (sphereFactor_nonneg _) hbt hFb0 hFb hGb0 hGb hU).trans
      (by norm_num [rowFour])
  have hTp : ((rowFour.F : ℝ) / (rowFour.D : ℝ)) ^ 32 ≤ (0.06573201 : ℝ) ^ 31 := by norm_num [rowFour]
  have hu2 : frakU 4 2 (rowFour.D : ℝ) (rowFour.F : ℝ) ≤ (0.17692 : ℝ) :=
    frakU_le_of (by norm_num) hD hF0.le hFD (by norm_num) hTp (r := (88460/615471 : ℝ)) (by norm_num)
      (by rw [Xsum_eq]; norm_num) (by norm_num [sigmaNorm])
  have hu3 : frakU 4 3 (rowFour.D : ℝ) (rowFour.F : ℝ) ≤ (0.0150549 : ℝ) :=
    frakU_le_of (by norm_num) hD hF0.le hFD (by norm_num) hTp (r := (50183/4103140 : ℝ)) (by norm_num)
      (by rw [Xsum_eq]; norm_num) (by norm_num [sigmaNorm])
  have hanc : (sigmaNorm 4 : ℝ) * Bbar32 (3 ^ (4 * 3)) (rowFour.D : ℝ) (rowFour.F : ℝ) ≤ (0.0016354 : ℝ) :=
    sigma_Bbar_le hD hF0.le hFD (by norm_num) hTp (r := (8177/6154710 : ℝ)) (by norm_num)
      (by rw [Xsum_eq]; norm_num) (by norm_num [sigmaNorm])
  have hP : ∑ ℓ ∈ Finset.range (3 + 1), frakU 4 ℓ (rowFour.D : ℝ) (rowFour.F : ℝ) * (1.091027546 : ℝ) ^ ℓ ≤ (2.321174416888 : ℝ) := by
    have e0 : frakU 4 0 (rowFour.D : ℝ) (rowFour.F : ℝ) = 1 := by simp [frakU]
    have e1 := frakU_le_one 4 1 (rowFour.D : ℝ) (rowFour.F : ℝ)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, e0]
    have y0 : (0 : ℝ) ≤ (1.091027546 : ℝ) := by norm_num
    calc _ ≤ 0 + 1 * (1.091027546 : ℝ) ^ 0 + 1 * (1.091027546 : ℝ) ^ 1 + (0.17692 : ℝ) * (1.091027546 : ℝ) ^ 2 + (0.0150549 : ℝ) * (1.091027546 : ℝ) ^ 3  := by
          gcongr
      _ ≤ _ := by norm_num
  have hS : rowFour.Sinf (rowFour.D : ℝ) (rowFour.F : ℝ) ≤ (2.323811291 : ℝ) := by
    have hy : rowFour.xHist⁻¹ ≤ (1.091027546 : ℝ) := (inv_anti₀ (by norm_num) hxl).trans (by norm_num)
    refine (Sinf_le rowFour hD hF0.le hx0 hy (r := (1/9 : ℝ)) (by norm_num) (by norm_num) (by norm_num) hanc hP).trans ?_
    norm_num
  have he : rowFour.eStar rowFour.deltaStar rowFour.D rowFour.F ≤ (0.00812594360865 : ℝ) :=
    (eStar_le rowFour hwl hw1 hD.le hx0 hxu (Sinf_nonneg rowFour hD hF0.le hx0) hS hH (by norm_num)).trans
      (by norm_num [rowFour])
  have hcap : nativeCap 4 (rowFour.g - rowFour.nu) (rowFour.D : ℝ) (rowFour.F : ℝ) ≤ (0.169438720000000001 : ℝ) :=
    (nativeCap_le hD hF0.le (r := 1 / 10 ^ 20)
      (Bbar32_crude hD hF0.le (Nat.one_le_pow _ _ (by norm_num)) (by norm_num) (by norm_num [rowFour]))).trans
      (by norm_num [sigmaNorm, rowFour])
  have hc0 := nativeCap_nonneg (d := 4) (k := rowFour.g - rowFour.nu) hD hF0.le
  have hθ : (rowFour.F : ℝ) < rowFour.thetaR := rowFour_bad1
  unfold Row.badCharge
  exact bad_lt hF0 hθ hc0 hcap (q := (0.606289468683 : ℝ)) (by norm_num) (by norm_num) he (by norm_num)
    (by norm_num [Row.thetaR, rowFour])

/-- The group 2 fields for `rowFour`. -/
theorem rowFour_group2 : Group2 rowFour :=
  ⟨rowFour_hist1, rowFour_hist2, rowFour_avg4, rowFour_avg5, rowFour_bad1, rowFour_bad2⟩

end GMCExplicitDelta.Certificates

