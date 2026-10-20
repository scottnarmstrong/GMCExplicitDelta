module

public import GMCExplicitDelta.Certificates.Group2Bad
public import GMCExplicitDelta.Contract.Rows

/-!
# Numeric obligations, group 2, for the row `rowThree`

O.hist.1, O.hist.2, O.avg.4, O.avg.5, O.bad.1, O.bad.2 (generated numerals; checked by `norm_num`).
-/

@[expose] public section

open Real

namespace GMCExplicitDelta.Certificates

open GMCExplicitDelta.Contract

theorem rowThree_x : (0.897603768015 : ℝ) ≤ rowThree.xHist ∧ rowThree.xHist ≤ (0.897603768016 : ℝ) := by
  have hq : -(2 * (rowThree.s : ℝ)) + ((3 : ℕ) : ℝ) / 32 = (-0.09833 : ℝ) := by norm_num [rowThree]
  rw [xHist_eq rowThree hq]
  have : (0.897603768015 : ℝ) ≤ Real.exp (-0.108026546344736 : ℝ) := exp_lb' (by norm_num) (by norm_num [GMCNumerics.expPoly, GMCNumerics.expErr, Finset.sum_range_succ, Nat.factorial])
  have hl := this
  have : Real.exp (-0.108026546344735 : ℝ) ≤ (0.897603768016 : ℝ) := exp_ub' (by norm_num) (by norm_num [GMCNumerics.expPoly, GMCNumerics.expErr, Finset.sum_range_succ, Nat.factorial])
  have hu := this
  exact three_rpow_neg_enclosure (cl := (-0.108026546344736 : ℝ)) (cu := (-0.108026546344735 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num) hl hu

theorem rowThree_w : (0.809756698703 : ℝ) ≤ rowThree.wHaar ∧ rowThree.wHaar ≤ (0.809756698704 : ℝ) := by
  have hq : -(2 * (rowThree.s : ℝ)) = (-0.19208 : ℝ) := by norm_num [rowThree]
  rw [wHaar_eq rowThree hq]
  have : (0.809756698703 : ℝ) ≤ Real.exp (-0.211021448407371 : ℝ) := exp_lb' (by norm_num) (by norm_num [GMCNumerics.expPoly, GMCNumerics.expErr, Finset.sum_range_succ, Nat.factorial])
  have hl := this
  have : Real.exp (-0.21102144840737 : ℝ) ≤ (0.809756698704 : ℝ) := exp_ub' (by norm_num) (by norm_num [GMCNumerics.expPoly, GMCNumerics.expErr, Finset.sum_range_succ, Nat.factorial])
  have hu := this
  exact three_rpow_neg_enclosure (cl := (-0.211021448407371 : ℝ)) (cu := (-0.21102144840737 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num) hl hu

theorem rowThree_bg : (0.08352461473 : ℝ) ≤ rowThree.bg rowThree.deltaStar := by
  have hq : -(2 * (rowThree.s : ℝ)) + ((3 : ℕ) : ℝ) / 32 = (-0.09833 : ℝ) := by norm_num [rowThree]
  refine bg_ge rowThree (c := (0.02450193161469723 : ℝ)) hq (by norm_num) ?_ (by norm_num)
  rw [kappaH_ne_two (by norm_num)]
  norm_num [rowThree, proxyA, kappaQ1]

theorem rowThree_zF : rowThree.zF rowThree.deltaStar ≤ (0.942685385875 : ℝ) := by
  obtain ⟨hxl, hxu⟩ := rowThree_x
  have hx0 : 0 < rowThree.xHist := lt_of_lt_of_le (by norm_num) hxl
  have : Real.exp (0.04900386322939446 : ℝ) ≤ (1.05022440799 : ℝ) := exp_ub' (by norm_num) (by norm_num [GMCNumerics.expPoly, GMCNumerics.expErr, Finset.sum_range_succ, Nat.factorial])
  refine zF_le rowThree (c := (0.04900386322939446 : ℝ)) (xu := (0.897603768016 : ℝ)) (eu := (1.05022440799 : ℝ)) ?_ hx0 hxu this (by norm_num)
  rw [kappaH_ne_two (by norm_num)]
  norm_num [rowThree, proxyA, kappaQ1]

theorem rowThree_zG : rowThree.zG rowThree.deltaStar ≤ (0.90869729572 : ℝ) := by
  obtain ⟨hxl, hxu⟩ := rowThree_x
  have hx0 : 0 < rowThree.xHist := lt_of_lt_of_le (by norm_num) hxl
  have : Real.exp (0.01228329807057243 : ℝ) ≤ (1.01235904761 : ℝ) := exp_ub' (by norm_num) (by norm_num [GMCNumerics.expPoly, GMCNumerics.expErr, Finset.sum_range_succ, Nat.factorial])
  refine zG_le rowThree (c := (0.01228329807057243 : ℝ)) (xu := (0.897603768016 : ℝ)) (eu := (1.01235904761 : ℝ)) ?_ hx0 hxu this (by norm_num)
  rw [kappaH_ne_two (by norm_num)]
  norm_num [rowThree, proxyA, kappaQ1]

theorem rowThree_hist1 : rowThree.zG rowThree.deltaStar < rowThree.zF rowThree.deltaStar ∧
    rowThree.zF rowThree.deltaStar < 1 := by
  obtain ⟨hxl, hxu⟩ := rowThree_x
  have hx0 : 0 < rowThree.xHist := lt_of_lt_of_le (by norm_num) hxl
  exact ⟨zG_lt_zF rowThree hx0 (by norm_num [rowThree]), lt_of_le_of_lt rowThree_zF (by norm_num)⟩

theorem rowThree_hist2 : 0 < rowThree.bg rowThree.deltaStar :=
  lt_of_lt_of_le (by norm_num) rowThree_bg

theorem rowThree_avg4 : (3 : ℝ) ^ (-(((3 : ℕ) : ℝ) / 2)) < rowThree.xHist := by
  obtain ⟨hxl, hxu⟩ := rowThree_x
  calc (3 : ℝ) ^ (-(((3 : ℕ) : ℝ) / 2)) ≤ (3 : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ = 3⁻¹ := Real.rpow_neg_one 3
    _ < rowThree.xHist := lt_of_lt_of_le (by norm_num) hxl


theorem rowThree_avg5 : frakU 3 rowThree.historyCutoff (rowThree.D : ℝ) (rowThree.F : ℝ) < 1 := by
  have h : rowThree.historyCutoff = 12 := rfl
  rw [h]
  exact frakU_twelve_lt_one (by norm_num [rowThree]) (by norm_num [rowThree]) (by norm_num [sigmaNorm])
    (by norm_num)

theorem rowThree_bad1 : (rowThree.F : ℝ) < rowThree.thetaR := by
  norm_num [Row.thetaR, rowThree]


theorem rowThree_bad2 : rowThree.badCharge rowThree.deltaStar rowThree.D rowThree.F < rowThree.badBudget := by
  have hD : (0 : ℝ) < (rowThree.D : ℝ) := by norm_num [rowThree]
  have hF0 : (0 : ℝ) < (rowThree.F : ℝ) := by norm_num [rowThree]
  have hFD : (rowThree.F : ℝ) ≤ (rowThree.D : ℝ) := by norm_num [rowThree]
  have hδ : (0 : ℝ) ≤ (rowThree.deltaStar : ℝ) := by norm_num [rowThree]
  have hη : (0 : ℝ) < (rowThree.eta : ℝ) := by norm_num [rowThree]
  have hes : (0 : ℝ) < (rowThree.epsSub : ℝ) := by norm_num [rowThree]
  obtain ⟨hxl, hxu⟩ := rowThree_x
  obtain ⟨hwl, hwu⟩ := rowThree_w
  have hx0 : 0 < rowThree.xHist := lt_of_lt_of_le (by norm_num) hxl
  have hw0 : 0 ≤ rowThree.wHaar := by unfold Row.wHaar; positivity
  have hw1 : rowThree.wHaar ≤ 1 := hwu.trans (by norm_num)
  have hzF := rowThree_zF
  have hzG := rowThree_zG
  have hzF0 := zF_nonneg rowThree ((rowThree.deltaStar : ℚ) : ℝ) hx0
  have hzG0 := zG_nonneg rowThree ((rowThree.deltaStar : ℚ) : ℝ) hx0
  have hAF0 := AF_nonneg (d := 3) hδ
  have hAG0 := AG_nonneg (d := 3) hδ
  have hAF : AF 3 ((rowThree.deltaStar : ℚ) : ℝ) ≤ (0.00001795114719 : ℝ) :=
    (AF_le (by norm_num) hδ).trans (by norm_num [rowThree, kappaQ1])
  have hAG : AG 3 ((rowThree.deltaStar : ℚ) : ℝ) ≤ (0.00001814668121 : ℝ) :=
    (AG_le (by norm_num) hδ).trans (by norm_num [rowThree, kappaQ1])
  have hFb : rowThree.Fbar rowThree.deltaStar ≤ (1.0845375927 : ℝ) := by
    unfold Row.Fbar
    exact (bracket_le (wl := (0.809756698703 : ℝ)) hwl hw1 hzF0 hzF (by norm_num) Ch_nonneg Ch_le hAF0 hAF).trans
      (by norm_num [rowThree])
  have hGb : rowThree.Gbar rowThree.deltaStar ≤ (0.4072142511 : ℝ) := by
    unfold Row.Gbar
    exact (bracket_le (wl := (0.809756698703 : ℝ)) hwl hw1 hzG0 hzG (by norm_num) Ch_nonneg Ch_le hAG0 hAG).trans
      (by norm_num [rowThree])
  have hFb0 : 0 ≤ rowThree.Fbar rowThree.deltaStar := by
    unfold Row.Fbar
    exact bracket_nonneg hw1 hzF0 (lt_of_le_of_lt hzF (by norm_num)) Ch_nonneg hAF0
  have hGb0 : 0 ≤ rowThree.Gbar rowThree.deltaStar := by
    unfold Row.Gbar
    exact bracket_nonneg hw1 hzG0 (lt_of_le_of_lt hzG (by norm_num)) Ch_nonneg hAG0
  have hC1 : rowThree.C1 ≤ (1.667669803619 : ℝ) :=
    (C1_le rowThree hwl hw1 hx0 hxu (by norm_num)).trans (by norm_num)
  have hbg := rowThree_bg
  have hhb : rowThree.hbar ≤ (1.089658916 : ℝ) :=
    hbar_le rowThree (by norm_num) (by norm_num [Row.gridCount, rowThree])
  have hbt : sphereFactor 3 ≤ (1.139340519 : ℝ) :=
    sphereFactor_le 3 (by norm_num) (by norm_num [sphereFactorPow, Nat.choose_eq_factorial_div_factorial, Nat.factorial])
  have hAg : rowThree.Ag = (1/52 : ℝ) := by norm_num [Row.Ag, rowThree]
  have hM1 : rowThree.M1 rowThree.deltaStar ≤ ((0.334917653 : ℝ) + rowThree.Ag) ^ 2 :=
    M1_le rowThree _ (by norm_num) hbg (by norm_num) (cg_nonneg _)
      ((cg_sq_le rowThree hhb).trans (by norm_num [proxyA])) (Ag_nonneg _)
  have hM2 : rowThree.M2 rowThree.deltaStar ≤ (77.612580697 : ℝ) :=
    M2_le rowThree _ (by norm_num) hbg (by norm_num)
  have hexp0 : Real.exp (3560769/8450000000 : ℝ) ≤ (1.00042148158 : ℝ) := exp_ub' (by norm_num) (by norm_num [GMCNumerics.expPoly, GMCNumerics.expErr, Finset.sum_range_succ, Nat.factorial])
  have hexp : Real.exp (32 * rowThree.Ag ^ 2 * ((rowThree.deltaStar : ℚ) : ℝ) ^ 2) ≤ (1.00042148158 : ℝ) := by
    have e : 32 * rowThree.Ag ^ 2 * ((rowThree.deltaStar : ℚ) : ℝ) ^ 2 = (3560769/8450000000 : ℝ) := by
      norm_num [Row.Ag, rowThree]
    rw [e]; exact hexp0
  have hU : rowThree.Ugrid rowThree.deltaStar ≤ (0.05594022002 : ℝ) := by
    refine (Ugrid_le rowThree hes hw0 hwu varsigma_le (hbar_nonneg _) hhb (xl := (0.897603768015 : ℝ)) (by norm_num) hxl hexp
      P32_le hM1 hM2).trans ?_
    rw [hAg]
    rw [kappaH_ne_two (show (3 : ℕ) ≠ 2 by norm_num)]
    norm_num [rowThree, kappaQ1]
  have hH : rowThree.Hhist rowThree.deltaStar rowThree.D ≤ (12.625907528 : ℝ) :=
    (Hhist_le rowThree hη hD.le hC1 (sphereFactor_nonneg _) hbt hFb0 hFb hGb0 hGb hU).trans
      (by norm_num [rowThree])
  have hTp : ((rowThree.F : ℝ) / (rowThree.D : ℝ)) ^ 32 ≤ (0.060929293 : ℝ) ^ 31 := by norm_num [rowThree]
  have hu2 : frakU 3 2 (rowThree.D : ℝ) (rowThree.F : ℝ) ≤ (0.3315062 : ℝ) :=
    frakU_le_of (by norm_num) hD hF0.le hFD (by norm_num) hTp (r := (1657531/5801980 : ℝ)) (by norm_num)
      (by rw [Xsum_eq]; norm_num) (by norm_num [sigmaNorm])
  have hu3 : frakU 3 3 (rowThree.D : ℝ) (rowThree.F : ℝ) ≤ (0.0445408 : ℝ) :=
    frakU_le_of (by norm_num) hD hF0.le hFD (by norm_num) hTp (r := (55676/1450495 : ℝ)) (by norm_num)
      (by rw [Xsum_eq]; norm_num) (by norm_num [sigmaNorm])
  have hanc : (sigmaNorm 3 : ℝ) * Bbar32 (3 ^ (3 * 3)) (rowThree.D : ℝ) (rowThree.F : ℝ) ≤ (0.0078024 : ℝ) :=
    sigma_Bbar_le hD hF0.le hFD (by norm_num) hTp (r := (9753/1450495 : ℝ)) (by norm_num)
      (by rw [Xsum_eq]; norm_num) (by norm_num [sigmaNorm])
  have hP : ∑ ℓ ∈ Finset.range (3 + 1), frakU 3 ℓ (rowThree.D : ℝ) (rowThree.F : ℝ) * (1.11407732 : ℝ) ^ ℓ ≤ (2.58712142032 : ℝ) := by
    have e0 : frakU 3 0 (rowThree.D : ℝ) (rowThree.F : ℝ) = 1 := by simp [frakU]
    have e1 := frakU_le_one 3 1 (rowThree.D : ℝ) (rowThree.F : ℝ)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, e0]
    have y0 : (0 : ℝ) ≤ (1.11407732 : ℝ) := by norm_num
    calc _ ≤ 0 + 1 * (1.11407732 : ℝ) ^ 0 + 1 * (1.11407732 : ℝ) ^ 1 + (0.3315062 : ℝ) * (1.11407732 : ℝ) ^ 2 + (0.0445408 : ℝ) * (1.11407732 : ℝ) ^ 3  := by
          gcongr
      _ ≤ _ := by norm_num
  have hS : rowThree.Sinf (rowThree.D : ℝ) (rowThree.F : ℝ) ≤ (2.602422469 : ℝ) := by
    have hy : rowThree.xHist⁻¹ ≤ (1.11407732 : ℝ) := (inv_anti₀ (by norm_num) hxl).trans (by norm_num)
    refine (Sinf_le rowThree hD hF0.le hx0 hy (r := (0.1925 : ℝ)) (by norm_num) (by norm_num) (by norm_num) hanc hP).trans ?_
    norm_num
  have he : rowThree.eStar rowThree.deltaStar rowThree.D rowThree.F ≤ (0.0100322488793 : ℝ) :=
    (eStar_le rowThree hwl hw1 hD.le hx0 hxu (Sinf_nonneg rowThree hD hF0.le hx0) hS hH (by norm_num)).trans
      (by norm_num [rowThree])
  have hcap : nativeCap 3 (rowThree.g - rowThree.nu) (rowThree.D : ℝ) (rowThree.F : ℝ) ≤ (0.178494110000000001 : ℝ) :=
    (nativeCap_le hD hF0.le (r := 1 / 10 ^ 20)
      (Bbar32_crude hD hF0.le (Nat.one_le_pow _ _ (by norm_num)) (by norm_num) (by norm_num [rowThree]))).trans
      (by norm_num [sigmaNorm, rowThree])
  have hc0 := nativeCap_nonneg (d := 3) (k := rowThree.g - rowThree.nu) hD hF0.le
  have hθ : (rowThree.F : ℝ) < rowThree.thetaR := rowThree_bad1
  unfold Row.badCharge
  exact bad_lt hF0 hθ hc0 hcap (q := (0.62357707407 : ℝ)) (by norm_num) (by norm_num) he (by norm_num)
    (by norm_num [Row.thetaR, rowThree])

/-- The group 2 fields for `rowThree`. -/
theorem rowThree_group2 : Group2 rowThree :=
  ⟨rowThree_hist1, rowThree_hist2, rowThree_avg4, rowThree_avg5, rowThree_bad1, rowThree_bad2⟩

end GMCExplicitDelta.Certificates

