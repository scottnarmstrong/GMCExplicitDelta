module

public import GMCExplicitDelta.Certificates.Group2Bad
public import GMCExplicitDelta.Contract.Rows

/-!
# Numeric obligations, group 2, for the row `rowTwo`

O.hist.1, O.hist.2, O.avg.4, O.avg.5, O.bad.1, O.bad.2 (generated numerals; checked by `norm_num`).
-/

@[expose] public section

open Real

namespace GMCExplicitDelta.Certificates

open GMCExplicitDelta.Contract

theorem rowTwo_x : (0.811983777323 : ℝ) ≤ rowTwo.xHist ∧ rowTwo.xHist ≤ (0.811983777324 : ℝ) := by
  have hq : -(2 * (rowTwo.s : ℝ)) + ((2 : ℕ) : ℝ) / 32 = (-0.18958 : ℝ) := by norm_num [rowTwo]
  rw [xHist_eq rowTwo hq]
  have : (0.811983777323 : ℝ) ≤ Real.exp (-0.208274917685701 : ℝ) := exp_lb' (by norm_num) (by norm_num [GMCNumerics.expPoly, GMCNumerics.expErr, Finset.sum_range_succ, Nat.factorial])
  have hl := this
  have : Real.exp (-0.2082749176857 : ℝ) ≤ (0.811983777324 : ℝ) := exp_ub' (by norm_num) (by norm_num [GMCNumerics.expPoly, GMCNumerics.expErr, Finset.sum_range_succ, Nat.factorial])
  have hu := this
  exact three_rpow_neg_enclosure (cl := (-0.208274917685701 : ℝ)) (cu := (-0.2082749176857 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num) hl hu

theorem rowTwo_w : (0.758101357146 : ℝ) ≤ rowTwo.wHaar ∧ rowTwo.wHaar ≤ (0.758101357147 : ℝ) := by
  have hq : -(2 * (rowTwo.s : ℝ)) = (-0.25208 : ℝ) := by norm_num [rowTwo]
  rw [wHaar_eq rowTwo hq]
  have : (0.758101357146 : ℝ) ≤ Real.exp (-0.276938185727458 : ℝ) := exp_lb' (by norm_num) (by norm_num [GMCNumerics.expPoly, GMCNumerics.expErr, Finset.sum_range_succ, Nat.factorial])
  have hl := this
  have : Real.exp (-0.276938185727456 : ℝ) ≤ (0.758101357147 : ℝ) := exp_ub' (by norm_num) (by norm_num [GMCNumerics.expPoly, GMCNumerics.expErr, Finset.sum_range_succ, Nat.factorial])
  have hu := this
  exact three_rpow_neg_enclosure (cl := (-0.276938185727458 : ℝ)) (cu := (-0.276938185727456 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num) hl hu

theorem rowTwo_bg : (0.11601518035 : ℝ) ≤ rowTwo.bg rowTwo.deltaStar := by
  have hq : -(2 * (rowTwo.s : ℝ)) + ((2 : ℕ) : ℝ) / 32 = (-0.18958 : ℝ) := by norm_num [rowTwo]
  refine bg_ge rowTwo (c := (0.0922597373348144 : ℝ)) hq (by norm_num) ?_ (by norm_num)
  rw [kappaH_two]
  norm_num [rowTwo, proxyA]

theorem rowTwo_zF : rowTwo.zF rowTwo.deltaStar ≤ (0.976524496445 : ℝ) := by
  obtain ⟨hxl, hxu⟩ := rowTwo_x
  have hx0 : 0 < rowTwo.xHist := lt_of_lt_of_le (by norm_num) hxl
  have : Real.exp (0.1845194746696288 : ℝ) ≤ (1.202640402082 : ℝ) := exp_ub' (by norm_num) (by norm_num [GMCNumerics.expPoly, GMCNumerics.expErr, Finset.sum_range_succ, Nat.factorial])
  refine zF_le rowTwo (c := (0.1845194746696288 : ℝ)) (xu := (0.811983777324 : ℝ)) (eu := (1.202640402082 : ℝ)) ?_ hx0 hxu this (by norm_num)
  rw [kappaH_two]
  norm_num [rowTwo, proxyA]

theorem rowTwo_zG : rowTwo.zG rowTwo.deltaStar ≤ (0.850317857826 : ℝ) := by
  obtain ⟨hxl, hxu⟩ := rowTwo_x
  have hx0 : 0 < rowTwo.xHist := lt_of_lt_of_le (by norm_num) hxl
  have : Real.exp (0.0461298686674072 : ℝ) ≤ (1.047210401946 : ℝ) := exp_ub' (by norm_num) (by norm_num [GMCNumerics.expPoly, GMCNumerics.expErr, Finset.sum_range_succ, Nat.factorial])
  refine zG_le rowTwo (c := (0.0461298686674072 : ℝ)) (xu := (0.811983777324 : ℝ)) (eu := (1.047210401946 : ℝ)) ?_ hx0 hxu this (by norm_num)
  rw [kappaH_two]
  norm_num [rowTwo, proxyA]

theorem rowTwo_hist1 : rowTwo.zG rowTwo.deltaStar < rowTwo.zF rowTwo.deltaStar ∧
    rowTwo.zF rowTwo.deltaStar < 1 := by
  obtain ⟨hxl, hxu⟩ := rowTwo_x
  have hx0 : 0 < rowTwo.xHist := lt_of_lt_of_le (by norm_num) hxl
  exact ⟨zG_lt_zF rowTwo hx0 (by norm_num [rowTwo]), lt_of_le_of_lt rowTwo_zF (by norm_num)⟩

theorem rowTwo_hist2 : 0 < rowTwo.bg rowTwo.deltaStar :=
  lt_of_lt_of_le (by norm_num) rowTwo_bg

theorem rowTwo_avg4 : (3 : ℝ) ^ (-(((2 : ℕ) : ℝ) / 2)) < rowTwo.xHist := by
  obtain ⟨hxl, hxu⟩ := rowTwo_x
  calc (3 : ℝ) ^ (-(((2 : ℕ) : ℝ) / 2)) ≤ (3 : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ = 3⁻¹ := Real.rpow_neg_one 3
    _ < rowTwo.xHist := lt_of_lt_of_le (by norm_num) hxl


theorem rowTwo_avg5 : frakU 2 rowTwo.historyCutoff (rowTwo.D : ℝ) (rowTwo.F : ℝ) < 1 := by
  have h : rowTwo.historyCutoff = 12 := rfl
  rw [h]
  exact frakU_twelve_lt_one (by norm_num [rowTwo]) (by norm_num [rowTwo]) (by norm_num [sigmaNorm])
    (by norm_num)

theorem rowTwo_bad1 : (rowTwo.F : ℝ) < rowTwo.thetaR := by
  norm_num [Row.thetaR, rowTwo]


theorem rowTwo_bad2 : rowTwo.badCharge rowTwo.deltaStar rowTwo.D rowTwo.F < rowTwo.badBudget := by
  have hD : (0 : ℝ) < (rowTwo.D : ℝ) := by norm_num [rowTwo]
  have hF0 : (0 : ℝ) < (rowTwo.F : ℝ) := by norm_num [rowTwo]
  have hFD : (rowTwo.F : ℝ) ≤ (rowTwo.D : ℝ) := by norm_num [rowTwo]
  have hδ : (0 : ℝ) ≤ (rowTwo.deltaStar : ℝ) := by norm_num [rowTwo]
  have hη : (0 : ℝ) < (rowTwo.eta : ℝ) := by norm_num [rowTwo]
  have hes : (0 : ℝ) < (rowTwo.epsSub : ℝ) := by norm_num [rowTwo]
  obtain ⟨hxl, hxu⟩ := rowTwo_x
  obtain ⟨hwl, hwu⟩ := rowTwo_w
  have hx0 : 0 < rowTwo.xHist := lt_of_lt_of_le (by norm_num) hxl
  have hw0 : 0 ≤ rowTwo.wHaar := by unfold Row.wHaar; positivity
  have hw1 : rowTwo.wHaar ≤ 1 := hwu.trans (by norm_num)
  have hzF := rowTwo_zF
  have hzG := rowTwo_zG
  have hzF0 := zF_nonneg rowTwo ((rowTwo.deltaStar : ℚ) : ℝ) hx0
  have hzG0 := zG_nonneg rowTwo ((rowTwo.deltaStar : ℚ) : ℝ) hx0
  have hAF0 := AF_nonneg (d := 2) hδ
  have hAG0 := AG_nonneg (d := 2) hδ
  have hAF : AF 2 ((rowTwo.deltaStar : ℚ) : ℝ) ≤ (0 : ℝ) := by rw [AF_two]
  have hAG : AG 2 ((rowTwo.deltaStar : ℚ) : ℝ) ≤ (0 : ℝ) := by rw [AG_two]
  have hFb : rowTwo.Fbar rowTwo.deltaStar ≤ (31.1627399565 : ℝ) := by
    unfold Row.Fbar
    exact (bracket_le (wl := (0.758101357146 : ℝ)) hwl hw1 hzF0 hzF (by norm_num) Ch_nonneg Ch_le hAF0 hAF).trans
      (by norm_num [rowTwo])
  have hGb : rowTwo.Gbar rowTwo.deltaStar ≤ (0.6674575455 : ℝ) := by
    unfold Row.Gbar
    exact (bracket_le (wl := (0.758101357146 : ℝ)) hwl hw1 hzG0 hzG (by norm_num) Ch_nonneg Ch_le hAG0 hAG).trans
      (by norm_num [rowTwo])
  have hFb0 : 0 ≤ rowTwo.Fbar rowTwo.deltaStar := by
    unfold Row.Fbar
    exact bracket_nonneg hw1 hzF0 (lt_of_le_of_lt hzF (by norm_num)) Ch_nonneg hAF0
  have hGb0 : 0 ≤ rowTwo.Gbar rowTwo.deltaStar := by
    unfold Row.Gbar
    exact bracket_nonneg hw1 hzG0 (lt_of_le_of_lt hzG (by norm_num)) Ch_nonneg hAG0
  have hC1 : rowTwo.C1 ≤ (1.044685245553 : ℝ) :=
    (C1_le rowTwo hwl hw1 hx0 hxu (by norm_num)).trans (by norm_num)
  have hbg := rowTwo_bg
  have hhb : rowTwo.hbar ≤ (1.06887252 : ℝ) :=
    hbar_le rowTwo (by norm_num) (by norm_num [Row.gridCount, rowTwo])
  have hbt : sphereFactor 2 ≤ (1.074827941 : ℝ) :=
    sphereFactor_le 2 (by norm_num) (by norm_num [sphereFactorPow, Nat.choose_eq_factorial_div_factorial, Nat.factorial])
  have hAg : rowTwo.Ag = (3/284 : ℝ) := by norm_num [Row.Ag, rowTwo]
  have hM1 : rowTwo.M1 rowTwo.deltaStar ≤ ((0.278755346 : ℝ) + rowTwo.Ag) ^ 2 :=
    M1_le rowTwo _ (by norm_num) hbg (by norm_num) (cg_nonneg _)
      ((cg_sq_le rowTwo hhb).trans (by norm_num [proxyA])) (Ag_nonneg _)
  have hM2 : rowTwo.M2 rowTwo.deltaStar ≤ (40.228278451 : ℝ) :=
    M2_le rowTwo _ (by norm_num) hbg (by norm_num)
  have hexp0 : Real.exp (483956001/1008200000000 : ℝ) ≤ (1.000480135067 : ℝ) := exp_ub' (by norm_num) (by norm_num [GMCNumerics.expPoly, GMCNumerics.expErr, Finset.sum_range_succ, Nat.factorial])
  have hexp : Real.exp (32 * rowTwo.Ag ^ 2 * ((rowTwo.deltaStar : ℚ) : ℝ) ^ 2) ≤ (1.000480135067 : ℝ) := by
    have e : 32 * rowTwo.Ag ^ 2 * ((rowTwo.deltaStar : ℚ) : ℝ) ^ 2 = (483956001/1008200000000 : ℝ) := by
      norm_num [Row.Ag, rowTwo]
    rw [e]; exact hexp0
  have hU : rowTwo.Ugrid rowTwo.deltaStar ≤ (0.141641059336 : ℝ) := by
    refine (Ugrid_le rowTwo hes hw0 hwu varsigma_le (hbar_nonneg _) hhb (xl := (0.811983777323 : ℝ)) (by norm_num) hxl hexp
      P32_le hM1 hM2).trans ?_
    rw [hAg]
    simp only [kappaH_two]
    norm_num [rowTwo]
  have hH : rowTwo.Hhist rowTwo.deltaStar rowTwo.D ≤ (1148.729346637 : ℝ) :=
    (Hhist_le rowTwo hη hD.le hC1 (sphereFactor_nonneg _) hbt hFb0 hFb hGb0 hGb hU).trans
      (by norm_num [rowTwo])
  have hTp : ((rowTwo.F : ℝ) / (rowTwo.D : ℝ)) ^ 32 ≤ (0.008589055 : ℝ) ^ 31 := by norm_num [rowTwo]
  have hu2 : frakU 2 2 (rowTwo.D : ℝ) (rowTwo.F : ℝ) ≤ (0.4367666 : ℝ) :=
    frakU_le_of (by norm_num) hD hF0.le hFD (by norm_num) hTp (r := (2183833/5425865 : ℝ)) (by norm_num)
      (by rw [Xsum_eq]; norm_num) (by norm_num [sigmaNorm])
  have hu3 : frakU 2 3 (rowTwo.D : ℝ) (rowTwo.F : ℝ) ≤ (0.0841216 : ℝ) :=
    frakU_le_of (by norm_num) hD hF0.le hFD (by norm_num) hTp (r := (420608/5425865 : ℝ)) (by norm_num)
      (by rw [Xsum_eq]; norm_num) (by norm_num [sigmaNorm])
  have hanc : (sigmaNorm 2 : ℝ) * Bbar32 (3 ^ (2 * 3)) (rowTwo.D : ℝ) (rowTwo.F : ℝ) ≤ (0.0196389 : ℝ) :=
    sigma_Bbar_le hD hF0.le hFD (by norm_num) hTp (r := (196389/10851730 : ℝ)) (by norm_num)
      (by rw [Xsum_eq]; norm_num) (by norm_num [sigmaNorm])
  have hP : ∑ ℓ ∈ Finset.range (3 + 1), frakU 2 ℓ (rowTwo.D : ℝ) (rowTwo.F : ℝ) * (1.231551699 : ℝ) ^ ℓ ≤ (3.051136456314 : ℝ) := by
    have e0 : frakU 2 0 (rowTwo.D : ℝ) (rowTwo.F : ℝ) = 1 := by simp [frakU]
    have e1 := frakU_le_one 2 1 (rowTwo.D : ℝ) (rowTwo.F : ℝ)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, e0]
    have y0 : (0 : ℝ) ≤ (1.231551699 : ℝ) := by norm_num
    calc _ ≤ 0 + 1 * (1.231551699 : ℝ) ^ 0 + 1 * (1.231551699 : ℝ) ^ 1 + (0.4367666 : ℝ) * (1.231551699 : ℝ) ^ 2 + (0.0841216 : ℝ) * (1.231551699 : ℝ) ^ 3  := by
          gcongr
      _ ≤ _ := by norm_num
  have hS : rowTwo.Sinf (rowTwo.D : ℝ) (rowTwo.F : ℝ) ≤ (3.127776658 : ℝ) := by
    have hy : rowTwo.xHist⁻¹ ≤ (1.231551699 : ℝ) := (inv_anti₀ (by norm_num) hxl).trans (by norm_num)
    refine (Sinf_le rowTwo hD hF0.le hx0 hy (r := (1/3 : ℝ)) (by norm_num) (by norm_num) (by norm_num) hanc hP).trans ?_
    norm_num
  have he : rowTwo.eStar rowTwo.deltaStar rowTwo.D rowTwo.F ≤ (0.0126345933836 : ℝ) :=
    (eStar_le rowTwo hwl hw1 hD.le hx0 hxu (Sinf_nonneg rowTwo hD hF0.le hx0) hS hH (by norm_num)).trans
      (by norm_num [rowTwo])
  have hcap : nativeCap 2 (rowTwo.g - rowTwo.nu) (rowTwo.D : ℝ) (rowTwo.F : ℝ) ≤ (0.576477490000000001 : ℝ) :=
    (nativeCap_le hD hF0.le (r := 1 / 10 ^ 20)
      (Bbar32_crude hD hF0.le (Nat.one_le_pow _ _ (by norm_num)) (by norm_num) (by norm_num [rowTwo]))).trans
      (by norm_num [sigmaNorm, rowTwo])
  have hc0 := nativeCap_nonneg (d := 2) (k := rowTwo.g - rowTwo.nu) hD hF0.le
  have hθ : (rowTwo.F : ℝ) < rowTwo.thetaR := rowTwo_bad1
  unfold Row.badCharge
  exact bad_lt hF0 hθ hc0 hcap (q := (1.218721164368 : ℝ)) (by norm_num) (by norm_num) he (by norm_num)
    (by norm_num [Row.thetaR, rowTwo])

/-- The group 2 fields for `rowTwo`. -/
theorem rowTwo_group2 : Group2 rowTwo :=
  ⟨rowTwo_hist1, rowTwo_hist2, rowTwo_avg4, rowTwo_avg5, rowTwo_bad1, rowTwo_bad2⟩

end GMCExplicitDelta.Certificates

