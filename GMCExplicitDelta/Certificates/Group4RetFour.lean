module

public import GMCExplicitDelta.Certificates.Group4PowerFour
public import GMCExplicitDelta.Certificates.Group4Ret
public import GMCExplicitDelta.Contract.Rows

/-!
# Group 4, row four: `ret1`–`ret4`

The kernel certificates `bandUp_four`, `rho_check_four`, `power_check_four` are combined with
`Dom_bandUp`, the profile/`D_next` bounds and the exponential enclosures.
-/

@[expose] public section

open Matrix GMCNumerics GMCExplicitDelta.Contract Real

namespace GMCExplicitDelta.Certificates.Group4

theorem bandDom_four : Dom (10 ^ 24) 33 (bandMatrix (rowFour.deltaStar : ℝ)) bandFour := by
  rw [← bandUp_four]
  refine Dom_bandUp (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_
  · norm_num [rowFour]
  · norm_num [proxyA, rowFour]
  · norm_num [ratioC3, proxyA, rowFour, Nat.factorial]

theorem gamma_four : rowFour.gammaH (rowFour.deltaStar : ℝ) = (60079352717799699 / 2500000000000000000 : ℝ) := by
  norm_num [Row.gammaH, kappaQ1, rowFour]


theorem rowFour_rets :
    rowFour.post (rowFour.deltaStar : ℝ) (rowFour.D : ℝ) (rowFour.F : ℝ) < (rowFour.D : ℝ) ∧
    rowFour.meanpost (rowFour.deltaStar : ℝ) (rowFour.F : ℝ) < (rowFour.F : ℝ) ∧
    rowFour.seed (rowFour.deltaStar : ℝ) < (rowFour.D : ℝ) ∧
    rowFour.meanseed (rowFour.deltaStar : ℝ) < (rowFour.F : ℝ) := by
  have hS : 0 < 10 ^ 24 := by norm_num
  have hD : 0 < (rowFour.D : ℝ) := by norm_num [rowFour]
  have hF : 0 < (rowFour.F : ℝ) := by norm_num [rowFour]
  have hFn : rowFour.Fnext (rowFour.F : ℝ) = (7797891827968 : ℝ) / 56500000000000 := by
    norm_num [Row.Fnext, Row.tStar, Row.Mwin, rowFour]
  have hFn0 : 0 < rowFour.Fnext (rowFour.F : ℝ) := by rw [hFn]; norm_num
  have hDF : rowFour.Dnext (rowFour.D : ℝ) (rowFour.F : ℝ) ≤ (169438720000000000000000000001 : ℝ) / 1000000000000000000000000000000 :=
    (Dnext_le rowFour hD hF (by norm_num) (by norm_num [rowFour])
      (by norm_num [sigmaNorm, rowFour])).trans (le_of_eq (by norm_num [rowFour]))
  obtain ⟨hρ0, hρ⟩ := rhoOK_sound (by norm_num) (by norm_num) (by norm_num) rho_check_four
  have hρ' : ∀ r : ℕ, 1 ≤ r → r ≤ 32 →
      rowFour.Fnext (rowFour.F : ℝ) ^ (32 - r) * ((169438720000000000000000000001 : ℝ) / 1000000000000000000000000000000) ^ (32 * (r - 1)) ≤
        (((rhoFour.getD r 0 : ℕ) : ℝ) / ((10 ^ 24 : ℕ) : ℝ)) ^ 31 := by
    intro r h1 h2
    rw [hFn]
    exact hρ r h1 h2
  have hchk := power_check_four
  simp only [Bool.and_eq_true] at hchk
  have hk : rowFour.h < 2 ^ 10 := by norm_num [rowFour]
  have hfm := fresh_bounds rowFour hS hk bandDom_four hD hF hFn0 hDF hρ0 hρ' hchk.1
  have hE1 : Real.exp (rowFour.gammaH (rowFour.deltaStar : ℝ)) ≤ 1.024322832 := by
    rw [gamma_four]
    refine exp_up (by rw [abs_of_pos (by norm_num)]; norm_num) ?_
    norm_num [expPoly, expErr, Finset.sum_range_succ, Nat.factorial, abs_of_pos]
  have hE2 : Real.exp (-rowFour.gammaH (rowFour.deltaStar : ℝ)) ≤ 0.976254723 := by
    rw [gamma_four]
    refine exp_up (by rw [abs_neg, abs_of_pos (by norm_num)]; norm_num) ?_
    norm_num [expPoly, expErr, Finset.sum_range_succ, Nat.factorial, abs_of_pos, abs_neg]
  have hE3 : 0.976254720 ≤ Real.exp (-rowFour.gammaH (rowFour.deltaStar : ℝ)) := by
    rw [gamma_four]
    refine exp_lo (by rw [abs_neg, abs_of_pos (by norm_num)]; norm_num) ?_
    norm_num [expPoly, expErr, Finset.sum_range_succ, Nat.factorial, abs_of_pos, abs_neg]
  have hcosh := cosh_le_of_exp hE1 hE2
  have hx0 : 0 ≤ rowFour.seedPoint (rowFour.deltaStar : ℝ) := by
    simp only [Row.seedPoint, if_neg (by norm_num : ¬ (4 : ℕ) = 2)]
    linarith [one_le_cosh' (rowFour.gammaH (rowFour.deltaStar : ℝ))]
  have hx : rowFour.seedPoint (rowFour.deltaStar : ℝ) ≤ ((10 ^ 21 : ℕ) : ℝ) / ((10 ^ 24 : ℕ) : ℝ) := by
    simp only [Row.seedPoint, if_neg (by norm_num : ¬ (4 : ℕ) = 2)]
    have h2 : ((1.024322832 + 0.976254723) / 2 : ℝ) ≤ 1 + 1 / 1000 := by norm_num
    have h3 : ((10 ^ 21 : ℕ) : ℝ) / ((10 ^ 24 : ℕ) : ℝ) = 1 / 1000 := by norm_num
    rw [h3]
    linarith
  have hsd := seed_bounds rowFour hS hk bandDom_four hx0 hx hchk.2
  refine rets_ge3 rowFour (by norm_num) (su := (228331649 / 100000000 : ℝ)) (Ru := 3.127325884) (e2 := 1.049237265) (Fnr := (7797891827968 : ℝ) / 56500000000000) hD hfm hsd ?_ ?_ ?_ ?_ hE1 hE2 hE3 ?_ (by norm_num) ?_ ?_ hFn (by norm_num) ?_ ?_
  · rw [gamma_four]; norm_num
  · norm_num
  · norm_num [cFreshFour, rowFour, sphereFactorPow, Nat.choose_eq_factorial_div_factorial, Nat.factorial]
  · norm_num [cSeedFour, rowFour]
  · norm_num
  · norm_num [rowFour]
  · norm_num
  · norm_num [rowFour]
  · norm_num [rowFour]

end GMCExplicitDelta.Certificates.Group4
