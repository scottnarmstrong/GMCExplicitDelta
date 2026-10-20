module

public import GMCExplicitDelta.Certificates.Group4PowerThree
public import GMCExplicitDelta.Certificates.Group4Ret
public import GMCExplicitDelta.Contract.Rows

/-!
# Group 4, row three: `ret1`–`ret4`

The kernel certificates `bandUp_three`, `rho_check_three`, `power_check_three` are combined with
`Dom_bandUp`, the profile/`D_next` bounds and the exponential enclosures.
-/

@[expose] public section

open Matrix GMCNumerics GMCExplicitDelta.Contract Real

namespace GMCExplicitDelta.Certificates.Group4

theorem bandDom_three : Dom (10 ^ 24) 33 (bandMatrix (rowThree.deltaStar : ℝ)) bandThree := by
  rw [← bandUp_three]
  refine Dom_bandUp (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_
  · norm_num [rowThree]
  · norm_num [proxyA, rowThree]
  · norm_num [ratioC3, proxyA, rowThree, Nat.factorial]

theorem gamma_three : rowThree.gammaH (rowThree.deltaStar : ℝ) = (1286824076307837 / 50000000000000000 : ℝ) := by
  norm_num [Row.gammaH, kappaQ1, rowThree]


theorem rowThree_rets :
    rowThree.post (rowThree.deltaStar : ℝ) (rowThree.D : ℝ) (rowThree.F : ℝ) < (rowThree.D : ℝ) ∧
    rowThree.meanpost (rowThree.deltaStar : ℝ) (rowThree.F : ℝ) < (rowThree.F : ℝ) ∧
    rowThree.seed (rowThree.deltaStar : ℝ) < (rowThree.D : ℝ) ∧
    rowThree.meanseed (rowThree.deltaStar : ℝ) < (rowThree.F : ℝ) := by
  have hS : 0 < 10 ^ 24 := by norm_num
  have hD : 0 < (rowThree.D : ℝ) := by norm_num [rowThree]
  have hF : 0 < (rowThree.F : ℝ) := by norm_num [rowThree]
  have hFn : rowThree.Fnext (rowThree.F : ℝ) = (47952995983241 : ℝ) / 332000000000000 := by
    norm_num [Row.Fnext, Row.tStar, Row.Mwin, rowThree]
  have hFn0 : 0 < rowThree.Fnext (rowThree.F : ℝ) := by rw [hFn]; norm_num
  have hDF : rowThree.Dnext (rowThree.D : ℝ) (rowThree.F : ℝ) ≤ (178494110000000000000000000001 : ℝ) / 1000000000000000000000000000000 :=
    (Dnext_le rowThree hD hF (by norm_num) (by norm_num [rowThree])
      (by norm_num [sigmaNorm, rowThree])).trans (le_of_eq (by norm_num [rowThree]))
  obtain ⟨hρ0, hρ⟩ := rhoOK_sound (by norm_num) (by norm_num) (by norm_num) rho_check_three
  have hρ' : ∀ r : ℕ, 1 ≤ r → r ≤ 32 →
      rowThree.Fnext (rowThree.F : ℝ) ^ (32 - r) * ((178494110000000000000000000001 : ℝ) / 1000000000000000000000000000000) ^ (32 * (r - 1)) ≤
        (((rhoThree.getD r 0 : ℕ) : ℝ) / ((10 ^ 24 : ℕ) : ℝ)) ^ 31 := by
    intro r h1 h2
    rw [hFn]
    exact hρ r h1 h2
  have hchk := power_check_three
  simp only [Bool.and_eq_true] at hchk
  have hk : rowThree.h < 2 ^ 10 := by norm_num [rowThree]
  have hfm := fresh_bounds rowThree hS hk bandDom_three hD hF hFn0 hDF hρ0 hρ' hchk.1
  have hE1 : Real.exp (rowThree.gammaH (rowThree.deltaStar : ℝ)) ≤ 1.026070526 := by
    rw [gamma_three]
    refine exp_up (by rw [abs_of_pos (by norm_num)]; norm_num) ?_
    norm_num [expPoly, expErr, Finset.sum_range_succ, Nat.factorial, abs_of_pos]
  have hE2 : Real.exp (-rowThree.gammaH (rowThree.deltaStar : ℝ)) ≤ 0.974591880 := by
    rw [gamma_three]
    refine exp_up (by rw [abs_neg, abs_of_pos (by norm_num)]; norm_num) ?_
    norm_num [expPoly, expErr, Finset.sum_range_succ, Nat.factorial, abs_of_pos, abs_neg]
  have hE3 : 0.974591877 ≤ Real.exp (-rowThree.gammaH (rowThree.deltaStar : ℝ)) := by
    rw [gamma_three]
    refine exp_lo (by rw [abs_neg, abs_of_pos (by norm_num)]; norm_num) ?_
    norm_num [expPoly, expErr, Finset.sum_range_succ, Nat.factorial, abs_of_pos, abs_neg]
  have hcosh := cosh_le_of_exp hE1 hE2
  have hx0 : 0 ≤ rowThree.seedPoint (rowThree.deltaStar : ℝ) := by
    simp only [Row.seedPoint, if_neg (by norm_num : ¬ (3 : ℕ) = 2)]
    linarith [one_le_cosh' (rowThree.gammaH (rowThree.deltaStar : ℝ))]
  have hx : rowThree.seedPoint (rowThree.deltaStar : ℝ) ≤ ((10 ^ 21 : ℕ) : ℝ) / ((10 ^ 24 : ℕ) : ℝ) := by
    simp only [Row.seedPoint, if_neg (by norm_num : ¬ (3 : ℕ) = 2)]
    have h2 : ((1.026070526 + 0.974591880) / 2 : ℝ) ≤ 1 + 1 / 1000 := by norm_num
    have h3 : ((10 ^ 21 : ℕ) : ℝ) / ((10 ^ 24 : ℕ) : ℝ) = 1 / 1000 := by norm_num
    rw [h3]
    linarith
  have hsd := seed_bounds rowThree hS hk bandDom_three hx0 hx hchk.2
  refine rets_ge3 rowThree (by norm_num) (su := (64797401 / 25000000 : ℝ)) (Ru := 3.449886545) (e2 := 1.052820725) (Fnr := (47952995983241 : ℝ) / 332000000000000) hD hfm hsd ?_ ?_ ?_ ?_ hE1 hE2 hE3 ?_ (by norm_num) ?_ ?_ hFn (by norm_num) ?_ ?_
  · rw [gamma_three]; norm_num
  · norm_num
  · norm_num [cFreshThree, rowThree, sphereFactorPow, Nat.choose_eq_factorial_div_factorial, Nat.factorial]
  · norm_num [cSeedThree, rowThree]
  · norm_num
  · norm_num [rowThree]
  · norm_num
  · norm_num [rowThree]
  · norm_num [rowThree]

end GMCExplicitDelta.Certificates.Group4
