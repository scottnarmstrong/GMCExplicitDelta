module

public import GMCExplicitDelta.Certificates.Group4PowerTwo
public import GMCExplicitDelta.Certificates.Group4Ret
public import GMCExplicitDelta.Contract.Rows

/-!
# Group 4, row two: `ret1`–`ret4`

The kernel certificates `bandUp_two`, `rho_check_two`, `power_check_two` are combined with
`Dom_bandUp`, the profile/`D_next` bounds and the exponential enclosures.
-/

@[expose] public section

open Matrix GMCNumerics GMCExplicitDelta.Contract Real

namespace GMCExplicitDelta.Certificates.Group4

theorem bandDom_two : Dom (10 ^ 24) 33 (bandMatrix (rowTwo.deltaStar : ℝ)) bandTwo := by
  rw [← bandUp_two]
  refine Dom_bandUp (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_
  · norm_num [rowTwo]
  · norm_num [proxyA, rowTwo]
  · norm_num [ratioC3, proxyA, rowTwo, Nat.factorial]

theorem gamma_two : rowTwo.gammaH (rowTwo.deltaStar : ℝ) = (25487437774212783 / 400000000000000000 : ℝ) := by
  norm_num [Row.gammaH, kappaQ1, rowTwo]


theorem rowTwo_rets :
    rowTwo.post (rowTwo.deltaStar : ℝ) (rowTwo.D : ℝ) (rowTwo.F : ℝ) < (rowTwo.D : ℝ) ∧
    rowTwo.meanpost (rowTwo.deltaStar : ℝ) (rowTwo.F : ℝ) < (rowTwo.F : ℝ) ∧
    rowTwo.seed (rowTwo.deltaStar : ℝ) < (rowTwo.D : ℝ) ∧
    rowTwo.meanseed (rowTwo.deltaStar : ℝ) < (rowTwo.F : ℝ) := by
  have hS : 0 < 10 ^ 24 := by norm_num
  have hD : 0 < (rowTwo.D : ℝ) := by norm_num [rowTwo]
  have hF : 0 < (rowTwo.F : ℝ) := by norm_num [rowTwo]
  have hFn : rowTwo.Fnext (rowTwo.F : ℝ) = (19836532783151 : ℝ) / 41400000000000 := by
    norm_num [Row.Fnext, Row.tStar, Row.Mwin, rowTwo]
  have hFn0 : 0 < rowTwo.Fnext (rowTwo.F : ℝ) := by rw [hFn]; norm_num
  have hDF : rowTwo.Dnext (rowTwo.D : ℝ) (rowTwo.F : ℝ) ≤ (576477490000000000000000000001 : ℝ) / 1000000000000000000000000000000 :=
    (Dnext_le rowTwo hD hF (by norm_num) (by norm_num [rowTwo])
      (by norm_num [sigmaNorm, rowTwo])).trans (le_of_eq (by norm_num [rowTwo]))
  obtain ⟨hρ0, hρ⟩ := rhoOK_sound (by norm_num) (by norm_num) (by norm_num) rho_check_two
  have hρ' : ∀ r : ℕ, 1 ≤ r → r ≤ 32 →
      rowTwo.Fnext (rowTwo.F : ℝ) ^ (32 - r) * ((576477490000000000000000000001 : ℝ) / 1000000000000000000000000000000) ^ (32 * (r - 1)) ≤
        (((rhoTwo.getD r 0 : ℕ) : ℝ) / ((10 ^ 24 : ℕ) : ℝ)) ^ 31 := by
    intro r h1 h2
    rw [hFn]
    exact hρ r h1 h2
  have hchk := power_check_two
  simp only [Bool.and_eq_true] at hchk
  have hk : rowTwo.h < 2 ^ 10 := by norm_num [rowTwo]
  have hfm := fresh_bounds rowTwo hS hk bandDom_two hD hF hFn0 hDF hρ0 hρ' hchk.1
  have hsd := seed_bounds rowTwo hS hk bandDom_two (by simp [Row.seedPoint]) (by simp [Row.seedPoint]) hchk.2
  have hE : Real.exp (rowTwo.gammaH (rowTwo.deltaStar : ℝ)) ≤ 1.065792438 := by
    rw [gamma_two]
    refine exp_up (by rw [abs_of_pos (by norm_num)]; norm_num) ?_
    norm_num [expPoly, expErr, Finset.sum_range_succ, Nat.factorial, abs_of_pos]
  refine rets_two rowTwo hD hfm hsd ?_ ?_ hE hFn (by norm_num) ?_ ?_
  · norm_num [cFreshTwo, rowTwo, sphereFactorPow, Nat.choose_eq_factorial_div_factorial, Nat.factorial]
  · norm_num [cSeedTwo, rowTwo]
  · norm_num [rowTwo]
  · norm_num [rowTwo]

end GMCExplicitDelta.Certificates.Group4
