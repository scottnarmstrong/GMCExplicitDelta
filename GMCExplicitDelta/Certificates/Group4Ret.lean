module

public import GMCExplicitDelta.Certificates.Group4Dnext

/-!
# Group 4: assembling the four returns from rational bounds

Row-independent lemmas: from `0 ≤ freshMoment ≤ c₁` and `0 ≤ ∑ bandRow · x₀^r ≤ c₂` and
rational bounds for `e^{γ_h}`, `cosh`, `sinh`, deduce `post < D`, `meanpost < F`, `seed < D`,
`meanseed < F` (`d = 2`, resp. `d ≠ 2`).
-/

@[expose] public section

open Matrix GMCNumerics GMCExplicitDelta.Contract Real

namespace GMCExplicitDelta.Certificates.Group4

/-! ### Fresh moment and seed sums for a row -/

theorem fresh_bounds {d : ℕ} (row : Row d) {B : List (List ℕ)} {ρ : List ℕ} {S fuel c : ℕ}
    {Fp : ℝ} (hS : 0 < S) (hk : row.h < 2 ^ fuel)
    (hB : Dom S 33 (bandMatrix (row.deltaStar : ℝ)) B)
    (hD : 0 < (row.D : ℝ)) (hF : 0 < (row.F : ℝ)) (hFn : 0 < row.Fnext (row.F : ℝ))
    (hDF : row.Dnext (row.D : ℝ) (row.F : ℝ) ≤ Fp)
    (hρ0 : ρ.getD 0 0 = S)
    (hρ : ∀ r : ℕ, 1 ≤ r → r ≤ 32 →
      row.Fnext (row.F : ℝ) ^ (32 - r) * Fp ^ (32 * (r - 1)) ≤ (((ρ.getD r 0 : ℕ) : ℝ) / S) ^ 31)
    (hchk : checkVec S 33 fuel B row.h ρ 32 c = true) :
    0 ≤ row.freshMoment (row.deltaStar : ℝ) (row.D : ℝ) (row.F : ℝ) ∧
      row.freshMoment (row.deltaStar : ℝ) (row.D : ℝ) (row.F : ℝ) ≤ (c : ℝ) / S := by
  have hDn := Dnext_pos row hD hF
  have hv := domV_profile row hS hρ0 hFn hDn hDF hρ
  exact freshSum_bounds hS hk hB hchk hv

theorem seed_bounds {d : ℕ} (row : Row d) {B : List (List ℕ)} {S fuel c X : ℕ}
    (hS : 0 < S) (hk : row.h < 2 ^ fuel)
    (hB : Dom S 33 (bandMatrix (row.deltaStar : ℝ)) B)
    (hx0 : 0 ≤ row.seedPoint (row.deltaStar : ℝ))
    (hx : row.seedPoint (row.deltaStar : ℝ) ≤ (X : ℝ) / S)
    (hchk : checkVec S 33 fuel B row.h (powList S X) 32 c = true) :
    0 ≤ ∑ r : Fin 33, bandRow (row.deltaStar : ℝ) row.h r *
        row.seedPoint (row.deltaStar : ℝ) ^ (r : ℕ) ∧
      ∑ r : Fin 33, bandRow (row.deltaStar : ℝ) row.h r *
        row.seedPoint (row.deltaStar : ℝ) ^ (r : ℕ) ≤ (c : ℝ) / S :=
  freshSum_bounds hS hk hB hchk (domV_pow hS hx0 hx)

/-! ### The map `Φ` -/

theorem sinh_nonneg' {γ : ℝ} (hγ : 0 ≤ γ) : 0 ≤ Real.sinh γ := by
  rw [Real.sinh_eq]
  have : Real.exp (-γ) ≤ Real.exp γ := Real.exp_le_exp.2 (by linarith)
  linarith

theorem one_le_cosh' (x : ℝ) : 1 ≤ Real.cosh x := by
  rw [Real.cosh_eq]
  linarith [Real.add_one_le_exp x, Real.add_one_le_exp (-x)]

theorem sphereFactorPow_nonneg (d : ℕ) : (0 : ℝ) ≤ (sphereFactorPow d : ℝ) := by
  have : (0 : ℚ) ≤ sphereFactorPow d := by
    unfold sphereFactorPow; split_ifs <;> positivity
  exact_mod_cast this

theorem PhiMap_le_bound {γ j Cu Shu Ru : ℝ} (hγ : 0 ≤ γ) (hj : 0 ≤ j) (hC : Real.cosh γ ≤ Cu)
    (hSh : Real.sinh γ ≤ Shu) (hR : √(j * (j + 2)) ≤ Ru) :
    PhiMap γ j ≤ (1 + j) * Cu - 1 + Ru * Shu := by
  unfold PhiMap
  have hs : 0 ≤ Real.sinh γ := sinh_nonneg' hγ
  have h1 : (1 + j) * Real.cosh γ ≤ (1 + j) * Cu :=
    mul_le_mul_of_nonneg_left hC (by linarith)
  have h2 : √(j * (j + 2)) * Real.sinh γ ≤ Ru * Shu :=
    mul_le_mul hR hSh hs ((Real.sqrt_nonneg _).trans hR)
  linarith

theorem PhiMap_mono {γ j j' : ℝ} (hγ : 0 ≤ γ) (hj : 0 ≤ j) (hjj : j ≤ j') :
    PhiMap γ j ≤ PhiMap γ j' := by
  unfold PhiMap
  have hs : 0 ≤ Real.sinh γ := sinh_nonneg' hγ
  have hc : 0 ≤ Real.cosh γ := (Real.cosh_pos γ).le
  have h1 : (1 + j) * Real.cosh γ ≤ (1 + j') * Real.cosh γ :=
    mul_le_mul_of_nonneg_right (by linarith) hc
  have h2 : √(j * (j + 2)) ≤ √(j' * (j' + 2)) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have h3 := mul_le_mul_of_nonneg_right h2 hs
  linarith

theorem cosh_le_of_exp {γ a b : ℝ} (ha : Real.exp γ ≤ a) (hb : Real.exp (-γ) ≤ b) :
    Real.cosh γ ≤ (a + b) / 2 := by
  rw [Real.cosh_eq]; linarith

theorem sinh_le_of_exp {γ a b : ℝ} (ha : Real.exp γ ≤ a) (hb : b ≤ Real.exp (-γ)) :
    Real.sinh γ ≤ (a - b) / 2 := by
  rw [Real.sinh_eq]; linarith

theorem exp_two_mul_le {γ a : ℝ} (ha : Real.exp γ ≤ a) : Real.exp (2 * γ) ≤ a ^ 2 := by
  rw [two_mul, Real.exp_add, ← sq]
  exact pow_le_pow_left₀ (Real.exp_pos _).le ha 2

theorem exp_up {q b : ℝ} (hq : |q| ≤ 1) (h : expPoly q 10 + expErr q 10 ≤ b) :
    Real.exp q ≤ b :=
  exp_le_of_poly (n := 10) hq (by norm_num) h

theorem exp_lo {q y : ℝ} (hq : |q| ≤ 1) (h : y ≤ expPoly q 10 - expErr q 10) :
    y ≤ Real.exp q :=
  le_exp_of_poly (n := 10) hq (by norm_num) h

/-! ### The bundles -/

theorem rets_two (row : Row 2) {c1 c2 a1 Fnr : ℝ}
    (hD : 0 < (row.D : ℝ))
    (hfm : 0 ≤ row.freshMoment (row.deltaStar : ℝ) (row.D : ℝ) (row.F : ℝ) ∧
      row.freshMoment (row.deltaStar : ℝ) (row.D : ℝ) (row.F : ℝ) ≤ c1)
    (hsd : 0 ≤ ∑ r : Fin 33, bandRow (row.deltaStar : ℝ) row.h r *
        row.seedPoint (row.deltaStar : ℝ) ^ (r : ℕ) ∧
      ∑ r : Fin 33, bandRow (row.deltaStar : ℝ) row.h r *
        row.seedPoint (row.deltaStar : ℝ) ^ (r : ℕ) ≤ c2)
    (hβ : (sphereFactorPow 2 : ℝ) * c1 < (row.D : ℝ) ^ 32) (hs : c2 < (row.D : ℝ) ^ 32)
    (hE : Real.exp (row.gammaH (row.deltaStar : ℝ)) ≤ a1)
    (hFn : row.Fnext (row.F : ℝ) = Fnr) (hFnpos : 0 ≤ Fnr)
    (hmp : a1 * (1 + Fnr) - 1 < (row.F : ℝ)) (hms : a1 - 1 < (row.F : ℝ)) :
    row.post (row.deltaStar : ℝ) (row.D : ℝ) (row.F : ℝ) < (row.D : ℝ) ∧
    row.meanpost (row.deltaStar : ℝ) (row.F : ℝ) < (row.F : ℝ) ∧
    row.seed (row.deltaStar : ℝ) < (row.D : ℝ) ∧
    row.meanseed (row.deltaStar : ℝ) < (row.F : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Row.post, Row.sym, ↓reduceIte]
    have hb := sphereFactorPow_nonneg 2
    refine rpow32_lt (mul_nonneg hb hfm.1) hD.le ?_
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hfm.2 hb) hβ
  · simp only [Row.meanpost, ↓reduceIte]
    rw [hFn]
    have := mul_le_mul_of_nonneg_right hE (by linarith : (0 : ℝ) ≤ 1 + Fnr)
    linarith
  · simp only [Row.seed]
    exact rpow32_lt hsd.1 hD.le (lt_of_le_of_lt hsd.2 hs)
  · simp only [Row.meanseed, ↓reduceIte]
    linarith

theorem rets_ge3 {d : ℕ} (row : Row d) (hd : d ≠ 2) {c1 c2 a1 b1 b2 e2 Fnr su Ru : ℝ}
    (hD : 0 < (row.D : ℝ))
    (hfm : 0 ≤ row.freshMoment (row.deltaStar : ℝ) (row.D : ℝ) (row.F : ℝ) ∧
      row.freshMoment (row.deltaStar : ℝ) (row.D : ℝ) (row.F : ℝ) ≤ c1)
    (hsd : 0 ≤ ∑ r : Fin 33, bandRow (row.deltaStar : ℝ) row.h r *
        row.seedPoint (row.deltaStar : ℝ) ^ (r : ℕ) ∧
      ∑ r : Fin 33, bandRow (row.deltaStar : ℝ) row.h r *
        row.seedPoint (row.deltaStar : ℝ) ^ (r : ℕ) ≤ c2)
    (hγ : 0 ≤ row.gammaH (row.deltaStar : ℝ))
    (hsu0 : 0 ≤ su) (hβ : (sphereFactorPow d : ℝ) * c1 ≤ su ^ 32)
    (hs : c2 < (row.D : ℝ) ^ 32)
    (hE1 : Real.exp (row.gammaH (row.deltaStar : ℝ)) ≤ a1)
    (hE2 : Real.exp (-row.gammaH (row.deltaStar : ℝ)) ≤ b1)
    (hE3 : b2 ≤ Real.exp (-row.gammaH (row.deltaStar : ℝ)))
    (hR : su * (su + 2) ≤ Ru ^ 2) (hR0 : 0 ≤ Ru)
    (hΦ : (1 + su) * ((a1 + b1) / 2) - 1 + Ru * ((a1 - b2) / 2) < (row.D : ℝ))
    (he2 : a1 ^ 2 ≤ e2)
    (hFn : row.Fnext (row.F : ℝ) = Fnr) (hFnpos : 0 ≤ Fnr)
    (hmp : e2 * Fnr + (e2 - 1) / 2 < (row.F : ℝ)) (hms : (e2 - 1) / 2 < (row.F : ℝ)) :
    row.post (row.deltaStar : ℝ) (row.D : ℝ) (row.F : ℝ) < (row.D : ℝ) ∧
    row.meanpost (row.deltaStar : ℝ) (row.F : ℝ) < (row.F : ℝ) ∧
    row.seed (row.deltaStar : ℝ) < (row.D : ℝ) ∧
    row.meanseed (row.deltaStar : ℝ) < (row.F : ℝ) := by
  have hE2' : Real.exp (2 * row.gammaH (row.deltaStar : ℝ)) ≤ e2 :=
    (exp_two_mul_le hE1).trans he2
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Row.post, if_neg hd, Row.sym]
    have hb := sphereFactorPow_nonneg d
    have hsym : ((sphereFactorPow d : ℝ) * row.freshMoment (row.deltaStar : ℝ) (row.D : ℝ)
        (row.F : ℝ)) ^ ((1 : ℝ) / 32) ≤ su :=
      rpow32_le (mul_nonneg hb hfm.1) hsu0
        ((mul_le_mul_of_nonneg_left hfm.2 hb).trans hβ)
    have hsym0 : 0 ≤ ((sphereFactorPow d : ℝ) * row.freshMoment (row.deltaStar : ℝ) (row.D : ℝ)
        (row.F : ℝ)) ^ ((1 : ℝ) / 32) := Real.rpow_nonneg (mul_nonneg hb hfm.1) _
    refine lt_of_le_of_lt ((PhiMap_mono hγ hsym0 hsym).trans ?_) hΦ
    exact PhiMap_le_bound hγ hsu0 (cosh_le_of_exp hE1 hE2) (sinh_le_of_exp hE1 hE3)
      (Real.sqrt_le_iff.2 ⟨hR0, hR⟩)
  · simp only [Row.meanpost, if_neg hd]
    rw [hFn]
    have := mul_le_mul_of_nonneg_right hE2' hFnpos
    linarith
  · simp only [Row.seed]
    exact rpow32_lt hsd.1 hD.le (lt_of_le_of_lt hsd.2 hs)
  · simp only [Row.meanseed, if_neg hd]
    linarith

end GMCExplicitDelta.Certificates.Group4
