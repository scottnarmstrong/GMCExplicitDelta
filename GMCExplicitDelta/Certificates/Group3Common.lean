module

public import GMCExplicitDelta.Certificates.Group3Haar
public import GMCExplicitDelta.Contract.DerivedBarrier
public import GMCExplicitDelta.Contract.Rows
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Numeric obligations, group 3: row-independent lemmas

Enclosures of `3^q`, of the localization bracket, of `K_s`, `B_tail`, `τ_abs`, the b₀ bound, the
planar derivative-test identities and the barrier monotonicity lemmas. All statements are about an
arbitrary `row : Row d`; the row files supply the numerals.
-/

@[expose] public section

open Real

namespace GMCExplicitDelta.Certificates.G3

open GMCExplicitDelta.Contract GMCExplicitDelta.Haar

variable {d : ℕ}

/-! ### π and powers of three -/

/-- Lower enclosure of `π` (20 digits). -/
def PL : ℚ := 314159265358979323846 / 10 ^ 20

/-- Upper enclosure of `π` (20 digits). -/
def PH : ℚ := 314159265358979323847 / 10 ^ 20

theorem PL_le_pi : (PL : ℝ) ≤ π := by
  have := (GMCNumerics.pi_enclosure).1
  unfold PL; push_cast; norm_num at this ⊢; linarith

theorem pi_le_PH : π ≤ (PH : ℝ) := by
  have := (GMCNumerics.pi_enclosure).2
  unfold PH; push_cast; norm_num at this ⊢; linarith

theorem exp_lb {c yl : ℝ} (hc : -1 ≤ c ∧ c ≤ 1)
    (h : yl ≤ GMCNumerics.expPoly c 14 - GMCNumerics.expErr c 14) : yl ≤ Real.exp c :=
  GMCNumerics.le_exp_of_poly (n := 14) (abs_le.2 hc) (by norm_num) h

theorem exp_ub {c yu : ℝ} (hc : -1 ≤ c ∧ c ≤ 1)
    (h : GMCNumerics.expPoly c 14 + GMCNumerics.expErr c 14 ≤ yu) : Real.exp c ≤ yu :=
  GMCNumerics.exp_le_of_poly (n := 14) (abs_le.2 hc) (by norm_num) h

theorem three_rpow_enc {q cl cu yl yu : ℝ} (hq : 0 ≤ q)
    (hcl : cl ≤ q * 1.098612288668109) (hcu : q * 1.098612288668111 ≤ cu)
    (hyl : yl ≤ Real.exp cl) (hyu : Real.exp cu ≤ yu) :
    yl ≤ (3 : ℝ) ^ q ∧ (3 : ℝ) ^ q ≤ yu := by
  obtain ⟨l1, l2⟩ := GMCNumerics.log_three_enclosure
  have h1 := mul_le_mul_of_nonneg_right l1 hq
  have h2 := mul_le_mul_of_nonneg_right l2 hq
  rw [Real.rpow_def_of_pos (by norm_num)]
  constructor
  · exact hyl.trans (Real.exp_le_exp.2 (by nlinarith))
  · exact (Real.exp_le_exp.2 (by nlinarith)).trans hyu

theorem qs_enc (row : Row d) {q cl cu yl yu : ℝ} (hq : 2 * (row.s : ℝ) = q) (hq0 : 0 ≤ q)
    (hcl : cl ≤ q * 1.098612288668109) (hcu : q * 1.098612288668111 ≤ cu)
    (hyl : yl ≤ Real.exp cl) (hyu : Real.exp cu ≤ yu) : yl ≤ row.qs ∧ row.qs ≤ yu := by
  unfold Row.qs; rw [hq]; exact three_rpow_enc hq0 hcl hcu hyl hyu

theorem us_enc (row : Row d) {q cl cu yl yu : ℝ} (hq : (row.s : ℝ) = q) (hq0 : 0 ≤ q)
    (hcl : cl ≤ q * 1.098612288668109) (hcu : q * 1.098612288668111 ≤ cu)
    (hyl : yl ≤ Real.exp cl) (hyu : Real.exp cu ≤ yu) : yl ≤ row.us ∧ row.us ≤ yu := by
  unfold Row.us; rw [hq]; exact three_rpow_enc hq0 hcl hcu hyl hyu

theorem rhoS_le (row : Row d) {qu ρu : ℝ} (hq : row.qs ≤ qu) (h : qu / 3 ≤ ρu) :
    row.rhoS ≤ ρu := by
  rw [rhoS_eq]; linarith

/-! ### Coefficient majorants (H12 hypotheses) -/

theorem haar_majorants' (row : Row d) (hd2 : d = 2 → ∀ k : ℕ, 1 ≤ k →
      row.haarL k ≤ 9 / 9 ^ k ∧ 1 + 2 * row.haarL k ≤ 3) :
    (∀ k, 1 ≤ k → row.haarL k ≤ row.L1sharp * (9 / 9 ^ k)) ∧
    (∀ k, 1 ≤ k → row.haarH k ≤ row.Hsharp) := by
  refine ⟨?_, ?_⟩
  · intro k hk
    by_cases hd : d = 2
    · rw [Row.L1sharp, ite_eq_left hd, one_mul]; exact (hd2 hd k hk).1
    · have hfirst : row.haarL 1 = row.etaOmega * (5 * π ^ 2 / 54) := by
        simp only [Row.haarL, hd, false_and, ite_false, pow_one,
          div_self (by norm_num : (9 : ℝ) ≠ 0), mul_one]
      rw [Row.L1sharp, ite_eq_right hd, hfirst, Row.haarL, ite_eq_right (by simp only [hd, false_and,
        not_false_eq_true])]
  · intro k hk
    by_cases hd : d = 2
    · have heta : row.etaOmega = 1 := by norm_num [Row.etaOmega, Row.omegaEff, hd]
      simpa only [Row.haarH, heta, hd, Nat.cast_ofNat, one_mul, Row.Hsharp, ite_true] using
        (hd2 hd k hk).2
    · have hkpow : (9 : ℝ) ≤ 9 ^ k := by
        simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 9) hk
      have hl : row.haarL k ≤ row.haarL 1 := by
        have hc : 0 ≤ row.etaOmega * (5 * π ^ 2 / 54) := by
          unfold Row.etaOmega
          positivity
        have hr : (9 : ℝ) / 9 ^ k ≤ 1 := (div_le_one (by positivity)).2 hkpow
        simpa only [Row.haarL, hd, false_and, ite_false, pow_one,
          div_self (by norm_num : (9 : ℝ) ≠ 0), mul_one] using
          mul_le_mul_of_nonneg_left hr hc
      have he : 0 ≤ row.etaOmega := by unfold Row.etaOmega; positivity
      unfold Row.haarH Row.Hsharp
      rw [ite_eq_right hd]
      exact mul_le_mul_of_nonneg_left
        (add_le_add_right (mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg d)) 1) he

/-- O.geo.2, the coefficient part for `d = 2`. -/
theorem geo2_haarL_two (row : Row 2) : ∀ k : ℕ, 1 ≤ k →
    row.haarL k ≤ 9 / 9 ^ k ∧ 1 + 2 * row.haarL k ≤ 3 := by
  intro k hk
  have hp3 : (3 : ℝ) < π := Real.pi_gt_three
  have hp4 : π < 3.15 := Real.pi_lt_d2
  have h9 : (0 : ℝ) < 9 / 9 ^ k := by positivity
  have h9le : (9 : ℝ) / 9 ^ k ≤ 1 := by
    have hkpow : (9 : ℝ) ≤ 9 ^ k := by
      simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 9) hk
    exact (div_le_one (by positivity)).2 hkpow
  have heta : row.etaOmega = 1 := by norm_num [Row.etaOmega, Row.omegaEff]
  have hL : row.haarL k ≤ 9 / 9 ^ k := by
    by_cases h1 : k = 1
    · subst h1
      simp only [Row.haarL, and_self, ite_true, pow_one, div_self (by norm_num : (9 : ℝ) ≠ 0)]
      have : (81 : ℝ) ≤ π ^ 4 := by
        have := pow_le_pow_left₀ (by norm_num) hp3.le 4
        norm_num at this; linarith
      have h243 : 243 / (10 * π ^ 4) ≤ 4 / 5 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
      linarith
    · have hne : ¬ (2 = 2 ∧ k = 1) := fun h => h1 h.2
      rw [Row.haarL, ite_eq_right hne, heta, one_mul]
      have : 5 * π ^ 2 / 54 ≤ 1 := by nlinarith
      calc 5 * π ^ 2 / 54 * (9 / 9 ^ k) ≤ 1 * (9 / 9 ^ k) :=
            mul_le_mul_of_nonneg_right this h9.le
        _ = _ := one_mul _
  exact ⟨hL, by linarith⟩

/-! ### The localization bracket and `c_ν` -/

theorem locBracket_enc (row : Row d) {ω : ℝ} {pl ph : ℚ} (hω : row.omegaEff = ω) (hω0 : 0 < ω)
    (hpl : 0 < pl) (h1 : (pl : ℝ) ≤ π) (h2 : π ≤ (ph : ℝ)) {bl bu : ℝ}
    (hbl : bl ≤ 1 - 2 * ω + 4 * ω / (ph : ℝ) - 1 / (3 : ℝ) ^ row.nu -
      (ph : ℝ) / (8 * ω * ((3 : ℝ) ^ row.nu) ^ 2))
    (hbu : 1 - 2 * ω + 4 * ω / (pl : ℝ) - 1 / (3 : ℝ) ^ row.nu -
      (pl : ℝ) / (8 * ω * ((3 : ℝ) ^ row.nu) ^ 2) ≤ bu) :
    bl ≤ row.locBracket ∧ row.locBracket ≤ bu := by
  have hpl' : (0 : ℝ) < pl := by exact_mod_cast hpl
  have hpi : 0 < π := lt_of_lt_of_le hpl' h1
  have hph : (0 : ℝ) < ph := lt_of_lt_of_le hpi h2
  have hN : (0 : ℝ) < ((3 : ℝ) ^ row.nu) ^ 2 := by positivity
  unfold Row.locBracket Row.cosMean
  rw [hω]
  have a1 : 4 * ω / (ph : ℝ) ≤ 4 * ω / π := div_le_div_of_nonneg_left (by positivity) hpi h2
  have a2 : 4 * ω / π ≤ 4 * ω / (pl : ℝ) := div_le_div_of_nonneg_left (by positivity) hpl' h1
  have b1 : π / (8 * ω * ((3 : ℝ) ^ row.nu) ^ 2) ≤ (ph : ℝ) / (8 * ω * ((3 : ℝ) ^ row.nu) ^ 2) :=
    div_le_div_of_nonneg_right h2 (by positivity)
  have b2 : (pl : ℝ) / (8 * ω * ((3 : ℝ) ^ row.nu) ^ 2) ≤ π / (8 * ω * ((3 : ℝ) ^ row.nu) ^ 2) :=
    div_le_div_of_nonneg_right h1 (by positivity)
  constructor <;> linarith

theorem cNu_enc (row : Row d) {bl bu cl cu : ℝ} (hb : bl ≤ row.locBracket ∧ row.locBracket ≤ bu)
    (hbl0 : 0 ≤ bl) (hcl : cl ≤ bl ^ d) (hcu : bu ^ d ≤ cu) :
    cl ≤ row.cNu ∧ row.cNu ≤ cu := by
  unfold Row.cNu
  exact ⟨hcl.trans (pow_le_pow_left₀ hbl0 hb.1 d),
    (pow_le_pow_left₀ (hbl0.trans hb.1) hb.2 d).trans hcu⟩

/-! ### `K_s`, `B_tail`, `τ_abs` -/

/-- Rational majorant of `L₁^♯`. -/
def L1uQ (d : ℕ) (η pl ph : ℚ) : ℚ := if d = 2 then 1 else Lu d η pl ph 1

/-- Rational majorant of `𝖧^♯`. -/
def HsuQ (d : ℕ) (η pl ph : ℚ) : ℚ := if d = 2 then 3 else Hu d η pl ph 1

theorem L1sharp_le (row : Row d) {η pl ph : ℚ} (hη : row.etaOmega = (η : ℝ)) (hpl : 0 < pl)
    (h1 : (pl : ℝ) ≤ π) (h2 : π ≤ (ph : ℝ)) : row.L1sharp ≤ (L1uQ d η pl ph : ℝ) := by
  unfold Row.L1sharp L1uQ
  by_cases hd : d = 2
  · simp [hd]
  · simp only [hd, ite_false]; exact haarL_le_Lu row hη hpl h1 h2 1

theorem Hsharp_le (row : Row d) {η pl ph : ℚ} (hη : row.etaOmega = (η : ℝ)) (hpl : 0 < pl)
    (h1 : (pl : ℝ) ≤ π) (h2 : π ≤ (ph : ℝ)) : row.Hsharp ≤ (HsuQ d η pl ph : ℝ) := by
  unfold Row.Hsharp HsuQ
  by_cases hd : d = 2
  · simp [hd]
  · simp only [hd, ite_false]
    have := haarH_le_Hu row hη hpl h1 h2 1
    unfold Row.haarH at this
    rw [hη] at this
    simpa only [Hu, hη] using this

theorem Ks_le_cert (row : Row d) {qu : ℚ} (hq1 : 1 < row.qs) (hq : row.qs ≤ qu)
    (hqu : (qu : ℝ) < 9) {L1 Hs : ℚ} (hL1 : row.L1sharp ≤ (L1 : ℝ)) (hHs : row.Hsharp ≤ (Hs : ℝ))
    {K : ℚ} (hK : 0 ≤ K) (h : 9 * L1 + Hs * (qu - 1) / (1 - qu / 9) ≤ K ^ 2) :
    row.Ks ≤ K := by
  unfold Row.Ks
  refine Real.sqrt_le_iff.2 ⟨by exact_mod_cast hK, ?_⟩
  have hq9 : row.qs < 9 := lt_of_le_of_lt hq hqu
  have hd : 0 < 1 - row.qs / 9 := sub_pos.mpr ((div_lt_one (by norm_num : (0 : ℝ) < 9)).2 hq9)
  have hdu : 0 < 1 - (qu : ℝ) / 9 := sub_pos.mpr ((div_lt_one (by norm_num : (0 : ℝ) < 9)).2 hqu)
  have hH0 := Hsharp_nonneg row
  have hratio : (row.qs - 1) / (1 - row.qs / 9) ≤ ((qu : ℝ) - 1) / (1 - (qu : ℝ) / 9) :=
    div_le_div₀ (by linarith) (by linarith) hdu (by linarith)
  have h1 : row.Hsharp * ((row.qs - 1) / (1 - row.qs / 9)) ≤
      (Hs : ℝ) * (((qu : ℝ) - 1) / (1 - (qu : ℝ) / 9)) :=
    mul_le_mul hHs hratio (div_nonneg (by linarith) hd.le) (hH0.trans hHs)
  have h' : (9 * L1 + Hs * (qu - 1) / (1 - qu / 9) : ℚ) ≤ K ^ 2 := h
  have h'' : (9 * (L1 : ℝ) + (Hs : ℝ) * (((qu : ℝ) - 1) / (1 - (qu : ℝ) / 9))) ≤ (K : ℝ) ^ 2 := by
    have := (Rat.cast_le (K := ℝ)).2 h'
    push_cast at this
    simpa only [mul_div_assoc] using this
  calc 9 * row.L1sharp + row.Hsharp * (row.qs - 1) / (1 - row.qs / 9)
      = 9 * row.L1sharp + row.Hsharp * ((row.qs - 1) / (1 - row.qs / 9)) := by rw [mul_div_assoc]
    _ ≤ 9 * (L1 : ℝ) + (Hs : ℝ) * (((qu : ℝ) - 1) / (1 - (qu : ℝ) / 9)) := by linarith
    _ ≤ _ := h''

theorem Ks_nonneg (row : Row d) : 0 ≤ row.Ks := Real.sqrt_nonneg _

theorem tail_le (row : Row d) {uu Ksu : ℚ} (hKs : row.Ks ≤ (Ksu : ℝ)) (hu : row.us ≤ (uu : ℝ))
    (huu : (uu : ℝ) < 3) (n : ℕ) :
    row.Ks * (row.us / 3) ^ n / (1 - row.us / 3) ≤
      (Ksu : ℝ) * ((uu : ℝ) / 3) ^ n / (1 - (uu : ℝ) / 3) := by
  have hu0 := us_pos row
  have hd : 0 < 1 - (uu : ℝ) / 3 := by linarith
  have huu0 : (0 : ℝ) ≤ uu := hu0.le.trans hu
  have hd' : 0 < 1 - row.us / 3 := by linarith
  have hK0 := Ks_nonneg row
  have hKsu : 0 ≤ (Ksu : ℝ) := hK0.trans hKs
  have h1 : (row.us / 3) ^ n ≤ ((uu : ℝ) / 3) ^ n :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have h2 : row.Ks * (row.us / 3) ^ n ≤ (Ksu : ℝ) * ((uu : ℝ) / 3) ^ n :=
    mul_le_mul hKs h1 (by positivity) hKsu
  have h3 : 1 / (1 - row.us / 3) ≤ 1 / (1 - (uu : ℝ) / 3) :=
    one_div_le_one_div_of_le hd (by linarith)
  calc row.Ks * (row.us / 3) ^ n / (1 - row.us / 3)
      = row.Ks * (row.us / 3) ^ n * (1 / (1 - row.us / 3)) := by rw [mul_one_div]
    _ ≤ (Ksu : ℝ) * ((uu : ℝ) / 3) ^ n * (1 / (1 - (uu : ℝ) / 3)) :=
        mul_le_mul h2 h3 (by positivity) (by positivity)
    _ = _ := by rw [mul_one_div]

theorem tailD_le (row : Row d) {ρu Ksu : ℚ} (K : ℕ) (hKs : row.Ks ≤ (Ksu : ℝ))
    (hρ : row.rhoS ≤ (ρu : ℝ)) (hρ1 : (ρu : ℝ) < 1) :
    row.Ks * row.rhoS ^ (K + 1) * ((K : ℝ) + 1 - (K : ℝ) * row.rhoS) / (1 - row.rhoS) ^ 2 ≤
      (Ksu : ℝ) * (ρu : ℝ) ^ (K + 1) * ((K : ℝ) + 1) / (1 - (ρu : ℝ)) ^ 2 := by
  have hρ0 : 0 ≤ row.rhoS := by unfold Row.rhoS; positivity
  have hρu0 : (0 : ℝ) ≤ ρu := hρ0.trans hρ
  have hK0 := Ks_nonneg row
  have hKsu : 0 ≤ (Ksu : ℝ) := hK0.trans hKs
  have hρ1' : row.rhoS < 1 := lt_of_le_of_lt hρ hρ1
  have hd : 0 < 1 - (ρu : ℝ) := by linarith
  have hd' : 0 < 1 - row.rhoS := by linarith
  have hKc : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have h1 : (K : ℝ) + 1 - (K : ℝ) * row.rhoS ≤ (K : ℝ) + 1 := by nlinarith
  have h1' : 0 ≤ (K : ℝ) + 1 - (K : ℝ) * row.rhoS := by nlinarith
  have h2 : row.rhoS ^ (K + 1) ≤ (ρu : ℝ) ^ (K + 1) := pow_le_pow_left₀ hρ0 hρ _
  have h3 : row.Ks * row.rhoS ^ (K + 1) ≤ (Ksu : ℝ) * (ρu : ℝ) ^ (K + 1) :=
    mul_le_mul hKs h2 (by positivity) hKsu
  have hnum : row.Ks * row.rhoS ^ (K + 1) * ((K : ℝ) + 1 - (K : ℝ) * row.rhoS) ≤
      (Ksu : ℝ) * (ρu : ℝ) ^ (K + 1) * ((K : ℝ) + 1) :=
    mul_le_mul h3 h1 h1' (by positivity)
  have hden : (1 - (ρu : ℝ)) ^ 2 ≤ (1 - row.rhoS) ^ 2 := pow_le_pow_left₀ hd.le (by linarith) 2
  exact div_le_div₀ (by positivity) hnum (by positivity) hden

theorem minSeries_nonneg {q Λ H : ℝ} (hq : 0 ≤ q) (hΛ : 0 ≤ Λ) (hH : 0 ≤ H) :
    0 ≤ minSeries q Λ H :=
  tsum_nonneg fun j => mul_nonneg (pow_nonneg hq j) (le_min hΛ (div_nonneg hH (by positivity)))

theorem haarB_ge_sqrt (row : Row d) {k : ℕ} (hk : 1 ≤ k) (hq1 : 1 < row.qs) :
    √(row.haarL k) ≤ row.haarB k := by
  unfold Row.haarB
  rw [ite_eq_right (by omega)]
  refine Real.sqrt_le_sqrt ?_
  have := minSeries_nonneg (le_trans zero_le_one hq1.le) (haarL_nonneg row k) (haarH_nonneg row k)
  nlinarith

theorem haarB0_ge_sqrt (row : Row d) (hq1 : 1 < row.qs) (hR0 : 0 ≤ row.Rcirc)
    (hH0 : 0 ≤ row.Hcirc) : √(row.Lcirc) ≤ row.haarB 0 := by
  unfold Row.haarB
  rw [ite_eq_left rfl]
  refine Real.sqrt_le_sqrt ?_
  have := minSeries_nonneg (le_trans zero_le_one hq1.le) hR0 hH0
  nlinarith

theorem Sb_ge_two (row : Row d) (hsum : Summable row.haarB) : row.haarB 0 + row.haarB 1 ≤ row.Sb := by
  have := hsum.sum_le_tsum (Finset.range 2) (fun k _ => haarB_nonneg row k)
  unfold Row.Sb
  simpa [Finset.sum_range_succ] using this

theorem affine_sq_enc {a b x pl ph : ℝ} (ha : 0 ≤ a) (hpl : 0 ≤ pl) (h1 : pl ≤ x) (h2 : x ≤ ph) :
    a * pl ^ 2 + b ≤ a * x ^ 2 + b ∧ a * x ^ 2 + b ≤ a * ph ^ 2 + b := by
  have e1 : pl ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hpl h1 2
  have e2 : x ^ 2 ≤ ph ^ 2 := pow_le_pow_left₀ (hpl.trans h1) h2 2
  constructor <;> nlinarith

theorem cosMean_enc (row : Row d) {ω : ℝ} {pl ph : ℚ} (hω : row.omegaEff = ω) (hω0 : 0 < ω)
    (hpl : 0 < pl) (h1 : (pl : ℝ) ≤ π) (h2 : π ≤ (ph : ℝ)) :
    1 - 2 * ω + 4 * ω / (ph : ℝ) ≤ row.cosMean ∧ row.cosMean ≤ 1 - 2 * ω + 4 * ω / (pl : ℝ) := by
  have hpl' : (0 : ℝ) < pl := by exact_mod_cast hpl
  have hpi : 0 < π := lt_of_lt_of_le hpl' h1
  unfold Row.cosMean
  rw [hω]
  have a1 : 4 * ω / (ph : ℝ) ≤ 4 * ω / π := div_le_div_of_nonneg_left (by positivity) hpi h2
  have a2 : 4 * ω / π ≤ 4 * ω / (pl : ℝ) := div_le_div_of_nonneg_left (by positivity) hpl' h1
  constructor <;> linarith

theorem Rcirc_enc (row : Row d) {Lcl Lcu mlo mhi : ℝ}
    (hL : Lcl ≤ row.Lcirc ∧ row.Lcirc ≤ Lcu) (hm : mlo ≤ row.cosMean ∧ row.cosMean ≤ mhi)
    (hmlo : 0 ≤ mlo) :
    Lcl - mhi ^ (2 * d) ≤ row.Rcirc ∧ row.Rcirc ≤ Lcu - mlo ^ (2 * d) := by
  unfold Row.Rcirc
  have e1 : mlo ^ (2 * d) ≤ row.cosMean ^ (2 * d) := pow_le_pow_left₀ hmlo hm.1 _
  have e2 : row.cosMean ^ (2 * d) ≤ mhi ^ (2 * d) :=
    pow_le_pow_left₀ (hmlo.trans hm.1) hm.2 _
  constructor <;> linarith [hL.1, hL.2]

theorem Btail_le (row : Row d) {uu Ksu : ℚ} (hKs : row.Ks ≤ (Ksu : ℝ)) (hu : row.us ≤ (uu : ℝ))
    (huu : (uu : ℝ) < 3) :
    0 ≤ row.Btail ∧ row.Btail ≤ (Ksu : ℝ) * ((uu : ℝ) / 3) ^ (row.Kprime + 1) /
      (1 - (uu : ℝ) / 3) := by
  have hu0 := us_pos row
  have hu3 : row.us < 3 := lt_of_le_of_lt hu huu
  have hd' : 0 < 1 - row.us / 3 := by linarith
  have hK0 := Ks_nonneg row
  refine ⟨?_, tail_le row hKs hu huu _⟩
  unfold Row.Btail
  exact div_nonneg (mul_nonneg hK0 (pow_nonneg (by positivity) _)) hd'.le

theorem tauAbs_le (row : Row d) {cl Ksu ρu : ℝ} (hcl : 0 < cl) (hc : cl ≤ row.cNu)
    (hKs : row.Ks ≤ Ksu) (hρ : row.rhoS ≤ ρu) (hρ1 : ρu < 1) (hε : 0 ≤ (row.epsilon : ℝ))
    (hR : 0 ≤ (row.R : ℝ)) (hρ0 : 0 ≤ row.rhoS) :
    0 ≤ row.tauAbs ∧ row.tauAbs ≤ (1 + (row.epsilon : ℝ)) * (row.R : ℝ) * Ksu * ρu ^ (row.g + 1) /
      (cl * (1 - ρu)) := by
  have hK0 := Ks_nonneg row
  have hρ1' : row.rhoS < 1 := lt_of_le_of_lt hρ hρ1
  have hc0 : 0 < row.cNu := lt_of_lt_of_le hcl hc
  constructor
  · unfold Row.tauAbs
    have : 0 < 1 - row.rhoS := by linarith
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hR) hK0)
      (pow_nonneg hρ0 _)) (mul_nonneg hc0.le this.le)
  · unfold Row.tauAbs
    have h1 : row.rhoS ^ (row.g + 1) ≤ ρu ^ (row.g + 1) := pow_le_pow_left₀ hρ0 hρ _
    have h2 : row.Ks * row.rhoS ^ (row.g + 1) ≤ Ksu * ρu ^ (row.g + 1) :=
      mul_le_mul hKs h1 (by positivity) (hK0.trans hKs)
    have hd : 0 < 1 - ρu := by linarith
    have hd' : 0 < 1 - row.rhoS := by linarith
    have h3 : cl * (1 - ρu) ≤ row.cNu * (1 - row.rhoS) :=
      mul_le_mul hc (by linarith) hd.le hc0.le
    have hKsu : 0 ≤ Ksu := hK0.trans hKs
    have hρu0 : 0 ≤ ρu := hρ0.trans hρ
    have hnum : (1 + (row.epsilon : ℝ)) * (row.R : ℝ) * row.Ks * row.rhoS ^ (row.g + 1) ≤
        (1 + (row.epsilon : ℝ)) * (row.R : ℝ) * Ksu * ρu ^ (row.g + 1) := by
      have := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ (1 + (row.epsilon : ℝ)) * (row.R : ℝ))
      simpa only [mul_assoc] using this
    exact div_le_div₀ (by positivity) hnum (by positivity) h3


theorem Hsharp_pos (row : Row d) (hη : 0 < row.etaOmega) : 0 < row.Hsharp := by
  unfold Row.Hsharp
  split_ifs
  · norm_num
  · have := haarL_nonneg row 1
    positivity

theorem Ks_pos (row : Row d) (hH : 0 < row.Hsharp) (hq1 : 1 < row.qs) (hq9 : row.qs < 9) :
    0 < row.Ks := by
  unfold Row.Ks
  refine Real.sqrt_pos.2 ?_
  have hd : 0 < 1 - row.qs / 9 := sub_pos.mpr ((div_lt_one (by norm_num : (0 : ℝ) < 9)).2 hq9)
  have := L1sharp_nonneg row
  have h2 : 0 < row.Hsharp * (row.qs - 1) / (1 - row.qs / 9) :=
    div_pos (mul_pos hH (by linarith)) hd
  linarith

theorem tauAbs_pos (row : Row d) (hc : 0 < row.cNu) (hK : 0 < row.Ks) (hρ0 : 0 < row.rhoS)
    (hρ1 : row.rhoS < 1) (hε : 0 < (row.epsilon : ℝ)) (hR : 0 < (row.R : ℝ)) :
    0 < row.tauAbs := by
  unfold Row.tauAbs
  have : 0 < 1 - row.rhoS := by linarith
  positivity

theorem inv_sqrt_le {x rl ri : ℝ} (hrl : 0 < rl) (h : rl ^ 2 ≤ x) (hri : 1 / rl ≤ ri) :
    (√x)⁻¹ ≤ ri := by
  have h1 : rl ≤ √x := Real.le_sqrt_of_sq_le h
  have h2 := inv_anti₀ hrl h1
  rw [one_div] at hri
  linarith

theorem sigmaA_of_ne {F : ℝ} (hd : d ≠ 2) : sigmaA d F = √(1 + 2 * F) := by simp [sigmaA, hd]
theorem sigmaA_of_eq {F : ℝ} (hd : d = 2) : sigmaA d F = 1 := by simp [sigmaA, hd]
theorem sigmaV_of_ne (hd : d ≠ 2) : sigmaV d = √2 := by simp [sigmaV, hd]
theorem sigmaV_of_eq (hd : d = 2) : sigmaV d = 1 := by simp [sigmaV, hd]
theorem sigmaB_of_ne {F : ℝ} (hd : d ≠ 2) : sigmaB d F = 1 + 2 * F := by simp [sigmaB, hd]
theorem sigmaB_of_eq {F : ℝ} (hd : d = 2) : sigmaB d F = 1 := by simp [sigmaB, hd]


theorem haarL_one_ge (row : Row 2) {ph : ℚ} (h2 : π ≤ (ph : ℝ)) :
    1 / 5 + 243 / (10 * (ph : ℝ) ^ 4) ≤ row.haarL 1 := by
  have hpi := Real.pi_pos
  have h4 : π ^ 4 ≤ (ph : ℝ) ^ 4 := pow_le_pow_left₀ hpi.le h2 4
  simp only [Row.haarL, and_self, ite_true]
  have : 243 / (10 * (ph : ℝ) ^ 4) ≤ 243 / (10 * π ^ 4) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  linarith

/-! ### The b₀ bound -/

theorem energy0_le {q qu L0 Λ H Lc Rc Hc : ℝ} (hq1 : 1 < q) (hq : q ≤ qu) (hqu : qu < 9)
    (hΛ : 0 ≤ Λ) (hH : 0 ≤ H) (hL : L0 ≤ Lc) (hR : Λ ≤ Rc) (hHc : H ≤ Hc) (J : ℕ) :
    L0 + (q - 1) * minSeries q Λ H ≤
      Lc + Rc * (qu ^ J - 1) + Hc * (qu - 1) * (qu / 9) ^ J / (1 - qu / 9) := by
  have hq0 : 0 ≤ q := le_trans zero_le_one hq1.le
  have hq9 : q < 9 := lt_of_le_of_lt hq hqu
  have hd : 0 < 1 - q / 9 := sub_pos.mpr ((div_lt_one (by norm_num : (0 : ℝ) < 9)).2 hq9)
  have hdu : 0 < 1 - qu / 9 := sub_pos.mpr ((div_lt_one (by norm_num : (0 : ℝ) < 9)).2 hqu)
  have hs := minSeries_le_split hq1 hq9 hΛ hH J
  have h1 := mul_le_mul_of_nonneg_left hs (sub_nonneg.mpr hq1.le)
  have halg : (q - 1) * (Λ * (q ^ J - 1) / (q - 1) + H * (q / 9) ^ J / (1 - q / 9)) =
      Λ * (q ^ J - 1) + H * ((q - 1) / (1 - q / 9)) * (q / 9) ^ J := by
    field_simp [(sub_pos.mpr hq1).ne', hd.ne']
  have hqJ : q ^ J ≤ qu ^ J := pow_le_pow_left₀ hq0 hq J
  have hq1J : 1 ≤ q ^ J := one_le_pow₀ hq1.le
  have hratio : (q - 1) / (1 - q / 9) ≤ (qu - 1) / (1 - qu / 9) :=
    div_le_div₀ (by linarith) (by linarith) hdu (by linarith)
  have e1 : Λ * (q ^ J - 1) ≤ Rc * (qu ^ J - 1) :=
    mul_le_mul hR (by linarith) (by linarith) (hΛ.trans hR)
  have e2 : H * ((q - 1) / (1 - q / 9)) * (q / 9) ^ J ≤
      Hc * ((qu - 1) / (1 - qu / 9)) * (qu / 9) ^ J := by
    have hr0 : 0 ≤ (q - 1) / (1 - q / 9) := div_nonneg (by linarith) hd.le
    have hr0u : 0 ≤ (qu - 1) / (1 - qu / 9) := div_nonneg (by linarith) hdu.le
    exact mul_le_mul (mul_le_mul hHc hratio hr0 (hH.trans hHc))
      (pow_le_pow_left₀ (by positivity) (by linarith) J) (by positivity)
      (mul_nonneg (hH.trans hHc) hr0u)
  calc
    L0 + (q - 1) * minSeries q Λ H ≤
        L0 + (q - 1) * (Λ * (q ^ J - 1) / (q - 1) + H * (q / 9) ^ J / (1 - q / 9)) := by
      linarith only [h1]
    _ = L0 + (Λ * (q ^ J - 1) + H * ((q - 1) / (1 - q / 9)) * (q / 9) ^ J) := by rw [halg]
    _ ≤ Lc + (Rc * (qu ^ J - 1) + Hc * ((qu - 1) / (1 - qu / 9)) * (qu / 9) ^ J) := by
      linarith only [hL, e1, e2]
    _ = _ := by ring

/-- The numerical check for `b₀ ≤ r`. -/
abbrev chkB0 (Lc Rc Hc qu : ℚ) (J : ℕ) (r : ℚ) : Prop :=
  0 ≤ r ∧ Lc + Rc * (qu ^ J - 1) + Hc * (qu - 1) * (qu / 9) ^ J / (1 - qu / 9) ≤ r ^ 2

theorem haarB0_le_cert (row : Row d) (hq1 : 1 < row.qs) {qu : ℚ} (hq : row.qs ≤ qu)
    (hqu : (qu : ℝ) < 9) {Lc Rc Hc : ℚ} (hR0 : 0 ≤ row.Rcirc) (hH0 : 0 ≤ row.Hcirc)
    (hL : row.Lcirc ≤ (Lc : ℝ)) (hR : row.Rcirc ≤ (Rc : ℝ)) (hH : row.Hcirc ≤ (Hc : ℝ)) {J : ℕ}
    {r : ℚ} (hc : chkB0 Lc Rc Hc qu J r) : row.haarB 0 ≤ r := by
  unfold Row.haarB
  rw [ite_eq_left rfl]
  refine Real.sqrt_le_iff.2 ⟨by exact_mod_cast hc.1, ?_⟩
  refine (energy0_le hq1 hq hqu hR0 hH0 hL hR hH J).trans ?_
  have : ((Lc + Rc * (qu ^ J - 1) + Hc * (qu - 1) * (qu / 9) ^ J / (1 - qu / 9) : ℚ) : ℝ) ≤
      ((r ^ 2 : ℚ) : ℝ) := by exact_mod_cast hc.2
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_sub,
    Rat.cast_one, Rat.cast_ofNat] using this

end GMCExplicitDelta.Certificates.G3
