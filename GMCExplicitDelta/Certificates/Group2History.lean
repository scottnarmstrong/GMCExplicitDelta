module

public import GMCExplicitDelta.Certificates.Group2Averaging
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Numeric obligations, group 2: history constants

Generic upper bounds for the constants of `Contract/DerivedHistory.lean` (`F̄, Ḡ, C₁, M₁, M₂,
U_grid, H`) in terms of rational enclosures of their ingredients; the rows supply the numbers.
-/

@[expose] public section

open Real

namespace GMCExplicitDelta.Certificates

open GMCExplicitDelta.Contract

/-! ### Powers of three -/

theorem three_rpow_le {q c y : ℝ} (h1 : q * Real.log 3 ≤ c) (h2 : Real.exp c ≤ y) :
    (3 : ℝ) ^ q ≤ y := by
  rw [Real.rpow_def_of_pos (by norm_num)]
  calc Real.exp (Real.log 3 * q) ≤ Real.exp c := Real.exp_le_exp.2 (by linarith)
    _ ≤ y := h2

theorem le_three_rpow {q c y : ℝ} (h1 : c ≤ q * Real.log 3) (h2 : y ≤ Real.exp c) :
    y ≤ (3 : ℝ) ^ q := by
  rw [Real.rpow_def_of_pos (by norm_num)]
  calc y ≤ Real.exp c := h2
    _ ≤ Real.exp (Real.log 3 * q) := Real.exp_le_exp.2 (by linarith)

theorem xHist_eq {d : ℕ} (row : Row d) {q : ℝ} (hq : -(2 * (row.s : ℝ)) + (d : ℝ) / 32 = q) :
    row.xHist = (3 : ℝ) ^ q := by
  unfold Row.xHist; rw [hq]

theorem wHaar_eq {d : ℕ} (row : Row d) {q : ℝ} (hq : -(2 * (row.s : ℝ)) = q) :
    row.wHaar = (3 : ℝ) ^ q := by
  unfold Row.wHaar; rw [hq]

theorem log_xHist {d : ℕ} (row : Row d) {q : ℝ} (hq : -(2 * (row.s : ℝ)) + (d : ℝ) / 32 = q) :
    Real.log row.xHist = q * Real.log 3 := by
  rw [xHist_eq row hq, Real.log_rpow (by norm_num)]

/-! ### The source constants -/

theorem P32_le : P32 ≤ 24.942759 := by
  unfold P32
  have := root_le (n := 64) (a := 2 * (Nat.factorial 64 : ℝ)) (r := 24.942759) (by norm_num)
    (by positivity) (by norm_num) (by norm_num [Nat.factorial])
  simpa using this

theorem P32_nonneg : 0 ≤ P32 := by unfold P32; positivity

theorem varsigma_le : varsigma ≤ 1.01089 := by
  unfold varsigma
  have := root_le (n := 64) (a := (2 : ℝ)) (r := 1.01089) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  simpa using this

theorem varsigma_nonneg : 0 ≤ varsigma := by unfold varsigma; positivity

theorem Ch_nonneg : 0 ≤ Ch := by
  unfold Ch
  have : (0 : ℝ) ≤ (proxyA : ℝ) := by norm_num [proxyA]
  have := P32_nonneg
  have := varsigma_nonneg
  positivity

theorem Ch_le : Ch ≤ 0.540811 := by
  unfold Ch
  have h1 := P32_le
  have h2 := varsigma_le
  have h3 := P32_nonneg
  have h4 := varsigma_nonneg
  have ha : (proxyA : ℝ) = 1072331 / 100000000 := by norm_num [proxyA]
  rw [ha]
  calc 2 * (1072331 / 100000000 : ℝ) * P32 * varsigma
      ≤ 2 * (1072331 / 100000000 : ℝ) * 24.942759 * 1.01089 := by gcongr
    _ ≤ 0.540811 := by norm_num

theorem sqrt_Ch_le : √Ch ≤ 0.735399 := by
  refine Real.sqrt_le_iff.2 ⟨by norm_num, ?_⟩
  refine Ch_le.trans (by norm_num)

theorem kappaH_two : kappaH 2 = 0 := by simp [kappaH]

theorem kappaH_ne_two {d : ℕ} (hd : d ≠ 2) : kappaH d = (kappaQ1 : ℝ) := by simp [kappaH, hd]

theorem AF_two (δ : ℝ) : AF 2 δ = 0 := by simp [AF, kappaH_two]

theorem AG_two (δ : ℝ) : AG 2 δ = 0 := by simp [AG, kappaH_two]

theorem kappaQ1_pos : (0 : ℝ) < (kappaQ1 : ℝ) := by norm_num [kappaQ1]

theorem AF_nonneg {d : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) : 0 ≤ AF d δ := by
  have hk : 0 ≤ kappaH d := by
    unfold kappaH; split_ifs
    · exact le_rfl
    · exact kappaQ1_pos.le
  have := Real.sqrt_nonneg Ch
  unfold AF; positivity

theorem AG_nonneg {d : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) : 0 ≤ AG d δ := by
  have hk : 0 ≤ kappaH d := by
    unfold kappaH; split_ifs
    · exact le_rfl
    · exact kappaQ1_pos.le
  have := Real.sqrt_nonneg Ch
  have := varsigma_nonneg
  unfold AG; positivity

theorem AF_le {d : ℕ} (hd : d ≠ 2) {δ : ℝ} (hδ : 0 ≤ δ) :
    AF d δ ≤ 2 * (kappaQ1 : ℝ) * 0.735399 * δ ^ 3 + (kappaQ1 : ℝ) ^ 2 * δ ^ 4 := by
  rw [AF, kappaH_ne_two hd]
  have := sqrt_Ch_le
  have := kappaQ1_pos
  gcongr

theorem AG_le {d : ℕ} (hd : d ≠ 2) {δ : ℝ} (hδ : 0 ≤ δ) :
    AG d δ ≤ 2 * (kappaQ1 : ℝ) * 0.735399 * 1.01089 * δ ^ 3 +
      (kappaQ1 : ℝ) ^ 2 * 1.01089 ^ 2 * δ ^ 4 := by
  rw [AG, kappaH_ne_two hd]
  have := sqrt_Ch_le
  have := varsigma_le
  have := varsigma_nonneg
  have := kappaQ1_pos
  gcongr

/-! ### `F̄, Ḡ, C₁` -/

theorem bracket_le {w wl C Cu A Au z zu δ : ℝ} (hwl : wl ≤ w) (hw1 : w ≤ 1) (hz0 : 0 ≤ z)
    (hzz : z ≤ zu) (hz1 : zu < 1) (hC0 : 0 ≤ C) (hCC : C ≤ Cu) (hA0 : 0 ≤ A) (hAA : A ≤ Au) :
    (1 - w) * (C * δ ^ 2 * z / (1 - z) ^ 2 + A * z * (1 + z) / (1 - z) ^ 3) ≤
      (1 - wl) * (Cu * δ ^ 2 * zu / (1 - zu) ^ 2 + Au * zu * (1 + zu) / (1 - zu) ^ 3) := by
  have hzu0 : 0 ≤ zu := hz0.trans hzz
  have h1 : 0 < 1 - zu := by linarith
  have h2 : 0 < 1 - z := by linarith
  have h3 : 0 ≤ 1 - w := by linarith
  have hCu : 0 ≤ Cu := hC0.trans hCC
  have hAu : 0 ≤ Au := hA0.trans hAA
  have hz1' : 1 - zu ≤ 1 - z := by linarith
  have hin : C * δ ^ 2 * z / (1 - z) ^ 2 + A * z * (1 + z) / (1 - z) ^ 3 ≤
      Cu * δ ^ 2 * zu / (1 - zu) ^ 2 + Au * zu * (1 + zu) / (1 - zu) ^ 3 := by
    gcongr
  have hin0 : 0 ≤ C * δ ^ 2 * z / (1 - z) ^ 2 + A * z * (1 + z) / (1 - z) ^ 3 := by positivity
  have hin1 : 0 ≤ Cu * δ ^ 2 * zu / (1 - zu) ^ 2 + Au * zu * (1 + zu) / (1 - zu) ^ 3 := by
    positivity
  calc (1 - w) * (C * δ ^ 2 * z / (1 - z) ^ 2 + A * z * (1 + z) / (1 - z) ^ 3)
      ≤ (1 - w) * (Cu * δ ^ 2 * zu / (1 - zu) ^ 2 + Au * zu * (1 + zu) / (1 - zu) ^ 3) :=
        mul_le_mul_of_nonneg_left hin h3
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hin1

theorem bracket_nonneg {w C A z δ : ℝ} (hw1 : w ≤ 1) (hz0 : 0 ≤ z) (hz1 : z < 1) (hC0 : 0 ≤ C)
    (hA0 : 0 ≤ A) :
    0 ≤ (1 - w) * (C * δ ^ 2 * z / (1 - z) ^ 2 + A * z * (1 + z) / (1 - z) ^ 3) := by
  have h2 : 0 < 1 - z := by linarith
  have h3 : 0 ≤ 1 - w := by linarith
  positivity

theorem C1_le {d : ℕ} (row : Row d) {wl xu : ℝ} (hwl : wl ≤ row.wHaar) (hw1 : row.wHaar ≤ 1)
    (hx0 : 0 < row.xHist) (hxx : row.xHist ≤ xu) (hx1 : xu < 1) :
    row.C1 ≤ (1 - wl) / (1 - xu) * xu := by
  unfold Row.C1 Row.C0
  have h1 : 0 < 1 - xu := by linarith
  have h2 : 0 ≤ 1 - row.wHaar := by linarith
  have h3 : 1 - xu ≤ 1 - row.xHist := by linarith
  have h4 : 0 ≤ 1 - wl := by linarith
  gcongr

/-! ### `M₁, M₂` -/

theorem mul_exp_neg_le (z : ℝ) : z * Real.exp (-z) ≤ Real.exp (-1) := by
  have h : z ≤ Real.exp (z - 1) := by
    have := Real.add_one_le_exp (z - 1); linarith
  calc z * Real.exp (-z) ≤ Real.exp (z - 1) * Real.exp (-z) := by gcongr
    _ = Real.exp (-1) := by rw [← Real.exp_add]; ring_nf

theorem M1_le {d : ℕ} (row : Row d) (δ : ℝ) {bl s : ℝ} (hbl : 0 < bl) (hb : bl ≤ row.bg δ)
    (hs : 0 ≤ s) (hc0 : 0 ≤ row.cg) (hc : row.cg ^ 2 ≤ s ^ 2 * bl * 2.718)
    (hA : 0 ≤ row.Ag) : row.M1 δ ≤ (s + row.Ag) ^ 2 := by
  unfold Row.M1
  have hb0 : 0 < row.bg δ := lt_of_lt_of_le hbl hb
  refine ciSup_le fun t => ?_
  have ht : (1 : ℝ) ≤ t := t.2
  have ht0 : 0 < (t : ℝ) := by linarith
  set b := row.bg δ with hbdef
  set c := row.cg with hcdef
  set A := row.Ag with hAdef
  have hE : Real.exp (-(b * t)) = Real.exp (-(b * t / 2)) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hE1 : Real.exp (-(b * t / 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; have : 0 < b * t := by positivity
    linarith
  have hE0 : 0 < Real.exp (-(b * t / 2)) := Real.exp_pos _
  set E := Real.exp (-(b * t / 2)) with hEdef
  -- (c √t E)² ≤ s²
  have hsq : (c * √(t : ℝ) * E) ^ 2 ≤ s ^ 2 := by
    have e1 : (c * √(t : ℝ) * E) ^ 2 = c ^ 2 * ((t : ℝ) * Real.exp (-(b * t))) := by
      rw [hE, mul_pow, mul_pow, Real.sq_sqrt ht0.le]; ring
    have e2 : (t : ℝ) * Real.exp (-(b * t)) ≤ Real.exp (-1) / b := by
      rw [le_div_iff₀ hb0]
      have := mul_exp_neg_le (b * t)
      calc (t : ℝ) * Real.exp (-(b * t)) * b = b * t * Real.exp (-(b * t)) := by ring
        _ ≤ _ := this
    have e3 : Real.exp (-1) ≤ 1 / 2.718 := by
      rw [Real.exp_neg, ← one_div]
      have := Real.exp_one_gt_d9
      apply one_div_le_one_div_of_le (by norm_num)
      linarith
    rw [e1]
    calc c ^ 2 * ((t : ℝ) * Real.exp (-(b * t))) ≤ c ^ 2 * (Real.exp (-1) / b) := by gcongr
      _ ≤ c ^ 2 * ((1 / 2.718) / b) := by gcongr
      _ = c ^ 2 / (2.718 * b) := by field_simp
      _ ≤ (s ^ 2 * bl * 2.718) / (2.718 * b) := by gcongr
      _ = s ^ 2 * (bl / b) := by field_simp
      _ ≤ s ^ 2 * 1 := by
          gcongr
          rw [div_le_one hb0]; exact hb
      _ = s ^ 2 := mul_one _
  have hcs : c * √(t : ℝ) * E ≤ s :=
    (pow_le_pow_iff_left₀ (by positivity) hs (by norm_num : (2 : ℕ) ≠ 0)).1 hsq
  calc (c * √(t : ℝ) + A) ^ 2 * Real.exp (-(b * t))
      = (c * √(t : ℝ) * E + A * E) ^ 2 := by rw [hE]; ring
    _ ≤ (s + A) ^ 2 := by
        have : A * E ≤ A := by nlinarith
        have h0 : 0 ≤ c * √(t : ℝ) * E + A * E := by positivity
        exact pow_le_pow_left₀ h0 (by linarith) 2

theorem M2_le {d : ℕ} (row : Row d) (δ : ℝ) {bl m : ℝ} (hbl : 0 < bl) (hb : bl ≤ row.bg δ)
    (hm : 4 ≤ m * bl ^ 2 * 2.718 ^ 2) : row.M2 δ ≤ m := by
  unfold Row.M2
  have hb0 : 0 < row.bg δ := lt_of_lt_of_le hbl hb
  refine ciSup_le fun t => ?_
  have ht : (1 : ℝ) ≤ t := t.2
  have ht0 : 0 < (t : ℝ) := by linarith
  set b := row.bg δ with hbdef
  have hE : Real.exp (-(b * t)) = Real.exp (-(b * t / 2)) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hE0 : 0 < Real.exp (-(b * t / 2)) := Real.exp_pos _
  have h1 : (t : ℝ) * Real.exp (-(b * t / 2)) ≤ 2 / (b * 2.718) := by
    have := mul_exp_neg_le (b * t / 2)
    have e3 : Real.exp (-1) ≤ 1 / 2.718 := by
      rw [Real.exp_neg, ← one_div]
      have := Real.exp_one_gt_d9
      apply one_div_le_one_div_of_le (by norm_num)
      linarith
    rw [le_div_iff₀ (by positivity)]
    calc (t : ℝ) * Real.exp (-(b * t / 2)) * (b * 2.718)
        = (b * t / 2) * Real.exp (-(b * t / 2)) * 2 * 2.718 := by ring
      _ ≤ Real.exp (-1) * 2 * 2.718 := by gcongr
      _ ≤ (1 / 2.718) * 2 * 2.718 := by gcongr
      _ = 2 := by norm_num
  calc (t : ℝ) ^ 2 * Real.exp (-(b * t)) = ((t : ℝ) * Real.exp (-(b * t / 2))) ^ 2 := by
        rw [hE]; ring
    _ ≤ (2 / (b * 2.718)) ^ 2 := by gcongr
    _ = 4 / (b ^ 2 * 2.718 ^ 2) := by field_simp; norm_num
    _ ≤ 4 / (bl ^ 2 * 2.718 ^ 2) := by gcongr
    _ ≤ m := by
        rw [div_le_iff₀ (by positivity)]; nlinarith

theorem M1_nonneg {d : ℕ} (row : Row d) (δ : ℝ) : 0 ≤ row.M1 δ := by
  unfold Row.M1
  exact Real.iSup_nonneg fun t => by positivity

theorem M2_nonneg {d : ℕ} (row : Row d) (δ : ℝ) : 0 ≤ row.M2 δ := by
  unfold Row.M2
  exact Real.iSup_nonneg fun t => by positivity

/-! ### Enclosures used by the rows -/

theorem exp_lb' {c yl : ℝ} (hc : -1 ≤ c ∧ c ≤ 1)
    (h : yl ≤ GMCNumerics.expPoly c 14 - GMCNumerics.expErr c 14) : yl ≤ Real.exp c :=
  GMCNumerics.le_exp_of_poly (n := 14) (abs_le.2 hc) (by norm_num) h

theorem exp_ub' {c yu : ℝ} (hc : -1 ≤ c ∧ c ≤ 1)
    (h : GMCNumerics.expPoly c 14 + GMCNumerics.expErr c 14 ≤ yu) : Real.exp c ≤ yu :=
  GMCNumerics.exp_le_of_poly (n := 14) (abs_le.2 hc) (by norm_num) h

theorem three_rpow_neg_enclosure {q cl cu yl yu : ℝ} (hq : q ≤ 0)
    (hcl : cl ≤ q * 1.098612288668111) (hcu : q * 1.098612288668109 ≤ cu)
    (hyl : yl ≤ Real.exp cl) (hyu : Real.exp cu ≤ yu) :
    yl ≤ (3 : ℝ) ^ q ∧ (3 : ℝ) ^ q ≤ yu := by
  obtain ⟨l1, l2⟩ := GMCNumerics.log_three_enclosure
  have h1 := mul_le_mul_of_nonpos_left l1 hq
  have h2 := mul_le_mul_of_nonpos_left l2 hq
  exact ⟨le_three_rpow (by linarith) hyl, three_rpow_le (by linarith) hyu⟩

theorem zF_le {d : ℕ} (row : Row d) {δ c xu eu zu : ℝ}
    (hc : (128 * (proxyA : ℝ) + 2 * kappaH d) * δ ^ 2 = c) (hx0 : 0 < row.xHist)
    (hx : row.xHist ≤ xu) (he : Real.exp c ≤ eu) (hz : xu * eu ≤ zu) : row.zF δ ≤ zu := by
  unfold Row.zF
  rw [hc]
  calc row.xHist * Real.exp c ≤ xu * eu :=
        mul_le_mul hx he (Real.exp_pos c).le (hx0.le.trans hx)
    _ ≤ zu := hz

theorem zG_le {d : ℕ} (row : Row d) {δ c xu eu zu : ℝ}
    (hc : (32 * (proxyA : ℝ) + kappaH d) * δ ^ 2 = c) (hx0 : 0 < row.xHist)
    (hx : row.xHist ≤ xu) (he : Real.exp c ≤ eu) (hz : xu * eu ≤ zu) : row.zG δ ≤ zu := by
  unfold Row.zG
  rw [hc]
  calc row.xHist * Real.exp c ≤ xu * eu :=
        mul_le_mul hx he (Real.exp_pos c).le (hx0.le.trans hx)
    _ ≤ zu := hz

theorem zF_nonneg {d : ℕ} (row : Row d) (δ : ℝ) (hx0 : 0 < row.xHist) : 0 ≤ row.zF δ := by
  unfold Row.zF; positivity

theorem zG_nonneg {d : ℕ} (row : Row d) (δ : ℝ) (hx0 : 0 < row.xHist) : 0 ≤ row.zG δ := by
  unfold Row.zG; positivity

theorem zG_lt_zF {d : ℕ} (row : Row d) {δ : ℝ} (hx0 : 0 < row.xHist) (hδ : δ ≠ 0) :
    row.zG δ < row.zF δ := by
  unfold Row.zG Row.zF
  have hk : 0 ≤ kappaH d := by
    unfold kappaH; split_ifs
    · exact le_rfl
    · exact kappaQ1_pos.le
  have ha : (0 : ℝ) < (proxyA : ℝ) := by norm_num [proxyA]
  have hd : 0 < δ ^ 2 := by positivity
  have : (32 * (proxyA : ℝ) + kappaH d) * δ ^ 2 < (128 * (proxyA : ℝ) + 2 * kappaH d) * δ ^ 2 :=
    mul_lt_mul_of_pos_right (by linarith) hd
  exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.2 this) hx0

theorem bg_ge {d : ℕ} (row : Row d) {δ q c bl : ℝ}
    (hq : -(2 * (row.s : ℝ)) + (d : ℝ) / 32 = q) (hq0 : q ≤ 0)
    (hc : (64 * (proxyA : ℝ) + kappaH d) * δ ^ 2 = c)
    (hb : bl ≤ -q * 1.098612288668109 - c) : bl ≤ row.bg δ := by
  unfold Row.bg
  rw [log_xHist row hq, hc]
  obtain ⟨l1, -⟩ := GMCNumerics.log_three_enclosure
  have h1 := mul_le_mul_of_nonpos_left l1 hq0
  linarith

theorem hbar_nonneg {d : ℕ} (row : Row d) : 0 ≤ row.hbar := by
  unfold Row.hbar; positivity

theorem hbar_le {d : ℕ} (row : Row d) {hu : ℝ} (hu0 : 0 ≤ hu)
    (h : (row.gridCount : ℝ) ≤ hu ^ 128) : row.hbar ≤ hu := by
  unfold Row.hbar
  have := root_le (n := 128) (by norm_num) (Nat.cast_nonneg _) hu0 h
  simpa using this

theorem sphereFactor_le (d : ℕ) {bu : ℝ} (hu0 : 0 ≤ bu) (h : (sphereFactorPow d : ℝ) ≤ bu ^ 32) :
    sphereFactor d ≤ bu := by
  unfold sphereFactor
  have hn : (0 : ℝ) ≤ (sphereFactorPow d : ℝ) := by
    unfold sphereFactorPow; split_ifs <;> positivity
  have := root_le (n := 32) (by norm_num) hn hu0 h
  simpa using this

theorem cg_nonneg {d : ℕ} (row : Row d) : 0 ≤ row.cg := by
  have := hbar_nonneg row
  unfold Row.cg; positivity

theorem Ag_nonneg {d : ℕ} (row : Row d) : 0 ≤ row.Ag := by
  unfold Row.Ag; positivity

theorem cg_sq_le {d : ℕ} (row : Row d) {hu : ℝ} (hh : row.hbar ≤ hu) :
    row.cg ^ 2 ≤ hu ^ 2 * (2 * (proxyA : ℝ)) := by
  have h0 := hbar_nonneg row
  have ha : (0 : ℝ) ≤ 2 * (proxyA : ℝ) := by norm_num [proxyA]
  unfold Row.cg
  rw [mul_pow, Real.sq_sqrt ha]
  gcongr

end GMCExplicitDelta.Certificates
