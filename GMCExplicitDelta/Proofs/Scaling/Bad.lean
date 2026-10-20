module

public import GMCExplicitDelta.Proofs.Scaling.BadPre

/-!
# R4(b)–(d): the bad charge at smaller disorder

Proof of `badCharge_scale_le`. The statement needs `0 ≤ ε_sub` (the contract's `Obligations` does
not record the sign of `ε_sub`).
-/

@[expose] public section

open Real

namespace GMCExplicitDelta.Assembly

open Contract

variable {d : ℕ}

/-! ### History terms -/

theorem histTerm_le {Ch α β δ δ' l z z' : ℝ} (hCh : 0 ≤ Ch) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hδ0 : 0 ≤ δ) (hδδ : δ ≤ δ') (hsq : δ ^ 2 = l * δ' ^ 2)
    (hz0 : 0 ≤ z) (hzz : z ≤ z') (hz' : z' < 1) :
    Ch * δ ^ 2 * z / (1 - z) ^ 2 + (α * δ ^ 3 + β * δ ^ 4) * z * (1 + z) / (1 - z) ^ 3 ≤
      l * (Ch * δ' ^ 2 * z' / (1 - z') ^ 2 +
        (α * δ' ^ 3 + β * δ' ^ 4) * z' * (1 + z') / (1 - z') ^ 3) := by
  have hz1 : 0 < 1 - z' := by linarith
  have hz'0 : 0 ≤ z' := hz0.trans hzz
  have hδ'0 : 0 ≤ δ' := hδ0.trans hδδ
  have h3 : δ ^ 3 ≤ l * δ' ^ 3 := by
    have : δ ^ 3 = δ * δ ^ 2 := by ring
    rw [this, hsq]
    have := mul_le_mul_of_nonneg_right hδδ (mul_nonneg hl0 (sq_nonneg δ'))
    nlinarith
  have h4 : δ ^ 4 ≤ l * δ' ^ 4 := by
    have : δ ^ 4 = (δ ^ 2) ^ 2 := by ring
    rw [this, hsq]
    have h : l * δ' ^ 4 - (l * δ' ^ 2) ^ 2 = l * (1 - l) * δ' ^ 4 := by ring
    nlinarith [mul_nonneg (mul_nonneg hl0 (sub_nonneg.2 hl1)) (by positivity : 0 ≤ δ' ^ 4)]
  have hαβ : α * δ ^ 3 + β * δ ^ 4 ≤ l * (α * δ' ^ 3 + β * δ' ^ 4) := by
    nlinarith [mul_le_mul_of_nonneg_left h3 hα, mul_le_mul_of_nonneg_left h4 hβ]
  have hs0 : 0 ≤ α * δ ^ 3 + β * δ ^ 4 := by positivity
  have hs0' : 0 ≤ α * δ' ^ 3 + β * δ' ^ 4 := by positivity
  have hzp : (1 - z') ^ 2 ≤ (1 - z) ^ 2 := by nlinarith
  have hzp3 : (1 - z') ^ 3 ≤ (1 - z) ^ 3 := pow_le_pow_left₀ hz1.le (by linarith) 3
  have t1 : Ch * δ ^ 2 * z / (1 - z) ^ 2 ≤ l * Ch * δ' ^ 2 * z' / (1 - z') ^ 2 := by
    apply div_le_div₀ (by positivity) _ (by positivity) hzp
    rw [hsq]
    have : 0 ≤ Ch * (l * δ' ^ 2) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hzz this]
  have t2 : (α * δ ^ 3 + β * δ ^ 4) * z * (1 + z) / (1 - z) ^ 3 ≤
      l * (α * δ' ^ 3 + β * δ' ^ 4) * z' * (1 + z') / (1 - z') ^ 3 := by
    apply div_le_div₀ (by positivity) _ (by positivity) hzp3
    have h5 : z * (1 + z) ≤ z' * (1 + z') := by nlinarith
    have h6 : 0 ≤ z * (1 + z) := by positivity
    have h7 : 0 ≤ l * (α * δ' ^ 3 + β * δ' ^ 4) := by positivity
    calc (α * δ ^ 3 + β * δ ^ 4) * z * (1 + z) = (α * δ ^ 3 + β * δ ^ 4) * (z * (1 + z)) := by ring
      _ ≤ l * (α * δ' ^ 3 + β * δ' ^ 4) * (z * (1 + z)) :=
          mul_le_mul_of_nonneg_right hαβ h6
      _ ≤ l * (α * δ' ^ 3 + β * δ' ^ 4) * (z' * (1 + z')) :=
          mul_le_mul_of_nonneg_left h5 h7
      _ = _ := by ring
  calc _ ≤ l * Ch * δ' ^ 2 * z' / (1 - z') ^ 2 +
        l * (α * δ' ^ 3 + β * δ' ^ 4) * z' * (1 + z') / (1 - z') ^ 3 := add_le_add t1 t2
    _ = _ := by ring

theorem histTerm_nonneg {Ch α β δ z : ℝ} (hCh : 0 ≤ Ch) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hδ0 : 0 ≤ δ) (hz0 : 0 ≤ z) (hz : z < 1) :
    0 ≤ Ch * δ ^ 2 * z / (1 - z) ^ 2 + (α * δ ^ 3 + β * δ ^ 4) * z * (1 + z) / (1 - z) ^ 3 := by
  have : 0 < 1 - z := by linarith
  positivity

section Row

variable (row : Row d)

theorem wHaar_nonneg : 0 ≤ row.wHaar := by unfold Row.wHaar; positivity

theorem wHaar_le_one (hO : row.Obligations) : row.wHaar ≤ 1 := by
  unfold Row.wHaar
  have hs : (0 : ℝ) < (row.s : ℝ) := by exact_mod_cast hO.par1.2.2.2.2.2.1
  exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)

theorem xHist_pos : 0 < row.xHist := by unfold Row.xHist; positivity

theorem zF_nonneg (δ : ℝ) : 0 ≤ row.zF δ := by
  unfold Row.zF; have := xHist_pos row; positivity

theorem zG_nonneg (δ : ℝ) : 0 ≤ row.zG δ := by
  unfold Row.zG; have := xHist_pos row; positivity

theorem zG_le_of_le {δ δ' : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ δ') : row.zG δ ≤ row.zG δ' := by
  unfold Row.zG
  have hx := xHist_pos row
  have hc : 0 ≤ 32 * (proxyA : ℝ) + kappaH d := by
    have := proxyA_pos; have := kappaH_nonneg d; positivity
  have hsq : δ ^ 2 ≤ δ' ^ 2 := pow_le_pow_left₀ hδ0.le hδ 2
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsq hc)) hx.le

theorem Ch_nonneg : 0 ≤ Ch := by
  unfold Ch P32 varsigma
  have := proxyA_pos
  positivity

theorem Fbar_le (hO : row.Obligations) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ (row.deltaStar : ℝ)) :
    row.Fbar δ ≤ lamOf row δ * row.Fbar row.deltaStar := by
  have hl := lamOf_pos row hδ0 hδ
  have hl1 := lamOf_le_one row hδ0 hδ
  have hw := wHaar_le_one row hO
  have hk := kappaH_nonneg d
  have h := histTerm_le (Ch := Ch) (α := 2 * kappaH d * √Ch) (β := kappaH d ^ 2)
    (δ := δ) (δ' := (row.deltaStar : ℝ)) (l := lamOf row δ) (z := row.zF δ)
    (z' := row.zF row.deltaStar) Ch_nonneg (by have := Real.sqrt_nonneg Ch; positivity)
    (by positivity) hl.le hl1 hδ0.le hδ (delta_sq row hδ0 hδ) (zF_nonneg row _)
    (zF_le_of_le row hδ0 hδ) hO.hist1.2
  unfold Row.Fbar AF
  calc (1 - row.wHaar) * _ ≤ (1 - row.wHaar) * (lamOf row δ * _) :=
        mul_le_mul_of_nonneg_left h (by linarith)
    _ = _ := by ring

theorem Gbar_le (hO : row.Obligations) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ (row.deltaStar : ℝ)) :
    row.Gbar δ ≤ lamOf row δ * row.Gbar row.deltaStar := by
  have hl := lamOf_pos row hδ0 hδ
  have hl1 := lamOf_le_one row hδ0 hδ
  have hw := wHaar_le_one row hO
  have hk := kappaH_nonneg d
  have hzG : row.zG row.deltaStar < 1 := hO.hist1.1.trans hO.hist1.2
  have hς : 0 ≤ varsigma := by unfold varsigma; positivity
  have h := histTerm_le (Ch := Ch) (α := 2 * kappaH d * √Ch * varsigma)
    (β := kappaH d ^ 2 * varsigma ^ 2)
    (δ := δ) (δ' := (row.deltaStar : ℝ)) (l := lamOf row δ) (z := row.zG δ)
    (z' := row.zG row.deltaStar) Ch_nonneg (by have := Real.sqrt_nonneg Ch; positivity)
    (by positivity) hl.le hl1 hδ0.le hδ (delta_sq row hδ0 hδ) (zG_nonneg row _)
    (zG_le_of_le row hδ0 hδ) hzG
  unfold Row.Gbar AG
  calc (1 - row.wHaar) * _ ≤ (1 - row.wHaar) * (lamOf row δ * _) :=
        mul_le_mul_of_nonneg_left h (by linarith)
    _ = _ := by ring

theorem Fbar_nonneg (hO : row.Obligations) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ (row.deltaStar : ℝ)) :
    0 ≤ row.Fbar δ := by
  have hw := wHaar_le_one row hO
  have hk := kappaH_nonneg d
  have h := histTerm_nonneg (Ch := Ch) (α := 2 * kappaH d * √Ch) (β := kappaH d ^ 2)
    (δ := δ) (z := row.zF δ) Ch_nonneg (by have := Real.sqrt_nonneg Ch; positivity)
    (by positivity) hδ0.le (zF_nonneg row _)
    ((zF_le_of_le row hδ0 hδ).trans_lt hO.hist1.2)
  unfold Row.Fbar AF
  exact mul_nonneg (by linarith) h

theorem Gbar_nonneg (hO : row.Obligations) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ (row.deltaStar : ℝ)) :
    0 ≤ row.Gbar δ := by
  have hw := wHaar_le_one row hO
  have hk := kappaH_nonneg d
  have hς : 0 ≤ varsigma := by unfold varsigma; positivity
  have hzG : row.zG row.deltaStar < 1 := hO.hist1.1.trans hO.hist1.2
  have h := histTerm_nonneg (Ch := Ch) (α := 2 * kappaH d * √Ch * varsigma)
    (β := kappaH d ^ 2 * varsigma ^ 2)
    (δ := δ) (z := row.zG δ) Ch_nonneg (by have := Real.sqrt_nonneg Ch; positivity)
    (by positivity) hδ0.le (zG_nonneg row _)
    ((zG_le_of_le row hδ0 hδ).trans_lt hzG)
  unfold Row.Gbar AG
  exact mul_nonneg (by linarith) h

theorem delta4_le {δ δ' l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hsq : δ ^ 2 = l * δ' ^ 2) :
    δ ^ 4 ≤ l * δ' ^ 4 := by
  have : δ ^ 4 = (δ ^ 2) ^ 2 := by ring
  rw [this, hsq]
  nlinarith [mul_nonneg (mul_nonneg hl0 (sub_nonneg.2 hl1)) (by positivity : 0 ≤ δ' ^ 4)]

theorem bg_ge {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ (row.deltaStar : ℝ)) :
    row.bg row.deltaStar ≤ row.bg δ := by
  unfold Row.bg
  have hc : 0 ≤ 64 * (proxyA : ℝ) + kappaH d := by
    have := proxyA_pos; have := kappaH_nonneg d; positivity
  have hsq : δ ^ 2 ≤ (row.deltaStar : ℝ) ^ 2 := pow_le_pow_left₀ hδ0.le hδ 2
  nlinarith [mul_le_mul_of_nonneg_left hsq hc]

theorem cg_nonneg : 0 ≤ row.cg := by unfold Row.cg Row.hbar; positivity

theorem Ag_nonneg : 0 ≤ row.Ag := by unfold Row.Ag; positivity

theorem M1_nonneg (δ : ℝ) : 0 ≤ row.M1 δ := by
  unfold Row.M1
  exact Real.iSup_nonneg fun t => by positivity

theorem M2_nonneg (δ : ℝ) : 0 ≤ row.M2 δ := by
  unfold Row.M2
  exact Real.iSup_nonneg fun t => by positivity

theorem M1_le (hO : row.Obligations) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ (row.deltaStar : ℝ)) :
    row.M1 δ ≤ row.M1 row.deltaStar := by
  unfold Row.M1
  haveI : Nonempty (Set.Ici (1 : ℝ)) := ⟨⟨1, le_rfl⟩⟩
  have hb : 0 < row.bg row.deltaStar := hO.hist2
  have hbdd : BddAbove (Set.range fun t : Set.Ici (1 : ℝ) =>
      (row.cg * √(t : ℝ) + row.Ag) ^ 2 * Real.exp (-(row.bg row.deltaStar * t))) :=
    ⟨2 * row.cg ^ 2 / row.bg row.deltaStar + 2 * row.Ag ^ 2, by
      rintro _ ⟨t, rfl⟩
      exact M1_term_bdd hb (cg_nonneg row) (Ag_nonneg row) t t.2⟩
  refine ciSup_le fun t => le_trans ?_ (le_ciSup hbdd t)
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply Real.exp_le_exp.mpr
  have := mul_le_mul_of_nonneg_right (bg_ge row hδ0 hδ) (by have ht : (1 : ℝ) ≤ (t : ℝ) := t.2; linarith)
  linarith

theorem M2_le (hO : row.Obligations) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ (row.deltaStar : ℝ)) :
    row.M2 δ ≤ row.M2 row.deltaStar := by
  unfold Row.M2
  haveI : Nonempty (Set.Ici (1 : ℝ)) := ⟨⟨1, le_rfl⟩⟩
  have hb : 0 < row.bg row.deltaStar := hO.hist2
  have hbdd : BddAbove (Set.range fun t : Set.Ici (1 : ℝ) =>
      (t : ℝ) ^ 2 * Real.exp (-(row.bg row.deltaStar * t))) :=
    ⟨2 / row.bg row.deltaStar ^ 2, by
      rintro _ ⟨t, rfl⟩
      exact M2_term_bdd hb t t.2⟩
  refine ciSup_le fun t => le_trans ?_ (le_ciSup hbdd t)
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply Real.exp_le_exp.mpr
  have := mul_le_mul_of_nonneg_right (bg_ge row hδ0 hδ) (by have ht : (1 : ℝ) ≤ (t : ℝ) := t.2; linarith)
  linarith

/-- The bracket of `U_grid`. -/
theorem Ugrid_bracket (hO : row.Obligations) (hε : 0 ≤ (row.epsSub : ℝ)) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ ≤ (row.deltaStar : ℝ)) :
    0 ≤ (if d = 2 then P32 * δ ^ 2 * row.M1 δ
      else (1 + (row.epsSub : ℝ)) * P32 * δ ^ 2 * row.M1 δ +
        (1 + (row.epsSub : ℝ)⁻¹) * kappaH d ^ 2 * δ ^ 4 * row.M2 δ) := by
  have h1 := M1_nonneg row δ
  have h2 := M2_nonneg row δ
  have hP : 0 ≤ P32 := by unfold P32; positivity
  have hi : 0 ≤ (row.epsSub : ℝ)⁻¹ := inv_nonneg.mpr hε
  split_ifs
  · positivity
  · positivity

theorem Ugrid_bracket_le (hO : row.Obligations) (hε : 0 ≤ (row.epsSub : ℝ)) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ : δ ≤ (row.deltaStar : ℝ)) :
    (if d = 2 then P32 * δ ^ 2 * row.M1 δ
      else (1 + (row.epsSub : ℝ)) * P32 * δ ^ 2 * row.M1 δ +
        (1 + (row.epsSub : ℝ)⁻¹) * kappaH d ^ 2 * δ ^ 4 * row.M2 δ) ≤
    lamOf row δ * (if d = 2 then P32 * (row.deltaStar : ℝ) ^ 2 * row.M1 row.deltaStar
      else (1 + (row.epsSub : ℝ)) * P32 * (row.deltaStar : ℝ) ^ 2 * row.M1 row.deltaStar +
        (1 + (row.epsSub : ℝ)⁻¹) * kappaH d ^ 2 * (row.deltaStar : ℝ) ^ 4 * row.M2 row.deltaStar) := by
  have hl := lamOf_pos row hδ0 hδ
  have hl1 := lamOf_le_one row hδ0 hδ
  have hsq := delta_sq row hδ0 hδ
  have h1 := M1_nonneg row δ
  have h2 := M2_nonneg row δ
  have m1 := M1_le row hO hδ0 hδ
  have m2 := M2_le row hO hδ0 hδ
  have hP : 0 ≤ P32 := by unfold P32; positivity
  have hi : 0 ≤ (row.epsSub : ℝ)⁻¹ := inv_nonneg.mpr hε
  have h4 := delta4_le hl.le hl1 hsq
  have hP1 : 0 ≤ P32 * δ ^ 2 := by positivity
  split_ifs
  · rw [hsq]
    calc P32 * (lamOf row δ * (row.deltaStar : ℝ) ^ 2) * row.M1 δ
        ≤ P32 * (lamOf row δ * (row.deltaStar : ℝ) ^ 2) * row.M1 row.deltaStar :=
          mul_le_mul_of_nonneg_left m1 (by positivity)
      _ = _ := by ring
  · have a1 : (1 + (row.epsSub : ℝ)) * P32 * δ ^ 2 * row.M1 δ ≤
        lamOf row δ * ((1 + (row.epsSub : ℝ)) * P32 * (row.deltaStar : ℝ) ^ 2 *
          row.M1 row.deltaStar) := by
      rw [hsq]
      calc (1 + (row.epsSub : ℝ)) * P32 * (lamOf row δ * (row.deltaStar : ℝ) ^ 2) * row.M1 δ
          ≤ (1 + (row.epsSub : ℝ)) * P32 * (lamOf row δ * (row.deltaStar : ℝ) ^ 2) *
              row.M1 row.deltaStar :=
            mul_le_mul_of_nonneg_left m1 (by positivity)
        _ = _ := by ring
    have a2 : (1 + (row.epsSub : ℝ)⁻¹) * kappaH d ^ 2 * δ ^ 4 * row.M2 δ ≤
        lamOf row δ * ((1 + (row.epsSub : ℝ)⁻¹) * kappaH d ^ 2 * (row.deltaStar : ℝ) ^ 4 *
          row.M2 row.deltaStar) := by
      have hc : 0 ≤ (1 + (row.epsSub : ℝ)⁻¹) * kappaH d ^ 2 := by positivity
      calc (1 + (row.epsSub : ℝ)⁻¹) * kappaH d ^ 2 * δ ^ 4 * row.M2 δ
          = ((1 + (row.epsSub : ℝ)⁻¹) * kappaH d ^ 2) * (δ ^ 4 * row.M2 δ) := by ring
        _ ≤ ((1 + (row.epsSub : ℝ)⁻¹) * kappaH d ^ 2) *
            ((lamOf row δ * (row.deltaStar : ℝ) ^ 4) * row.M2 row.deltaStar) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul h4 m2 h2 (by positivity)) hc
        _ = _ := by ring
    nlinarith

theorem Ugrid_le (hO : row.Obligations) (hε : 0 ≤ (row.epsSub : ℝ)) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ ≤ (row.deltaStar : ℝ)) :
    row.Ugrid δ ≤ lamOf row δ * row.Ugrid row.deltaStar := by
  have hl := lamOf_pos row hδ0 hδ
  have hb := Ugrid_bracket_le row hO hε hδ0 hδ
  have hb0 := Ugrid_bracket row hO hε hδ0 hδ
  have hb0' := Ugrid_bracket row hO hε (hδ0.trans_le hδ) le_rfl
  have hx := xHist_pos row
  have hw := wHaar_nonneg row
  have hPre : 0 ≤ row.wHaar * varsigma * row.hbar / (2 * row.xHist) := by
    unfold Row.hbar varsigma; positivity
  have hE : Real.exp (32 * row.Ag ^ 2 * δ ^ 2) ≤
      Real.exp (32 * row.Ag ^ 2 * (row.deltaStar : ℝ) ^ 2) := by
    apply Real.exp_le_exp.mpr
    have : δ ^ 2 ≤ (row.deltaStar : ℝ) ^ 2 := pow_le_pow_left₀ hδ0.le hδ 2
    nlinarith [sq_nonneg row.Ag]
  unfold Row.Ugrid
  calc row.wHaar * varsigma * row.hbar / (2 * row.xHist) * Real.exp (32 * row.Ag ^ 2 * δ ^ 2) * _
      ≤ row.wHaar * varsigma * row.hbar / (2 * row.xHist) * Real.exp (32 * row.Ag ^ 2 * δ ^ 2) *
        (lamOf row δ * _) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ row.wHaar * varsigma * row.hbar / (2 * row.xHist) *
          Real.exp (32 * row.Ag ^ 2 * (row.deltaStar : ℝ) ^ 2) * (lamOf row δ * _) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE hPre)
          (mul_nonneg hl.le hb0')
    _ = _ := by ring

theorem Ugrid_nonneg (hO : row.Obligations) (hε : 0 ≤ (row.epsSub : ℝ)) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ ≤ (row.deltaStar : ℝ)) : 0 ≤ row.Ugrid δ := by
  have hb0 := Ugrid_bracket row hO hε hδ0 hδ
  have hx := xHist_pos row
  have hw := wHaar_nonneg row
  unfold Row.Ugrid Row.hbar varsigma
  positivity

theorem xHist_lt_one (hO : row.Obligations) : row.xHist < 1 := by
  have h := hO.hist1.2
  have hx := xHist_pos row
  have : row.xHist ≤ row.zF row.deltaStar := by
    unfold Row.zF
    have hc : 0 ≤ (128 * (proxyA : ℝ) + 2 * kappaH d) * (row.deltaStar : ℝ) ^ 2 := by
      have := proxyA_pos; have := kappaH_nonneg d; positivity
    have := Real.one_le_exp hc
    nlinarith
  linarith

theorem C1_nonneg (hO : row.Obligations) : 0 ≤ row.C1 := by
  have hx := xHist_pos row
  have hx1 := xHist_lt_one row hO
  have hw := wHaar_le_one row hO
  unfold Row.C1 Row.C0
  have : 0 < 1 - row.xHist := by linarith
  have : 0 ≤ 1 - row.wHaar := by linarith
  positivity

theorem sphereFactor_nonneg (d : ℕ) : 0 ≤ sphereFactor d := by
  unfold sphereFactor
  exact Real.rpow_nonneg (sphereFactorPow_nonneg d) _

theorem Hhist_le (hO : row.Obligations) (hε : 0 ≤ (row.epsSub : ℝ)) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ ≤ (row.deltaStar : ℝ)) :
    row.Hhist δ (lamOf row δ * row.D) ≤ lamOf row δ * row.Hhist row.deltaStar row.D := by
  have hl := lamOf_pos row hδ0 hδ
  have hl1 := lamOf_le_one row hδ0 hδ
  have hD : (0 : ℝ) ≤ row.D := by exact_mod_cast hO.par1.1.le
  have hη : (0 : ℝ) < row.eta := by exact_mod_cast hO.par3.1
  have hF1 := Fbar_le row hO hδ0 hδ
  have hG1 := Gbar_le row hO hδ0 hδ
  have hF0 := Fbar_nonneg row hO hδ0 hδ
  have hG0 := Gbar_nonneg row hO hδ0 hδ
  have hU := Ugrid_le row hO hε hδ0 hδ
  have hX : row.Fbar δ / (2 * (row.eta : ℝ)) + row.Gbar δ ≤
      lamOf row δ * (row.Fbar row.deltaStar / (2 * (row.eta : ℝ)) + row.Gbar row.deltaStar) := by
    have : row.Fbar δ / (2 * (row.eta : ℝ)) ≤
        lamOf row δ * row.Fbar row.deltaStar / (2 * (row.eta : ℝ)) :=
      div_le_div_of_nonneg_right hF1 (by positivity)
    rw [mul_add, mul_div_assoc] at *
    linarith
  have hX0 : 0 ≤ row.Fbar δ / (2 * (row.eta : ℝ)) + row.Gbar δ := by positivity
  have hβ := sphereFactor_nonneg d
  unfold Row.Hhist
  have h1 : (1 + (row.eta : ℝ)) * row.C1 * (lamOf row δ * row.D) =
      lamOf row δ * ((1 + (row.eta : ℝ)) * row.C1 * row.D) := by ring
  have h2 : sphereFactor d * (1 + lamOf row δ * row.D) *
        (row.Fbar δ / (2 * (row.eta : ℝ)) + row.Gbar δ) ≤
      lamOf row δ * (sphereFactor d * (1 + row.D) *
        (row.Fbar row.deltaStar / (2 * (row.eta : ℝ)) + row.Gbar row.deltaStar)) := by
    have hlD : lamOf row δ * row.D ≤ row.D := by nlinarith
    calc sphereFactor d * (1 + lamOf row δ * row.D) *
          (row.Fbar δ / (2 * (row.eta : ℝ)) + row.Gbar δ)
        ≤ sphereFactor d * (1 + row.D) * (row.Fbar δ / (2 * (row.eta : ℝ)) + row.Gbar δ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (by linarith) hβ) hX0
      _ ≤ sphereFactor d * (1 + row.D) * (lamOf row δ *
          (row.Fbar row.deltaStar / (2 * (row.eta : ℝ)) + row.Gbar row.deltaStar)) :=
          mul_le_mul_of_nonneg_left hX (by positivity)
      _ = _ := by ring
  rw [h1]
  linarith

theorem Hhist_nonneg (hO : row.Obligations) (hε : 0 ≤ (row.epsSub : ℝ)) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ ≤ (row.deltaStar : ℝ)) {D : ℝ} (hD : 0 ≤ D) : 0 ≤ row.Hhist δ D := by
  have hη : (0 : ℝ) < row.eta := by exact_mod_cast hO.par3.1
  have hF0 := Fbar_nonneg row hO hδ0 hδ
  have hG0 := Gbar_nonneg row hO hδ0 hδ
  have hU := Ugrid_nonneg row hO hε hδ0 hδ
  have hC := C1_nonneg row hO
  have hβ := sphereFactor_nonneg d
  unfold Row.Hhist
  positivity

theorem Sinf_nonneg (D F : ℝ) : 0 ≤ row.Sinf D F := by
  unfold Row.Sinf
  refine tsum_nonneg fun ℓ => mul_nonneg ?_ (by have := xHist_pos row; positivity)
  unfold frakU
  split_ifs
  · exact zero_le_one
  · refine le_min zero_le_one ?_
    have : 0 ≤ Bbar32 (3 ^ (d * (ℓ - 1))) D F := rpow_one_div_32_nonneg _
    have := sigmaNorm_nonneg d
    positivity

theorem eStar_nonneg (hO : row.Obligations) (hε : 0 ≤ (row.epsSub : ℝ)) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ ≤ (row.deltaStar : ℝ)) {D : ℝ} (hD : 0 ≤ D) (F : ℝ) :
    0 ≤ row.eStar δ D F := by
  have hw := wHaar_le_one row hO
  have hx := xHist_pos row
  have h1 := Sinf_nonneg row D F
  have h2 := Hhist_nonneg row hO hε hδ0 hδ hD
  unfold Row.eStar
  have : 0 ≤ 1 - row.wHaar := by linarith
  positivity

theorem eStar_le (hO : row.Obligations) (hε : 0 ≤ (row.epsSub : ℝ)) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ ≤ (row.deltaStar : ℝ)) :
    row.eStar δ (lamOf row δ * row.D) (lamOf row δ * row.F) ≤
      lamOf row δ * row.eStar row.deltaStar row.D row.F := by
  have hl := lamOf_pos row hδ0 hδ
  have hx := xHist_pos row
  have hH := Hhist_le row hO hε hδ0 hδ
  unfold Row.eStar
  have hS : row.Sinf (lamOf row δ * row.D) (lamOf row δ * row.F) = row.Sinf row.D row.F := by
    unfold Row.Sinf
    simp only [frakU_smul hl]
  rw [hS]
  have : 0 ≤ row.xHist ^ row.g := by positivity
  have := mul_le_mul_of_nonneg_left hH this
  nlinarith

end Row

/-- **R4(b)–(d) (bad charge at smaller disorder).** Statement of the target. -/
theorem badCharge_scale_le_proof (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ))
    (hO : row.Obligations) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ ≤ (row.deltaStar : ℝ)) :
    row.badCharge δ (lamOf row δ * row.D) (lamOf row δ * row.F) ≤
      row.badCharge row.deltaStar row.D row.F := by
  have hε : 0 ≤ (row.epsSub : ℝ) := by exact_mod_cast hO.par4.le
  have hl := lamOf_pos row hδ0 hδ
  have hl1 := lamOf_le_one row hδ0 hδ
  have hD : (0 : ℝ) < row.D := by exact_mod_cast hO.par1.1
  have hF : (0 : ℝ) < row.F := by exact_mod_cast hO.par1.2.1
  have hθ := hO.bad1
  have hlF : lamOf row δ * row.F ≤ row.F := by nlinarith
  have hlF0 : 0 < lamOf row δ * row.F := by positivity
  have hU0 : 0 ≤ nativeCap d (row.g - row.nu) row.D row.F := nativeCap_nonneg d _ hD.le hF.le
  have hUs : nativeCap d (row.g - row.nu) (lamOf row δ * row.D) (lamOf row δ * row.F) =
      (nativeCap d (row.g - row.nu) row.D row.F / row.F) * (lamOf row δ * row.F) := by
    rw [nativeCap_smul hl]; field_simp
  -- the prefactors
  have hpre : PhiMap (Real.log (1 + 2 * (lamOf row δ * row.F)))
        (nativeCap d (row.g - row.nu) (lamOf row δ * row.D) (lamOf row δ * row.F)) /
        (lamOf row δ * row.F) ≤
      PhiMap (Real.log (1 + 2 * row.F)) (nativeCap d (row.g - row.nu) row.D row.F) / row.F := by
    rw [hUs]
    have := prefactor_mono (a := nativeCap d (row.g - row.nu) row.D row.F / row.F)
      (by positivity) hlF0 hlF
    rwa [div_mul_cancel₀ _ hF.ne'] at this
  have hpre0 : 0 ≤ PhiMap (Real.log (1 + 2 * (lamOf row δ * row.F)))
        (nativeCap d (row.g - row.nu) (lamOf row δ * row.D) (lamOf row δ * row.F)) /
        (lamOf row δ * row.F) := by
    refine div_nonneg (Coarse.phi_nonneg (nativeCap_nonneg d _ (by positivity) hlF0.le) ?_)
      hlF0.le
    exact Real.log_nonneg (by linarith)
  have hpre1 := hpre0.trans hpre
  -- the excess
  have he0 := eStar_nonneg row hO hε hδ0 hδ (D := lamOf row δ * row.D) (by positivity)
    (lamOf row δ * row.F)
  have he1 := eStar_le row hO hε hδ0 hδ
  have he0' := eStar_nonneg row hO hε (hδ0.trans_le hδ) le_rfl (D := row.D) hD.le row.F
  have hθ0 : 0 < row.thetaR - row.F := by linarith
  have hq : row.eStar δ (lamOf row δ * row.D) (lamOf row δ * row.F) /
        (row.thetaR - lamOf row δ * row.F) ≤
      row.eStar row.deltaStar row.D row.F / (row.thetaR - row.F) := by
    apply div_le_div₀ he0' _ hθ0 (by linarith)
    have : lamOf row δ * row.eStar row.deltaStar row.D row.F ≤ row.eStar row.deltaStar row.D row.F :=
      by nlinarith
    linarith
  have hq0 : 0 ≤ row.eStar δ (lamOf row δ * row.D) (lamOf row δ * row.F) /
        (row.thetaR - lamOf row δ * row.F) :=
    div_nonneg he0 (by linarith)
  unfold Row.badCharge
  exact mul_le_mul hpre (pow_le_pow_left₀ hq0 hq 31) (pow_nonneg hq0 _) hpre1

end GMCExplicitDelta.Assembly
