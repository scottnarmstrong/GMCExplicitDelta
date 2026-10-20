module

public import GMCExplicitDelta.Proofs.Scaling.T4
public import GMCExplicitDelta.Assembly.Scaling

/-!
# R4(e)–(f): the barrier at smaller disorder

Proof of `barrier_scale_pos`: `d ≥ 3` by monotonicity of each coefficient in `λ`, `d = 2` by the
planar derivative test T4 (`t4_mono`) and obligation O.bar.2.
-/

@[expose] public section

open Real

namespace GMCExplicitDelta.Assembly

open Contract

variable {d : ℕ}

theorem vi_smul {l D F : ℝ} (hl : 0 < l) (hF : 0 < F) :
    vi (l * D) (l * F) = 2 + l * (vi D F - 2) := by
  unfold vi
  field_simp
  ring

theorem vi_ge_two {D F : ℝ} (hF : 0 < F) : 2 ≤ vi D F := by
  unfold vi
  rw [le_div_iff₀ hF]
  nlinarith [sq_nonneg D]

section Row

variable (row : Row d)

theorem Z_pos (hO : row.Obligations) : (0 : ℝ) < row.Z := by exact_mod_cast hO.bar1.1

theorem scaling_tStar_pos (hO : row.Obligations) : 0 < row.tStar := by
  have hZ := Z_pos row hO
  have hZM : (row.Z : ℝ) < row.Mwin := hO.bar1.2.1
  unfold Row.tStar
  exact div_pos hZ (hZ.trans hZM)

theorem tStar_lt_one (hO : row.Obligations) : row.tStar < 1 := by
  have hZ := Z_pos row hO
  have hZM : (row.Z : ℝ) < row.Mwin := hO.bar1.2.1
  unfold Row.tStar
  exact (div_lt_one (hZ.trans hZM)).mpr hZM

theorem ellV_pos : (0 : ℝ) < (ellV d : ℝ) := by
  unfold ellV; split_ifs <;> norm_num

theorem rhoV_pos (hO : row.Obligations) : 0 < row.rhoV := hO.var1.1
theorem rhoV_lt (hO : row.Obligations) : row.rhoV < 1 := hO.var1.2

theorem Qt0_smul (hO : row.Obligations) {l D F : ℝ} (hl : 0 < l) (hF : 0 < F) :
    row.Qt0 (l * D) (l * F) = row.vT0 + l * (row.Qt0 D F - row.vT0) := by
  unfold Row.Qt0 Row.vT0
  rw [vi_smul hl hF]
  ring

theorem Qf0_smul {l D F : ℝ} (hl : 0 < l) (hF : 0 < F) :
    row.Qf0 (l * D) (l * F) = row.vF0 + l * (row.Qf0 D F - row.vF0) := by
  unfold Row.Qf0 Row.vF0
  rw [vi_smul hl hF]
  ring

theorem Qfor_smul (l F : ℝ) : row.Qfor (l * F) = l * row.Qfor F := by
  unfold Row.Qfor; ring

theorem Qt0_sub_vT0 (hO : row.Obligations) {D F : ℝ} (hF : 0 < F) :
    0 ≤ row.Qt0 D F - row.vT0 := by
  have h1 := rhoV_pos row hO
  have h2 := rhoV_lt row hO
  have h3 := vi_ge_two (D := D) hF
  have h4 := ellV_pos (d := d)
  have : row.Qt0 D F - row.vT0 =
      ((ellV d : ℝ) * row.rhoV ^ ((row.jV - 1) / ellV d) / (1 - row.rhoV)) * (vi D F - 2) := by
    unfold Row.Qt0 Row.vT0; ring
  rw [this]
  have : 0 < 1 - row.rhoV := by linarith
  positivity

theorem Qf0_sub_vF0 (hO : row.Obligations) {D F : ℝ} (hF : 0 < F) :
    0 ≤ row.Qf0 D F - row.vF0 := by
  have h1 := rhoV_pos row hO
  have h2 := rhoV_lt row hO
  have h3 := vi_ge_two (D := D) hF
  have h4 := ellV_pos (d := d)
  have : row.Qf0 D F - row.vF0 =
      (1 + (ellV d : ℝ) / (1 - row.rhoV)) * (vi D F - 2) := by
    unfold Row.Qf0 Row.vF0; ring
  rw [this]
  have : 0 < 1 - row.rhoV := by linarith
  positivity

theorem cV_nonneg (hO : row.Obligations) : 0 ≤ row.cV := by
  unfold Row.cV
  split_ifs with h
  · norm_num
  · have : (0 : ℝ) < row.young := by exact_mod_cast (hO.par2.2.2.2.2.2 h).1
    positivity

theorem Qfor_nonneg (hO : row.Obligations) {F : ℝ} (hF : 0 ≤ F) : 0 ≤ row.Qfor F := by
  have := cV_nonneg row hO
  have := ellV_pos (d := d)
  have h2 : 0 < 1 - row.rhoV := by linarith [rhoV_lt row hO]
  unfold Row.Qfor
  positivity

theorem vT0_nonneg (hO : row.Obligations) : 0 ≤ row.vT0 := by
  have := rhoV_pos row hO
  have := ellV_pos (d := d)
  have h2 : 0 < 1 - row.rhoV := by linarith [rhoV_lt row hO]
  unfold Row.vT0
  positivity

theorem vF0_nonneg (hO : row.Obligations) : 0 ≤ row.vF0 := by
  have := rhoV_pos row hO
  have := ellV_pos (d := d)
  have h2 : 0 < 1 - row.rhoV := by linarith [rhoV_lt row hO]
  unfold Row.vF0
  positivity

theorem vT1_nonneg (hO : row.Obligations) {D F : ℝ} (hF : 0 < F) : 0 ≤ row.vT1 D F := by
  have h1 := Qt0_sub_vT0 row hO (D := D) hF
  have h2 := Qfor_nonneg row hO hF.le
  have h3 := scaling_tStar_pos row hO
  have h4 := tStar_lt_one row hO
  unfold Row.vT1
  have : 0 ≤ 1 - row.tStar ^ 2 := by nlinarith
  nlinarith [mul_nonneg h2 this]

theorem vF1_nonneg (hO : row.Obligations) {D F : ℝ} (hF : 0 < F) : 0 ≤ row.vF1 D F := by
  have h1 := Qf0_sub_vF0 row hO (D := D) hF
  have h2 := Qfor_nonneg row hO hF.le
  have h3 := scaling_tStar_pos row hO
  have h4 := tStar_lt_one row hO
  unfold Row.vF1
  have : 0 ≤ 1 - row.tStar ^ 2 := by nlinarith
  nlinarith [mul_nonneg h2 this]

theorem vT_sum_pos (hO : row.Obligations) {D F : ℝ} (hF : 0 < F) :
    0 < row.vT0 + row.vT1 D F := by
  have h1 := rhoV_pos row hO
  have h2 : 0 < 1 - row.rhoV := by linarith [rhoV_lt row hO]
  have h3 := vi_ge_two (D := D) hF
  have h4 := ellV_pos (d := d)
  have h5 := Qfor_nonneg row hO hF.le
  have h6 := tStar_lt_one row hO
  have h7 := scaling_tStar_pos row hO
  have hq : 0 ≤ 1 - row.tStar ^ 2 := by nlinarith
  have : 0 < row.Qt0 D F := by
    unfold Row.Qt0
    have : 0 < vi D F := by linarith
    positivity
  unfold Row.vT1
  nlinarith [mul_nonneg h5 hq]

theorem vF_sum_pos (hO : row.Obligations) {D F : ℝ} (hF : 0 < F) :
    0 < row.vF0 + row.vF1 D F := by
  have h1 := rhoV_pos row hO
  have h2 : 0 < 1 - row.rhoV := by linarith [rhoV_lt row hO]
  have h3 := vi_ge_two (D := D) hF
  have h4 := ellV_pos (d := d)
  have h5 := Qfor_nonneg row hO hF.le
  have h6 := tStar_lt_one row hO
  have h7 := scaling_tStar_pos row hO
  have hq : 0 ≤ 1 - row.tStar ^ 2 := by nlinarith
  have : 0 < row.Qf0 D F := by
    unfold Row.Qf0
    have : 0 < vi D F := by linarith
    positivity
  unfold Row.vF1
  nlinarith [mul_nonneg h5 hq]

theorem cNu_pos (hO : row.Obligations) : 0 < row.cNu := by
  unfold Row.cNu; exact pow_pos hO.geo1.1 d

theorem R_pos (hO : row.Obligations) : (0 : ℝ) < row.R := by
  have : (1 : ℚ) < row.R := hO.par2.1
  have : (1 : ℝ) < row.R := by exact_mod_cast this
  linarith

theorem eps_pos (hO : row.Obligations) : (0 : ℝ) < row.epsilon := by
  exact_mod_cast hO.par2.2.1

theorem haarB_nonneg (k : ℕ) : 0 ≤ row.haarB k := by
  unfold Row.haarB; split_ifs <;> exact Real.sqrt_nonneg _

theorem Sb_nonneg : 0 ≤ row.Sb := tsum_nonneg fun k => haarB_nonneg row k

theorem Sd_nonneg : 0 ≤ row.Sd :=
  tsum_nonneg fun k => mul_nonneg (haarB_nonneg row _) (Real.sqrt_nonneg _)

theorem us_lt_three (hO : row.Obligations) : row.us < 3 := by
  unfold Row.us
  have hs : (row.s : ℝ) < 1 / 2 := by
    have h : row.s < 1 / 2 := hO.par1.2.2.2.2.2.2.1
    have := (Rat.cast_lt (K := ℝ)).2 h
    push_cast at this
    linarith
  calc (3 : ℝ) ^ (row.s : ℝ) < (3 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
    _ = 3 := Real.rpow_one 3

theorem Btail_nonneg (hO : row.Obligations) : 0 ≤ row.Btail := by
  have h1 := us_lt_three row hO
  have h0 : 0 ≤ row.us := by unfold Row.us; positivity
  have : 0 < 1 - row.us / 3 := by linarith
  unfold Row.Btail Row.Ks
  positivity

theorem coefAv_nonneg (hO : row.Obligations) : 0 ≤ row.coefAv := by
  have := cNu_pos row hO
  have := eps_pos row hO
  have := R_pos row hO
  unfold Row.coefAv sigmaV
  split_ifs <;> positivity

theorem coefA_nonneg (hO : row.Obligations) (F : ℝ) : 0 ≤ row.coefA F := by
  have := cNu_pos row hO
  have := eps_pos row hO
  have := R_pos row hO
  unfold Row.coefA sigmaA
  split_ifs <;> positivity

theorem coefB_nonneg (hO : row.Obligations) {F : ℝ} (hF : 0 ≤ F) : 0 ≤ row.coefB F := by
  have := cNu_pos row hO
  have := eps_pos row hO
  unfold Row.coefB sigmaB
  split_ifs <;> positivity

theorem F_pos (hO : row.Obligations) : (0 : ℝ) < row.F := by exact_mod_cast hO.par1.2.1

theorem barrier_ne_two (hO : row.Obligations) (hd2 : d ≠ 2) {l : ℝ} (hl0 : 0 < l) (hl1 : l ≤ 1) :
    row.barrier row.D row.F ≤ row.barrier (l * row.D) (l * row.F) := by
  have hF := F_pos row hO
  have ht0 := scaling_tStar_pos row hO
  have ht1 := tStar_lt_one row hO
  have hq : 0 ≤ 1 - row.tStar ^ 2 := by nlinarith
  have hq1 : 0 ≤ 1 - row.tStar := by linarith
  have hQ : ∀ x : ℝ, x ≤ 1 → ∀ Q : ℝ, 0 ≤ Q → l * Q ≤ Q := fun x _ Q hQ => by nlinarith
  have hQt : row.Qt0 (l * row.D) (l * row.F) + row.Qfor (l * row.F) * (1 - row.tStar ^ 2) ≤
      row.Qt0 row.D row.F + row.Qfor row.F * (1 - row.tStar ^ 2) := by
    rw [Qt0_smul row hO hl0 hF, Qfor_smul]
    have h1 := Qt0_sub_vT0 row hO (D := row.D) hF
    have h2 := Qfor_nonneg row hO hF.le
    nlinarith [mul_nonneg h2 hq, mul_nonneg (mul_nonneg h2 hq) (sub_nonneg.2 hl1),
      mul_nonneg h1 (sub_nonneg.2 hl1)]
  have hQf : row.Qf0 (l * row.D) (l * row.F) + row.Qfor (l * row.F) * (1 - row.tStar ^ 2) ≤
      row.Qf0 row.D row.F + row.Qfor row.F * (1 - row.tStar ^ 2) := by
    rw [Qf0_smul row hl0 hF, Qfor_smul]
    have h1 := Qf0_sub_vF0 row hO (D := row.D) hF
    have h2 := Qfor_nonneg row hO hF.le
    nlinarith [mul_nonneg h2 hq, mul_nonneg (mul_nonneg h2 hq) (sub_nonneg.2 hl1),
      mul_nonneg h1 (sub_nonneg.2 hl1)]
  have hA : row.coefA (l * row.F) ≤ row.coefA row.F := by
    unfold Row.coefA sigmaA
    rw [if_neg hd2, if_neg hd2]
    apply mul_le_mul_of_nonneg_left
    · exact Real.sqrt_le_sqrt (by nlinarith)
    · have := cNu_pos row hO; have := eps_pos row hO; have := R_pos row hO; positivity
  have hB : row.coefB (l * row.F) ≤ row.coefB row.F := by
    unfold Row.coefB sigmaB
    rw [if_neg hd2, if_neg hd2]
    apply mul_le_mul_of_nonneg_left
    · nlinarith
    · have := cNu_pos row hO; have := eps_pos row hO; positivity
  have hC : row.Cbar (l * row.D) (l * row.F) ≤ row.Cbar row.D row.F := by
    unfold Row.Cbar Row.qStar Row.rStar
    simp only [if_neg hd2]
    simp only [Real.sqrt_one, mul_one, div_one]
    have hSd := Sd_nonneg row
    have hSb := Sb_nonneg row
    have hBt := Btail_nonneg row hO
    have hAv := coefAv_nonneg row hO
    have hs1 : 0 ≤ √(1 - row.tStar) := Real.sqrt_nonneg _
    have e1 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hA hSd) hs1
    have e2 := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hQt) hSb
    have e3 := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hQf) hBt
    have := mul_le_mul_of_nonneg_left (add_le_add e2 e3) hAv
    linarith
  unfold Row.barrier Row.qStar
  simp only [if_neg hd2]
  have hsZ := Real.sqrt_nonneg (row.Z : ℝ)
  have hν : (0 : ℝ) ≤ row.nu := Nat.cast_nonneg _
  have c1 := mul_le_mul_of_nonneg_right hC hsZ
  have c2 := mul_le_mul_of_nonneg_left hB (mul_nonneg hν hq1)
  nlinarith

theorem uStar_smul (l F : ℝ) : row.uStar (l * F) = l * row.uStar F := by
  unfold Row.uStar; ring

theorem barrier_eq_two (hO : row.Obligations) (hd2 : d = 2) {l : ℝ} (hl0 : 0 < l)
    (hl1 : l ≤ 1) :
    row.barrier (l * row.D) (l * row.F) =
      (1 - row.tauAbs) * (row.Z : ℝ) - row.t4R row.D row.F l * √(row.Z : ℝ) -
        (row.Mwin : ℝ) * (row.badBudget : ℝ) := by
  have hF := F_pos row hO
  have hsZ : 0 < √(row.Z : ℝ) := Real.sqrt_pos.mpr (Z_pos row hO)
  have eA : row.coefA (l * row.F) = row.coefA row.F := by
    unfold Row.coefA sigmaA; simp [hd2]
  have eB : row.coefB (l * row.F) = row.coefB row.F := by
    unfold Row.coefB sigmaB; simp [hd2]
  have eq' : row.Qt0 (l * row.D) (l * row.F) + row.Qfor (l * row.F) * (1 - row.tStar ^ 2) =
      row.vT0 + l * row.vT1 row.D row.F := by
    rw [Qt0_smul row hO hl0 hF, Qfor_smul]; unfold Row.vT1; ring
  have eq'' : row.Qf0 (l * row.D) (l * row.F) + row.Qfor (l * row.F) * (1 - row.tStar ^ 2) =
      row.vF0 + l * row.vF1 row.D row.F := by
    rw [Qf0_smul row hl0 hF, Qfor_smul]; unfold Row.vF1; ring
  have eq : row.qStar (l * row.F) = qMatch (l * row.uStar row.F) := by
    unfold Row.qStar; rw [if_pos hd2, uStar_smul]
  have er : row.rStar (l * row.F) = rMatch (l * row.uStar row.F) := by
    unfold Row.rStar; rw [if_pos hd2, uStar_smul]
  have hr : 0 < rMatch (l * row.uStar row.F) :=
    rMatch_pos (by have := scaling_tStar_pos row hO; unfold Row.uStar; positivity)
  have hv1 : 0 ≤ row.vT0 + l * row.vT1 row.D row.F := by
    have := vT0_nonneg row hO; have := vT1_nonneg row hO (D := row.D) hF; positivity
  have hv2 : 0 ≤ row.vF0 + l * row.vF1 row.D row.F := by
    have := vF0_nonneg row hO; have := vF1_nonneg row hO (D := row.D) hF; positivity
  unfold Row.barrier Row.Cbar
  rw [eA, eB, eq, er, eq', eq'']
  unfold Row.t4R Row.t4a Row.t4b Row.t4c Row.t4L
  rw [Real.sqrt_div hv1, Real.sqrt_div hv2]
  have hsr : 0 < √(rMatch (l * row.uStar row.F)) := Real.sqrt_pos.mpr hr
  field_simp
  ring

/-- **R4(e)–(f) (barrier at smaller disorder).** Statement of the target. -/
theorem barrier_scale_pos_proof (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ))
    (hO : row.Obligations)
    {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) :
    0 < row.barrier (lam * row.D) (lam * row.F) := by
  by_cases hd2 : d = 2
  · have hF := F_pos row hO
    have hsZ : 0 < √(row.Z : ℝ) := Real.sqrt_pos.mpr (Z_pos row hO)
    obtain ⟨hn1, hn2, hS, hM⟩ := hO.bar2 hd2
    have ht0 := scaling_tStar_pos row hO
    have ht1 := tStar_lt_one row hO
    have hF1 : (row.F : ℝ) ≤ 1 := by
      have : row.F ≤ 1 := (hO.par1.2.2.1).trans (min_le_right _ _)
      exact_mod_cast this
    have hu0 : 0 < row.uStar row.F := by unfold Row.uStar; positivity
    have hu1 : row.uStar row.F ≤ 1 := by
      unfold Row.uStar; nlinarith
    have hq1 : 0 ≤ 1 - row.tStar := by linarith
    have hmono := t4_mono (u := row.uStar row.F) (a := row.t4a row.F) (b := row.t4b)
      (c := row.t4c) (L := row.t4L row.F) (v0t := row.vT0) (v1t := row.vT1 row.D row.F)
      (v0f := row.vF0) (v1f := row.vF1 row.D row.F) hu0 hu1
      (by unfold Row.t4a
          have := coefA_nonneg row hO row.F; have := Sd_nonneg row
          have := Real.sqrt_nonneg (1 - row.tStar); positivity)
      (by unfold Row.t4b
          have := coefAv_nonneg row hO; have := Sb_nonneg row; positivity)
      (by unfold Row.t4c
          have := coefAv_nonneg row hO; have := Btail_nonneg row hO; positivity)
      (by unfold Row.t4L
          have := coefB_nonneg row hO hF.le; positivity)
      (vT0_nonneg row hO) (vT1_nonneg row hO hF) (vF0_nonneg row hO) (vF1_nonneg row hO hF)
      (vT_sum_pos row hO hF) (vF_sum_pos row hO hF) hn1 hn2 hS
    have hle : row.t4R row.D row.F lam ≤ row.t4R row.D row.F 1 :=
      hmono ⟨h0, h1⟩ ⟨one_pos, le_rfl⟩ h1
    rw [barrier_eq_two row hO hd2 h0 h1]
    have key : √(row.Z : ℝ) * ((1 - row.tauAbs) * √(row.Z : ℝ) - row.t4R row.D row.F 1 -
        (row.Mwin : ℝ) * (row.badBudget : ℝ) / √(row.Z : ℝ)) =
        (1 - row.tauAbs) * (row.Z : ℝ) - row.t4R row.D row.F 1 * √(row.Z : ℝ) -
          (row.Mwin : ℝ) * (row.badBudget : ℝ) := by
      have hs := Real.mul_self_sqrt (Z_pos row hO).le
      field_simp
      linear_combination (1 - row.tauAbs) * hs
    have hpos := mul_pos hsZ hM
    rw [key] at hpos
    nlinarith [mul_le_mul_of_nonneg_right hle hsZ.le]
  · exact (hO.bar1.2.2).trans_le (barrier_ne_two row hO hd2 h0 h1)

end Row

end GMCExplicitDelta.Assembly
