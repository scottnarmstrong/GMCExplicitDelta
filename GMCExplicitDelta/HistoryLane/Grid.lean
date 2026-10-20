module

public import GMCExplicitDelta.HistoryLane.Sums2

/-!
# History lane: the summation step of G6

`grid_term_le`: for `b_g > 0`, `w x^L B_L ≤ U_grid`, so that
`w^{t+L+1} 3^{d(L+t)/32} B_L = x^t · w x^L B_L ≤ x^t U_grid`.
-/

@[expose] public section

open Real

namespace GMCExplicitDelta.Assembly

open GMCExplicitDelta.Contract GMCExplicitDelta.Certificates

variable {d : ℕ}

theorem M1_term_bdd' {b c A : ℝ} (hb : 0 < b) (hc : 0 ≤ c) (hA : 0 ≤ A) (t : ℝ) (ht : 1 ≤ t) :
    (c * √t + A) ^ 2 * Real.exp (-(b * t)) ≤ 2 * c ^ 2 / b + 2 * A ^ 2 := by
  have ht0 : 0 < t := by linarith
  have hs : √t ^ 2 = t := Real.sq_sqrt ht0.le
  have h1 : (c * √t + A) ^ 2 ≤ 2 * c ^ 2 * t + 2 * A ^ 2 := by
    nlinarith [sq_nonneg (c * √t - A)]
  have he : Real.exp (-(b * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have he0 : 0 < Real.exp (-(b * t)) := Real.exp_pos _
  have h2 : t * Real.exp (-(b * t)) ≤ 1 / b := by
    have hge : b * t + 1 ≤ Real.exp (b * t) := Real.add_one_le_exp _
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) hb]
    nlinarith
  calc (c * √t + A) ^ 2 * Real.exp (-(b * t))
      ≤ (2 * c ^ 2 * t + 2 * A ^ 2) * Real.exp (-(b * t)) :=
        mul_le_mul_of_nonneg_right h1 he0.le
    _ = 2 * c ^ 2 * (t * Real.exp (-(b * t))) + 2 * A ^ 2 * Real.exp (-(b * t)) := by ring
    _ ≤ 2 * c ^ 2 * (1 / b) + 2 * A ^ 2 * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left h2 (by positivity))
          (mul_le_mul_of_nonneg_left he (by positivity))
    _ = _ := by ring

theorem M2_term_bdd' {b : ℝ} (hb : 0 < b) (t : ℝ) (ht : 1 ≤ t) :
    t ^ 2 * Real.exp (-(b * t)) ≤ 2 / b ^ 2 := by
  have ht0 : 0 < t := by linarith
  have hbt : 0 < b * t := by positivity
  have hge : (b * t) ^ 2 / 2 ≤ Real.exp (b * t) := by
    have := Real.quadratic_le_exp_of_nonneg hbt.le
    nlinarith
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
  nlinarith

theorem le_M1 (row : Row d) {δ : ℝ} (hb : 0 < row.bg δ) {t : ℝ} (ht : 1 ≤ t) :
    (row.cg * √t + row.Ag) ^ 2 * Real.exp (-(row.bg δ * t)) ≤ row.M1 δ := by
  unfold Row.M1
  have hbdd : BddAbove (Set.range fun t : Set.Ici (1 : ℝ) =>
      (row.cg * √(t : ℝ) + row.Ag) ^ 2 * Real.exp (-(row.bg δ * t))) :=
    ⟨2 * row.cg ^ 2 / row.bg δ + 2 * row.Ag ^ 2, by
      rintro _ ⟨s, rfl⟩
      exact M1_term_bdd' hb (cg_nonneg row) (Ag_nonneg row) s s.2⟩
  exact le_ciSup hbdd (⟨t, ht⟩ : Set.Ici (1 : ℝ))

theorem le_M2 (row : Row d) {δ : ℝ} (hb : 0 < row.bg δ) {t : ℝ} (ht : 1 ≤ t) :
    t ^ 2 * Real.exp (-(row.bg δ * t)) ≤ row.M2 δ := by
  unfold Row.M2
  have hbdd : BddAbove (Set.range fun t : Set.Ici (1 : ℝ) =>
      (t : ℝ) ^ 2 * Real.exp (-(row.bg δ * t))) :=
    ⟨2 / row.bg δ ^ 2, by
      rintro _ ⟨s, rfl⟩
      exact M2_term_bdd' hb s s.2⟩
  exact le_ciSup hbdd (⟨t, ht⟩ : Set.Ici (1 : ℝ))

theorem Ugrid_nonneg' (row : Row d) {δ : ℝ} (hε : 0 < (row.epsSub : ℝ)) :
    0 ≤ row.Ugrid δ := by
  have h1 := M1_nonneg row δ
  have h2 := M2_nonneg row δ
  have hP : 0 ≤ P32 := by unfold P32; positivity
  have hκ := kappaH_nonneg' d
  have hx := xHist_pos' row
  have hw0 : 0 ≤ row.wHaar := by unfold Row.wHaar; positivity
  unfold Row.Ugrid Row.hbar varsigma
  split_ifs
  · positivity
  · have : 0 ≤ (row.epsSub : ℝ)⁻¹ := inv_nonneg.2 hε.le
    positivity

theorem grid_exp_identity (row : Row d) (δ : ℝ) (L : ℕ) :
    row.xHist ^ L *
        Real.exp ((64 * (proxyA : ℝ) * ((L : ℝ) + 1) + 32 * row.Ag ^ 2 +
          kappaH d * ((L : ℝ) + 1)) * δ ^ 2) =
      row.xHist⁻¹ * Real.exp (32 * row.Ag ^ 2 * δ ^ 2) *
        Real.exp (-(row.bg δ * ((L : ℝ) + 1))) := by
  have hx := xHist_pos' row
  have h1 : Real.exp (((L + 1 : ℕ) : ℝ) * Real.log row.xHist) = row.xHist ^ (L + 1) := by
    rw [Real.exp_nat_mul, Real.exp_log hx]
  have h2 : -(row.bg δ * ((L : ℝ) + 1)) =
      ((L + 1 : ℕ) : ℝ) * Real.log row.xHist +
        ((L : ℝ) + 1) * ((64 * (proxyA : ℝ) + kappaH d) * δ ^ 2) := by
    unfold Row.bg; push_cast; ring
  have hE : Real.exp ((64 * (proxyA : ℝ) * ((L : ℝ) + 1) + 32 * row.Ag ^ 2 +
          kappaH d * ((L : ℝ) + 1)) * δ ^ 2) =
      Real.exp (32 * row.Ag ^ 2 * δ ^ 2) *
        Real.exp (((L : ℝ) + 1) * ((64 * (proxyA : ℝ) + kappaH d) * δ ^ 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h2, Real.exp_add, h1, hE, pow_succ]
  field_simp
  try ring

theorem grid_term_le (row : Row d) (hε : 0 < (row.epsSub : ℝ)) {δ : ℝ} (hδ : 0 < δ)
    (hb : 0 < row.bg δ) (L : ℕ) :
    row.wHaar * row.xHist ^ L * gridBound row δ L ≤ row.Ugrid δ := by
  have hx := xHist_pos' row
  have hw0 : 0 ≤ row.wHaar := by unfold Row.wHaar; positivity
  have hκ := kappaH_nonneg' d
  have hP : 0 ≤ P32 := by unfold P32; positivity
  have hc := cg_nonneg row
  have hA := Ag_nonneg row
  have hk : (1 : ℝ) ≤ (L : ℝ) + 1 := by have : (0 : ℝ) ≤ L := Nat.cast_nonneg L; linarith
  set k : ℝ := (L : ℝ) + 1 with hkdef
  have hk0 : 0 < k := by linarith
  have hsq : √k ^ 2 = k := Real.sq_sqrt hk0.le
  have hsP : √P32 ^ 2 = P32 := Real.sq_sqrt hP
  set Xv : ℝ := δ * √P32 * (row.cg * √k + row.Ag) with hXv
  set Yv : ℝ := kappaH d * k * δ ^ 2 with hYv
  have hbr : (Xv + Yv) ^ 2 * Real.exp (-(row.bg δ * k)) ≤
      (if d = 2 then P32 * δ ^ 2 * row.M1 δ
        else (1 + (row.epsSub : ℝ)) * P32 * δ ^ 2 * row.M1 δ +
          (1 + (row.epsSub : ℝ)⁻¹) * kappaH d ^ 2 * δ ^ 4 * row.M2 δ) := by
    have hm1 := le_M1 row hb hk
    have hm2 := le_M2 row hb hk
    have he0 := (Real.exp_pos (-(row.bg δ * k))).le
    have hX2 : Xv ^ 2 * Real.exp (-(row.bg δ * k)) ≤ P32 * δ ^ 2 * row.M1 δ := by
      have : Xv ^ 2 = P32 * δ ^ 2 * (row.cg * √k + row.Ag) ^ 2 := by
        rw [hXv, mul_pow, mul_pow, hsP]; ring
      rw [this, mul_assoc]
      exact mul_le_mul_of_nonneg_left hm1 (by positivity)
    split_ifs with h2
    · have : kappaH d = 0 := by simp [kappaH, h2]
      have hY : Yv = 0 := by rw [hYv, this]; ring
      rw [hY, add_zero]; exact hX2
    · have hY2 : Yv ^ 2 * Real.exp (-(row.bg δ * k)) ≤
          kappaH d ^ 2 * δ ^ 4 * row.M2 δ := by
        have : Yv ^ 2 = kappaH d ^ 2 * δ ^ 4 * k ^ 2 := by rw [hYv]; ring
        rw [this, mul_assoc]
        exact mul_le_mul_of_nonneg_left hm2 (by positivity)
      have hyoung : (Xv + Yv) ^ 2 ≤ (1 + (row.epsSub : ℝ)) * Xv ^ 2 +
          (1 + (row.epsSub : ℝ)⁻¹) * Yv ^ 2 := by
        have hne := hε.ne'
        have : (1 + (row.epsSub : ℝ)) * Xv ^ 2 + (1 + (row.epsSub : ℝ)⁻¹) * Yv ^ 2 -
            (Xv + Yv) ^ 2 = ((row.epsSub : ℝ) ^ 2 * Xv ^ 2 - 2 * (row.epsSub : ℝ) * Xv * Yv + Yv ^ 2) /
              (row.epsSub : ℝ) := by field_simp; ring
        have h0 : 0 ≤ ((row.epsSub : ℝ) ^ 2 * Xv ^ 2 - 2 * (row.epsSub : ℝ) * Xv * Yv + Yv ^ 2) /
            (row.epsSub : ℝ) := div_nonneg (by nlinarith [sq_nonneg ((row.epsSub : ℝ) * Xv - Yv)]) hε.le
        linarith
      calc (Xv + Yv) ^ 2 * Real.exp (-(row.bg δ * k)) ≤
          ((1 + (row.epsSub : ℝ)) * Xv ^ 2 + (1 + (row.epsSub : ℝ)⁻¹) * Yv ^ 2) *
            Real.exp (-(row.bg δ * k)) := mul_le_mul_of_nonneg_right hyoung he0
        _ = (1 + (row.epsSub : ℝ)) * (Xv ^ 2 * Real.exp (-(row.bg δ * k))) +
            (1 + (row.epsSub : ℝ)⁻¹) * (Yv ^ 2 * Real.exp (-(row.bg δ * k))) := by ring
        _ ≤ (1 + (row.epsSub : ℝ)) * (P32 * δ ^ 2 * row.M1 δ) +
            (1 + (row.epsSub : ℝ)⁻¹) * (kappaH d ^ 2 * δ ^ 4 * row.M2 δ) := by
            gcongr
        _ = _ := by ring
  have hid := grid_exp_identity row δ L
  have hpre : 0 ≤ row.wHaar * varsigma * row.hbar / (2 * row.xHist) *
      Real.exp (32 * row.Ag ^ 2 * δ ^ 2) := by
    unfold varsigma Row.hbar; positivity
  have e : row.wHaar * row.xHist ^ L * gridBound row δ L =
      (row.wHaar * varsigma * row.hbar / (2 * row.xHist) * Real.exp (32 * row.Ag ^ 2 * δ ^ 2)) *
        ((Xv + Yv) ^ 2 * Real.exp (-(row.bg δ * k))) := by
    unfold gridBound
    have := hid
    calc _ = row.wHaar * (varsigma * row.hbar / 2) * (Xv + Yv) ^ 2 *
          (row.xHist ^ L * Real.exp ((64 * (proxyA : ℝ) * k + 32 * row.Ag ^ 2 + kappaH d * k) * δ ^ 2)) := by
            rw [hXv, hYv, hkdef]; ring
      _ = _ := by rw [this]; field_simp; try rfl
  rw [e]
  unfold Row.Ugrid
  exact mul_le_mul_of_nonneg_left hbr hpre

end GMCExplicitDelta.Assembly
