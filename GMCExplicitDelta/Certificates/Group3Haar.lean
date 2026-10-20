module

public import GMCExplicitDelta.Haar.TailsGeometric
public import GMCExplicitDelta.Numerics.Enclosures

/-!
# Numeric obligations, group 3: certified Haar sums

Row-independent machinery: rational upper bounds for the coefficients `b_k` (from the split bound
for the minimum series, H14), certificate checkers over `ℚ` (checked by `decide +kernel` in the
row files), and the finite-sum-plus-tail bounds for `S_b` and `S_d` (H12).
-/

@[expose] public section

open Real

namespace GMCExplicitDelta.Certificates.G3

open GMCExplicitDelta.Contract GMCExplicitDelta.Haar

variable {d : ℕ}

/-! ### Rational majorants -/

/-- The split bound `L q^J + H (q-1) (q/9)^J / (1 - q/9)` of `L + (q-1) minSeries q L H`. -/
def bSq (L H q : ℚ) (J : ℕ) : ℚ := L * q ^ J + H * (q - 1) * (q / 9) ^ J / (1 - q / 9)

/-- A rational upper bound for `𝖫_k`. -/
def Lu (d : ℕ) (η pl ph : ℚ) (k : ℕ) : ℚ :=
  if d = 2 ∧ k = 1 then 1 / 5 + 243 / (10 * pl ^ 4) else η * (5 * ph ^ 2 / 54) * (9 / 9 ^ k)

/-- A rational upper bound for `𝖧_k`. -/
def Hu (d : ℕ) (η pl ph : ℚ) (k : ℕ) : ℚ := η * (1 + d * Lu d η pl ph k)

theorem haarL_le_Lu (row : Row d) {η pl ph : ℚ} (hη : row.etaOmega = (η : ℝ)) (hpl : 0 < pl)
    (h1 : (pl : ℝ) ≤ π) (h2 : π ≤ (ph : ℝ)) (k : ℕ) : row.haarL k ≤ (Lu d η pl ph k : ℝ) := by
  have hpl' : (0 : ℝ) < pl := by exact_mod_cast hpl
  have hpi : 0 < π := lt_of_lt_of_le hpl' h1
  have hη0 : 0 ≤ (η : ℝ) := by rw [← hη]; unfold Row.etaOmega; positivity
  by_cases h : d = 2 ∧ k = 1
  · simp only [Row.haarL, Lu, h, and_self, ite_true]
    push_cast
    gcongr
  · simp only [Row.haarL, Lu, h, ite_false]
    rw [hη]
    push_cast
    gcongr

theorem haarH_le_Hu (row : Row d) {η pl ph : ℚ} (hη : row.etaOmega = (η : ℝ)) (hpl : 0 < pl)
    (h1 : (pl : ℝ) ≤ π) (h2 : π ≤ (ph : ℝ)) (k : ℕ) : row.haarH k ≤ (Hu d η pl ph k : ℝ) := by
  have hη0 : 0 ≤ (η : ℝ) := by rw [← hη]; unfold Row.etaOmega; positivity
  have hL := haarL_le_Lu row hη hpl h1 h2 k
  unfold Row.haarH Hu
  rw [hη]
  push_cast
  gcongr

/-- The split estimate for `L + (q-1) minSeries q L H` with monotone dependence on the data. -/
theorem energy_le_bSq {q qu L H Lu' Hu' : ℝ} (hq1 : 1 < q) (hq : q ≤ qu) (hqu : qu < 9)
    (hL : 0 ≤ L) (hH : 0 ≤ H) (hLu : L ≤ Lu') (hHu : H ≤ Hu') (J : ℕ) :
    L + (q - 1) * minSeries q L H ≤
      Lu' * qu ^ J + Hu' * (qu - 1) * (qu / 9) ^ J / (1 - qu / 9) := by
  have hq0 : 0 ≤ q := le_trans zero_le_one hq1.le
  have hq9 : q < 9 := lt_of_le_of_lt hq hqu
  have hd : 0 < 1 - q / 9 := sub_pos.mpr ((div_lt_one (by norm_num : (0 : ℝ) < 9)).2 hq9)
  have hdu : 0 < 1 - qu / 9 := sub_pos.mpr ((div_lt_one (by norm_num : (0 : ℝ) < 9)).2 hqu)
  have hs := minSeries_le_split hq1 hq9 hL hH J
  have h1 := mul_le_mul_of_nonneg_left hs (sub_nonneg.mpr hq1.le)
  have halg : L + (q - 1) *
      (L * (q ^ J - 1) / (q - 1) + H * (q / 9) ^ J / (1 - q / 9)) =
      L * q ^ J + H * ((q - 1) / (1 - q / 9)) * (q / 9) ^ J := by
    field_simp [(sub_pos.mpr hq1).ne', hd.ne']
    ring
  have hqu0 : 0 ≤ qu := hq0.trans hq
  have hLu0 : 0 ≤ Lu' := hL.trans hLu
  have hratio : (q - 1) / (1 - q / 9) ≤ (qu - 1) / (1 - qu / 9) := by
    apply div_le_div₀ (by linarith) (by linarith) hdu (by linarith)
  have e1 : L * q ^ J ≤ Lu' * qu ^ J :=
    mul_le_mul hLu (pow_le_pow_left₀ hq0 hq J) (pow_nonneg hq0 J) hLu0
  have e2 : H * ((q - 1) / (1 - q / 9)) * (q / 9) ^ J ≤
      Hu' * ((qu - 1) / (1 - qu / 9)) * (qu / 9) ^ J := by
    have hr0 : 0 ≤ (q - 1) / (1 - q / 9) := div_nonneg (by linarith) hd.le
    have hr0u : 0 ≤ (qu - 1) / (1 - qu / 9) := div_nonneg (by linarith) hdu.le
    refine mul_le_mul (mul_le_mul hHu hratio hr0 (hH.trans hHu))
      (pow_le_pow_left₀ (by positivity) (by linarith) J) (by positivity)
      (mul_nonneg (hH.trans hHu) hr0u)
  calc
    L + (q - 1) * minSeries q L H ≤ L + (q - 1) *
        (L * (q ^ J - 1) / (q - 1) + H * (q / 9) ^ J / (1 - q / 9)) := by linarith only [h1]
    _ = L * q ^ J + H * ((q - 1) / (1 - q / 9)) * (q / 9) ^ J := halg
    _ ≤ Lu' * qu ^ J + Hu' * ((qu - 1) / (1 - qu / 9)) * (qu / 9) ^ J := add_le_add e1 e2
    _ = _ := by ring

theorem haarB_le_cert (row : Row d) {k : ℕ} (hk : 1 ≤ k) (hq1 : 1 < row.qs) {qu : ℚ}
    (hq : row.qs ≤ qu) (hqu : (qu : ℝ) < 9) {L H : ℚ} (hL : row.haarL k ≤ L)
    (hH : row.haarH k ≤ H) (J : ℕ) {r : ℚ} (hr : 0 ≤ r) (h : bSq L H qu J ≤ r ^ 2) :
    row.haarB k ≤ r := by
  unfold Row.haarB
  rw [ite_eq_right (by omega)]
  refine Real.sqrt_le_iff.2 ⟨by exact_mod_cast hr, ?_⟩
  have hL0 := haarL_nonneg row k
  have hH0 := haarH_nonneg row k
  refine (energy_le_bSq hq1 hq hqu hL0 hH0 hL hH J).trans ?_
  have : ((bSq L H qu J : ℚ) : ℝ) ≤ ((r ^ 2 : ℚ) : ℝ) := by exact_mod_cast h
  simpa only [bSq, Rat.cast_add, Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_sub,
    Rat.cast_one, Rat.cast_ofNat] using this

/-! ### Certificate checkers (decided by the kernel in the row files) -/

/-- The check for `b_k ≤ r`. -/
abbrev chkB (d : ℕ) (η pl ph qu : ℚ) (k J : ℕ) (r : ℚ) : Prop :=
  0 ≤ r ∧ bSq (Lu d η pl ph k) (Hu d η pl ph k) qu J ≤ r ^ 2

theorem haarB_le_chk (row : Row d) {η pl ph qu : ℚ} (hη : row.etaOmega = (η : ℝ)) (hpl : 0 < pl)
    (h1 : (pl : ℝ) ≤ π) (h2 : π ≤ (ph : ℝ)) (hq1 : 1 < row.qs) (hq : row.qs ≤ qu)
    (hqu : (qu : ℝ) < 9) {k : ℕ} (hk : 1 ≤ k) {J : ℕ} {r : ℚ} (hc : chkB d η pl ph qu k J r) :
    row.haarB k ≤ r :=
  haarB_le_cert row hk hq1 hq hqu (haarL_le_Lu row hη hpl h1 h2 k)
    (haarH_le_Hu row hη hpl h1 h2 k) J hc.1 hc.2

/-- The ellipticity root is bounded by a rational. -/
theorem yk_le_cert (row : Row d) {θ qu σ : ℚ} (hR : 1 ≤ (row.R : ℝ)) (hθ : row.thetaR = (θ : ℝ))
    (hq1 : 1 ≤ row.qs) (hq : row.qs ≤ qu) (k : ℕ) (hσ0 : 0 ≤ σ)
    (hσ : (θ * qu ^ k) * (θ * qu ^ k + 2) ≤ σ ^ 2) :
    row.yk k ≤ 1 + (θ : ℝ) * (qu : ℝ) ^ k + σ := by
  have hθ0 : 0 ≤ (θ : ℝ) := by rw [← hθ]; exact thetaR_nonneg row hR
  have hq0 : 0 ≤ row.qs := le_trans zero_le_one hq1
  have ht0 : 0 ≤ row.thetaR * row.qs ^ k := mul_nonneg (by rw [hθ]; exact hθ0) (pow_nonneg hq0 k)
  have htT : row.thetaR * row.qs ^ k ≤ (θ : ℝ) * (qu : ℝ) ^ k := by
    rw [hθ]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq0 hq k) hθ0
  have hσ' : (θ * qu ^ k : ℝ) * ((θ : ℝ) * (qu : ℝ) ^ k + 2) ≤ (σ : ℝ) ^ 2 := by
    exact_mod_cast hσ
  have hsq : √(row.thetaR * row.qs ^ k * (row.thetaR * row.qs ^ k + 2)) ≤ σ := by
    refine Real.sqrt_le_iff.2 ⟨by exact_mod_cast hσ0, ?_⟩
    refine le_trans ?_ hσ'
    exact mul_le_mul htT (by linarith) (by linarith) (ht0.trans htT)
  unfold Row.yk ellipX
  linarith

/-- The check for `b_k √(k y_k / R) ≤ r s`. -/
abbrev chkW (d : ℕ) (η pl ph qu θ R : ℚ) (k J : ℕ) (r σ s : ℚ) : Prop :=
  chkB d η pl ph qu k J r ∧ 0 ≤ σ ∧ (θ * qu ^ k) * (θ * qu ^ k + 2) ≤ σ ^ 2 ∧ 0 ≤ s ∧
    (k : ℚ) * (1 + θ * qu ^ k + σ) / R ≤ s ^ 2

theorem haarW_le_chk (row : Row d) {η pl ph qu θ : ℚ} (hη : row.etaOmega = (η : ℝ))
    (hpl : 0 < pl) (h1 : (pl : ℝ) ≤ π) (h2 : π ≤ (ph : ℝ)) (hq1 : 1 < row.qs)
    (hq : row.qs ≤ qu) (hqu : (qu : ℝ) < 9) (hR : 1 ≤ (row.R : ℝ))
    (hθ : row.thetaR = (θ : ℝ)) {k : ℕ} (hk : 1 ≤ k) {J : ℕ} {r σ s : ℚ}
    (hc : chkW d η pl ph qu θ row.R k J r σ s) :
    row.haarB k * √((k : ℝ) * row.yk k / (row.R : ℝ)) ≤ (r : ℝ) * s := by
  obtain ⟨hB, hσ0, hσ, hs0, hs⟩ := hc
  have hb := haarB_le_chk row hη hpl h1 h2 hq1 hq hqu hk hB
  have hy := yk_le_cert row hR hθ hq1.le hq k hσ0 hσ
  have hR0 : 0 < (row.R : ℝ) := lt_of_lt_of_le zero_lt_one hR
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hsq : √((k : ℝ) * row.yk k / (row.R : ℝ)) ≤ s := by
    refine Real.sqrt_le_iff.2 ⟨by exact_mod_cast hs0, ?_⟩
    have hs' : (k : ℝ) * (1 + (θ : ℝ) * (qu : ℝ) ^ k + σ) / (row.R : ℝ) ≤ (s : ℝ) ^ 2 := by
      exact_mod_cast hs
    refine le_trans ?_ hs'
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hy hk0) hR0.le
  exact mul_le_mul hb hsq (Real.sqrt_nonneg _) (by exact_mod_cast hB.1)

/-! ### Rational sums -/

/-- `∑_{i<n} f i` as a recursion the kernel evaluates directly. -/
def sumQ (f : ℕ → ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => sumQ f n + f n

theorem sumQ_cast (f : ℕ → ℚ) (n : ℕ) :
    ((sumQ f n : ℚ) : ℝ) = ∑ i ∈ Finset.range n, (f i : ℝ) := by
  induction n with
  | zero => simp [sumQ]
  | succ n ih => rw [sumQ, Rat.cast_add, ih, Finset.sum_range_succ]

/-! ### `S_b` and `S_d` -/

variable (row : Row d)

theorem haar_hyps_summable (hq1 : 1 < row.qs) (hq9 : row.qs < 9) (hu3 : row.us < 3)
    (hL : ∀ k, 1 ≤ k → row.haarL k ≤ row.L1sharp * (9 / 9 ^ k))
    (hH : ∀ k, 1 ≤ k → row.haarH k ≤ row.Hsharp) : Summable row.haarB := by
  have htail := haarB_tail_le row hq1 hq9 hu3 hL hH 0
  apply (summable_nat_add_iff 1).1
  simpa only [zero_add, Nat.add_comm 1] using htail.1

theorem Sb_le_cert (hq1 : 1 < row.qs) (hq9 : row.qs < 9) (hu3 : row.us < 3)
    (hL : ∀ k, 1 ≤ k → row.haarL k ≤ row.L1sharp * (9 / 9 ^ k))
    (hH : ∀ k, 1 ≤ k → row.haarH k ≤ row.Hsharp) (K : ℕ) {rr : ℕ → ℚ}
    (hr : ∀ k, k ≤ K → row.haarB k ≤ (rr k : ℝ)) :
    row.Sb ≤ (sumQ rr (K + 1) : ℝ) +
      row.Ks * (row.us / 3) ^ (K + 1) / (1 - row.us / 3) := by
  have hsum := haar_hyps_summable row hq1 hq9 hu3 hL hH
  have htail := haarB_tail_le row hq1 hq9 hu3 hL hH K
  have hsplit := hsum.sum_add_tsum_nat_add (K + 1)
  have e : (fun j => row.haarB (j + (K + 1))) = fun j => row.haarB (K + 1 + j) := by
    funext j; rw [Nat.add_comm]
  rw [e] at hsplit
  unfold Row.Sb
  rw [← hsplit, sumQ_cast]
  refine add_le_add ?_ htail.2
  exact Finset.sum_le_sum fun k hk => hr k (by simpa [Nat.lt_succ_iff] using hk)

theorem Sd_le_cert (hq1 : 1 < row.qs) (hq9 : row.qs < 9) (hR : 1 ≤ (row.R : ℝ))
    (hrho : row.rhoS < 1)
    (hL : ∀ k, 1 ≤ k → row.haarL k ≤ row.L1sharp * (9 / 9 ^ k))
    (hH : ∀ k, 1 ≤ k → row.haarH k ≤ row.Hsharp) (K : ℕ) {ww : ℕ → ℚ}
    (hw : ∀ k, 1 ≤ k → k ≤ K →
      row.haarB k * √((k : ℝ) * row.yk k / (row.R : ℝ)) ≤ (ww k : ℝ)) :
    row.Sd ≤ (sumQ (fun i => ww (i + 1)) K : ℝ) +
      row.Ks * row.rhoS ^ (K + 1) * ((K : ℝ) + 1 - (K : ℝ) * row.rhoS) / (1 - row.rhoS) ^ 2 := by
  have htail := haarB_weighted_tail_le row hq1 hq9 hR hrho hL hH K
  set f : ℕ → ℝ := fun k => row.haarB (k + 1) * √(((k : ℝ) + 1) * row.yk (k + 1) / (row.R : ℝ))
    with hf
  have hsum : Summable f := by
    apply (summable_nat_add_iff K).1
    refine htail.1.congr fun j => ?_
    simp only [hf]
    have e1 : K + 1 + j = j + K + 1 := by omega
    have e2 : (((K + 1 + j : ℕ) : ℝ)) = ((j + K : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [e2, e1]
  have hsplit := hsum.sum_add_tsum_nat_add K
  have e : (∑' j, f (j + K)) = ∑' j, row.haarB (K + 1 + j) *
      √(((K + 1 + j : ℕ) : ℝ) * row.yk (K + 1 + j) / (row.R : ℝ)) := by
    refine tsum_congr fun j => ?_
    simp only [hf]
    have e1 : K + 1 + j = j + K + 1 := by omega
    have e2 : (((K + 1 + j : ℕ) : ℝ)) = ((j + K : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [e2, e1]
  have hSd : row.Sd = ∑' k, f k := rfl
  rw [hSd, ← hsplit, e, sumQ_cast]
  refine add_le_add ?_ htail.2
  refine Finset.sum_le_sum fun k hk => ?_
  have hk' : k < K := Finset.mem_range.1 hk
  have := hw (k + 1) (by omega) (by omega)
  simpa only [hf, Nat.cast_add, Nat.cast_one] using this

end GMCExplicitDelta.Certificates.G3
