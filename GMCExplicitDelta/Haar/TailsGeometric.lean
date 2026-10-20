module

public import GMCExplicitDelta.Haar.TailsBounds

/-! Exact shifted geometric sums and their use in H12. -/
@[expose] public section

namespace GMCExplicitDelta.Haar

open Contract Real
open scoped BigOperators

/-- Geometric tail, indexed exactly by n = K + 1 + j. -/
theorem hasSum_geometric_tail {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (K : ℕ) (C : ℝ) :
    HasSum (fun j : ℕ => C * r ^ (K + 1 + j)) (C * r ^ (K + 1) / (1 - r)) := by
  have h := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (C * r ^ (K + 1))
  simpa only [pow_add, mul_assoc, div_eq_mul_inv] using h

/-- The arithmetico-geometric tail in H12's second estimate. -/
theorem hasSum_count_geometric_tail {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (K : ℕ) :
    HasSum (fun j : ℕ => ((K + 1 + j : ℕ) : ℝ) * r ^ (K + 1 + j))
      (r ^ (K + 1) * ((K : ℝ) + 1 - (K : ℝ) * r) / (1 - r) ^ 2) := by
  have hn : ‖r‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have h := (((hasSum_geometric_of_lt_one hr0 hr1).mul_left ((K : ℝ) + 1)).add
    (hasSum_coe_mul_geometric_of_norm_lt_one hn)).mul_left (r ^ (K + 1))
  convert h using 1
  · funext j
    push_cast
    rw [pow_add]
    ring
  · have hd : 1 - r ≠ 0 := (sub_pos.mpr hr1).ne'
    field_simp [hd]
    ring

/-- A dominated nonnegative geometric tail is summable and obeys its closed bound. -/
theorem geometric_tail_le {b : ℕ → ℝ} {C r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (K : ℕ)
    (hb0 : ∀ k, 1 ≤ k → 0 ≤ b k)
    (hb : ∀ k, 1 ≤ k → b k ≤ C * r ^ k) :
    Summable (fun j => b (K + 1 + j)) ∧
      (∑' j, b (K + 1 + j)) ≤ C * r ^ (K + 1) / (1 - r) := by
  have hg := hasSum_geometric_tail hr0 hr1 K C
  have hs : Summable (fun j => b (K + 1 + j)) := hg.summable.of_norm_bounded (by
    intro j
    rw [Real.norm_eq_abs, abs_of_nonneg (hb0 _ (by omega))]
    exact hb _ (by omega))
  refine ⟨hs, ?_⟩
  rw [← hg.tsum_eq]
  exact hs.tsum_le_tsum (fun j => hb _ (by omega)) hg.summable

/-- A dominated arithmetico-geometric tail is summable and obeys its closed bound. -/
theorem count_geometric_tail_le {b : ℕ → ℝ} {C r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (K : ℕ)
    (hb0 : ∀ k, 1 ≤ k → 0 ≤ b k)
    (hb : ∀ k, 1 ≤ k → b k ≤ C * (k : ℝ) * r ^ k) :
    Summable (fun j => b (K + 1 + j)) ∧
      (∑' j, b (K + 1 + j)) ≤
        C * r ^ (K + 1) * ((K : ℝ) + 1 - (K : ℝ) * r) / (1 - r) ^ 2 := by
  have hg := (hasSum_count_geometric_tail hr0 hr1 K).mul_left C
  have hs : Summable (fun j => b (K + 1 + j)) := hg.summable.of_norm_bounded (by
    intro j
    rw [Real.norm_eq_abs, abs_of_nonneg (hb0 _ (by omega))]
    simpa only [mul_assoc] using hb (K + 1 + j) (by omega))
  refine ⟨hs, ?_⟩
  have hle := hs.tsum_le_tsum (fun j => by
    simpa only [mul_assoc] using hb (K + 1 + j) (by omega)) hg.summable
  rw [hg.tsum_eq] at hle
  convert hle using 1
  ring

variable {d : ℕ}

theorem haarB_nonneg (row : Row d) (k : ℕ) : 0 ≤ row.haarB k := by
  unfold Row.haarB
  split <;> exact sqrt_nonneg _

/-- H12's first tail, with the coefficient hypotheses exactly as in the source. -/
theorem haarB_tail_le (row : Row d) (hq1 : 1 < row.qs) (hq9 : row.qs < 9)
    (hu3 : row.us < 3)
    (hL : ∀ k, 1 ≤ k → row.haarL k ≤ row.L1sharp * (9 / 9 ^ k))
    (hH : ∀ k, 1 ≤ k → row.haarH k ≤ row.Hsharp) (K : ℕ) :
    Summable (fun j => row.haarB (K + 1 + j)) ∧
      (∑' j, row.haarB (K + 1 + j)) ≤ row.Ks * (row.us / 3) ^ (K + 1) / (1 - row.us / 3) := by
  apply geometric_tail_le (b := row.haarB) (C := row.Ks) (div_nonneg (us_pos row).le (by norm_num))
    ((div_lt_one (by norm_num : (0 : ℝ) < 3)).2 hu3) K
    (fun k _ => haarB_nonneg row k)
  intro k hk
  exact haarB_le row hq1 hq9 k hk (hL k hk) (hH k hk)

/-- The third H12 tail is the exact contract Tg. -/
theorem Tg_le (row : Row d) (hq1 : 1 < row.qs) (hq9 : row.qs < 9)
    (hrho1 : row.rhoS < 1)
    (hL : ∀ k, 1 ≤ k → row.haarL k ≤ row.L1sharp * (9 / 9 ^ k))
    (hH : ∀ k, 1 ≤ k → row.haarH k ≤ row.Hsharp) :
    Summable (fun j => row.haarB (row.g + 1 + j) * row.us ^ (row.g + 1 + j)) ∧
      row.Tg ≤ row.Ks * row.rhoS ^ (row.g + 1) / (1 - row.rhoS) := by
  have hrho0 : 0 ≤ row.rhoS := by unfold Row.rhoS; positivity
  apply geometric_tail_le (b := fun k => row.haarB k * row.us ^ k) (C := row.Ks) hrho0 hrho1 row.g
    (fun k _ => mul_nonneg (haarB_nonneg row k) (pow_nonneg (us_pos row).le k))
  intro k hk
  calc
    row.haarB k * row.us ^ k ≤ (row.Ks * (row.us / 3) ^ k) * row.us ^ k :=
      mul_le_mul_of_nonneg_right (haarB_le row hq1 hq9 k hk (hL k hk) (hH k hk))
        (pow_nonneg (us_pos row).le k)
    _ = row.Ks * row.rhoS ^ k := by
      rw [rhoS_eq, qs_eq_us_sq]
      rw [mul_assoc, ← mul_pow]
      congr 2
      ring

/-- C6's ellipticity estimate controls the weight in H12's second tail. -/
theorem sqrt_count_yk_le (row : Row d) (hR : 1 ≤ (row.R : ℝ)) (hq : 1 ≤ row.qs)
    (k : ℕ) (hk : 1 ≤ k) :
    √((k : ℝ) * row.yk k / (row.R : ℝ)) ≤ (k : ℝ) * row.us ^ k := by
  have hR0 : 0 < (row.R : ℝ) := lt_of_lt_of_le zero_lt_one hR
  have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hy := yk_le row hR hq k
  have hy' : (k : ℝ) * row.yk k / (row.R : ℝ) ≤ (k : ℝ) * row.qs ^ k := by
    apply (div_le_iff₀ hR0).2
    nlinarith only [mul_le_mul_of_nonneg_left hy hk0]
  calc
    √((k : ℝ) * row.yk k / (row.R : ℝ)) ≤ √((k : ℝ) * row.qs ^ k) := sqrt_le_sqrt hy'
    _ = √(k : ℝ) * row.us ^ k := by
      rw [sqrt_mul hk0, qs_eq_us_sq, ← pow_mul, Nat.mul_comm 2 k, pow_mul,
        sqrt_sq (pow_nonneg (us_pos row).le k)]
    _ ≤ (k : ℝ) * row.us ^ k := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (us_pos row).le k)
      exact sqrt_le_self_iff.mpr (Or.inr (by exact_mod_cast hk))

/-- H12's second tail, as a tsum over all k > K. -/
theorem haarB_weighted_tail_le (row : Row d) (hq1 : 1 < row.qs) (hq9 : row.qs < 9)
    (hR : 1 ≤ (row.R : ℝ)) (hrho1 : row.rhoS < 1)
    (hL : ∀ k, 1 ≤ k → row.haarL k ≤ row.L1sharp * (9 / 9 ^ k))
    (hH : ∀ k, 1 ≤ k → row.haarH k ≤ row.Hsharp) (K : ℕ) :
    Summable (fun j => row.haarB (K + 1 + j) *
      √(((K + 1 + j : ℕ) : ℝ) * row.yk (K + 1 + j) / (row.R : ℝ))) ∧
      (∑' j, row.haarB (K + 1 + j) *
        √(((K + 1 + j : ℕ) : ℝ) * row.yk (K + 1 + j) / (row.R : ℝ))) ≤
      row.Ks * row.rhoS ^ (K + 1) * ((K : ℝ) + 1 - (K : ℝ) * row.rhoS) / (1 - row.rhoS) ^ 2 := by
  have hrho0 : 0 ≤ row.rhoS := by unfold Row.rhoS; positivity
  apply count_geometric_tail_le
    (b := fun k => row.haarB k * √((k : ℝ) * row.yk k / (row.R : ℝ)))
    (C := row.Ks) hrho0 hrho1 K
    (fun k _ => mul_nonneg (haarB_nonneg row k) (sqrt_nonneg _))
  intro k hk
  calc
    row.haarB k * √((k : ℝ) * row.yk k / (row.R : ℝ)) ≤
        (row.Ks * (row.us / 3) ^ k) * ((k : ℝ) * row.us ^ k) :=
      mul_le_mul (haarB_le row hq1 hq9 k hk (hL k hk) (hH k hk))
        (sqrt_count_yk_le row hR hq1.le k hk) (sqrt_nonneg _)
        (mul_nonneg (sqrt_nonneg _) (pow_nonneg (div_nonneg (us_pos row).le (by norm_num)) k))
    _ = row.Ks * (k : ℝ) * row.rhoS ^ k := by
      rw [rhoS_eq, qs_eq_us_sq]
      calc
        (row.Ks * (row.us / 3) ^ k) * ((k : ℝ) * row.us ^ k) =
          row.Ks * (k : ℝ) * ((row.us / 3) * row.us) ^ k := by rw [mul_pow]; ring
        _ = _ := by congr 2; ring

end GMCExplicitDelta.Haar
