module

public import GMCExplicitDelta.Haar.TailsMinimumSeries

/-! H12: contract Haar coefficient bounds and geometric tail estimates. -/
@[expose] public section

namespace GMCExplicitDelta.Haar

open Contract Real
open scoped BigOperators

variable {d : ℕ}

theorem qs_eq_us_sq (row : Row d) : row.qs = row.us ^ 2 := by
  unfold Row.qs Row.us
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring

theorem us_pos (row : Row d) : 0 < row.us := Real.rpow_pos_of_pos (by norm_num) _

theorem rhoS_eq (row : Row d) : row.rhoS = row.qs / 3 := by
  unfold Row.rhoS Row.qs
  rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 3), Real.rpow_one]

theorem haarL_nonneg (row : Row d) (k : ℕ) : 0 ≤ row.haarL k := by
  unfold Row.haarL Row.etaOmega
  split <;> positivity

theorem haarH_nonneg (row : Row d) (k : ℕ) : 0 ≤ row.haarH k := by
  unfold Row.haarH Row.etaOmega
  have h := haarL_nonneg row k
  positivity

theorem L1sharp_nonneg (row : Row d) : 0 ≤ row.L1sharp := by
  unfold Row.L1sharp
  split
  · norm_num
  · exact haarL_nonneg row 1

theorem Hsharp_nonneg (row : Row d) : 0 ≤ row.Hsharp := by
  unfold Row.Hsharp Row.etaOmega
  split
  · norm_num
  · have h := haarL_nonneg row 1
    positivity

/-- The split-at-k estimate underlying H12, over abstract nonnegative constants. -/
theorem haar_energy_le {q L H Ls Hs : ℝ} (hq1 : 1 < q) (hq9 : q < 9)
    (hL : 0 ≤ L) (hH : 0 ≤ H) (k : ℕ)
    (hLs : L ≤ Ls * (9 / 9 ^ k)) (hHs : H ≤ Hs) :
    L + (q - 1) * minSeries q L H ≤
      (9 * Ls + Hs * (q - 1) / (1 - q / 9)) * (q / 9) ^ k := by
  have hq0 : 0 ≤ q := le_trans zero_le_one hq1.le
  have hd : 0 < 1 - q / 9 := sub_pos.mpr
    ((div_lt_one (by norm_num : (0 : ℝ) < 9)).2 hq9)
  have hs := minSeries_le_split hq1 hq9 hL hH k
  have h1 := mul_le_mul_of_nonneg_left hs (sub_nonneg.mpr hq1.le)
  have halg : L + (q - 1) *
      (L * (q ^ k - 1) / (q - 1) + H * (q / 9) ^ k / (1 - q / 9)) =
      L * q ^ k + H * ((q - 1) / (1 - q / 9)) * (q / 9) ^ k := by
    field_simp [(sub_pos.mpr hq1).ne', hd.ne']
    ring
  have h2 : L * q ^ k ≤ 9 * Ls * (q / 9) ^ k := by
    calc
      L * q ^ k ≤ (Ls * (9 / 9 ^ k)) * q ^ k :=
        mul_le_mul_of_nonneg_right hLs (pow_nonneg hq0 k)
      _ = 9 * Ls * (q / 9) ^ k := by rw [div_pow]; ring
  have h3 : H * ((q - 1) / (1 - q / 9)) * (q / 9) ^ k ≤
      Hs * ((q - 1) / (1 - q / 9)) * (q / 9) ^ k := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hHs (div_nonneg (sub_nonneg.mpr hq1.le) hd.le))
      (pow_nonneg (by positivity) k)
  calc
    L + (q - 1) * minSeries q L H ≤ L + (q - 1) *
        (L * (q ^ k - 1) / (q - 1) + H * (q / 9) ^ k / (1 - q / 9)) :=
      by linarith only [h1]
    _ = L * q ^ k + H * ((q - 1) / (1 - q / 9)) * (q / 9) ^ k := halg
    _ ≤ 9 * Ls * (q / 9) ^ k + Hs * ((q - 1) / (1 - q / 9)) * (q / 9) ^ k :=
      add_le_add h2 h3
    _ = _ := by ring

/-- H12's coefficient bound about the exact contract definitions. -/
theorem haarB_le (row : Row d) (hq1 : 1 < row.qs) (hq9 : row.qs < 9)
    (k : ℕ) (hk : 1 ≤ k)
    (hL : row.haarL k ≤ row.L1sharp * (9 / 9 ^ k))
    (hH : row.haarH k ≤ row.Hsharp) :
    row.haarB k ≤ row.Ks * (row.us / 3) ^ k := by
  have hA : 0 ≤ 9 * row.L1sharp + row.Hsharp * (row.qs - 1) / (1 - row.qs / 9) := by
    have hL0 := L1sharp_nonneg row
    have hH0 := Hsharp_nonneg row
    have hd : 0 < 1 - row.qs / 9 := sub_pos.mpr
      ((div_lt_one (by norm_num : (0 : ℝ) < 9)).2 hq9)
    positivity
  have hr : row.qs / 9 = (row.us / 3) ^ 2 := by rw [qs_eq_us_sq]; ring
  unfold Row.haarB
  rw [ite_eq_right (by omega : k ≠ 0)]
  calc
    √(row.haarL k + (row.qs - 1) * minSeries row.qs (row.haarL k) (row.haarH k)) ≤
        √((9 * row.L1sharp + row.Hsharp * (row.qs - 1) / (1 - row.qs / 9)) *
          (row.qs / 9) ^ k) :=
      Real.sqrt_le_sqrt (haar_energy_le hq1 hq9 (haarL_nonneg row k) (haarH_nonneg row k) k hL hH)
    _ = row.Ks * (row.us / 3) ^ k := by
      rw [Real.sqrt_mul hA]
      change _ * _ = √(9 * row.L1sharp + row.Hsharp * (row.qs - 1) / (1 - row.qs / 9)) * _
      congr 1
      rw [hr, ← pow_mul, Nat.mul_comm 2 k, pow_mul,
        Real.sqrt_sq (pow_nonneg (div_nonneg (us_pos row).le (by norm_num)) k)]

/-- Ellipticity root scales sublinearly for factors at least one (C6 input to H12). -/
theorem ellipX_mul_le {θ a : ℝ} (hθ : 0 ≤ θ) (ha : 1 ≤ a) :
    ellipX (θ * a) ≤ a * ellipX θ := by
  have ha0 : 0 ≤ a := le_trans zero_le_one ha
  have hprod : θ * a * (θ * a + 2) ≤ a ^ 2 * (θ * (θ + 2)) := by
    have h := mul_nonneg (mul_nonneg hθ ha0) (sub_nonneg.mpr ha)
    nlinarith only [h]
  have hroot : √(θ * a * (θ * a + 2)) ≤ a * √(θ * (θ + 2)) := by
    calc
      √(θ * a * (θ * a + 2)) ≤ √(a ^ 2 * (θ * (θ + 2))) := sqrt_le_sqrt hprod
      _ = a * √(θ * (θ + 2)) := by rw [sqrt_mul (sq_nonneg a), sqrt_sq ha0]
  unfold ellipX
  nlinarith only [hroot, ha]

theorem ellipX_thetaR (row : Row d) (hR : 1 ≤ (row.R : ℝ)) :
    ellipX row.thetaR = (row.R : ℝ) := by
  have hR0 : 0 < (row.R : ℝ) := lt_of_lt_of_le zero_lt_one hR
  have hi : (row.R : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hR0).2 hR
  have hz : 0 ≤ ((row.R : ℝ) - (row.R : ℝ)⁻¹) / 2 := by linarith
  have hs : row.thetaR * (row.thetaR + 2) =
      (((row.R : ℝ) - (row.R : ℝ)⁻¹) / 2) ^ 2 := by
    unfold Row.thetaR
    field_simp [hR0.ne']
    ring
  unfold ellipX
  rw [hs, sqrt_sq hz]
  unfold Row.thetaR
  ring

theorem thetaR_nonneg (row : Row d) (hR : 1 ≤ (row.R : ℝ)) : 0 ≤ row.thetaR := by
  have hR0 : 0 < (row.R : ℝ) := lt_of_lt_of_le zero_lt_one hR
  have heq : row.thetaR = ((row.R : ℝ) - 1) ^ 2 / (2 * (row.R : ℝ)) := by
    unfold Row.thetaR
    field_simp [hR0.ne']
    ring
  rw [heq]
  positivity

theorem yk_le (row : Row d) (hR : 1 ≤ (row.R : ℝ)) (hq : 1 ≤ row.qs) (k : ℕ) :
    row.yk k ≤ (row.R : ℝ) * row.qs ^ k := by
  unfold Row.yk
  have h := ellipX_mul_le (thetaR_nonneg row hR) (one_le_pow₀ hq (n := k))
  rw [ellipX_thetaR row hR] at h
  simpa only [mul_comm] using h

end GMCExplicitDelta.Haar
