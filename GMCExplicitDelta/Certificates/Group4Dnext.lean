module

public import GMCExplicitDelta.Certificates.Group4Moment

/-!
# Group 4: the next cap `D_next` is `F` up to `10^{-30}`

`D_next = U_h = min{D, F + σ_d D B̄₃₂(3^{d(h-1)}, ϖ)}` and `B̄₃₂` is below `10^{-40}` for
`n = 3^{d(h-1)} ≥ 3^{520}` (`d ≥ 2`, `h ≥ 261`), so `F ≤ D_next ≤ F + 10^{-30}` whenever `F ≤ D`.
-/

@[expose] public section

open GMCExplicitDelta.Contract Real

namespace GMCExplicitDelta.Certificates.Group4

theorem assocStirling_le : ∀ k < 16, assocStirling 32 (k + 1) ≤ 10 ^ 25 := by decide +kernel

theorem Tvarpi_nonneg (D F : ℝ) (hD : 0 ≤ D) (hF : 0 ≤ F) : 0 ≤ Tvarpi D F := by
  unfold Tvarpi varpi
  exact Real.rpow_nonneg (le_min_iff.2 ⟨div_nonneg hF hD, zero_le_one⟩) _

theorem Tvarpi_le_one (D F : ℝ) (hD : 0 ≤ D) (hF : 0 ≤ F) : Tvarpi D F ≤ 1 := by
  unfold Tvarpi varpi
  exact Real.rpow_le_one (le_min_iff.2 ⟨div_nonneg hF hD, zero_le_one⟩) (min_le_right _ _)
    (by norm_num)

theorem Bbar32_nonneg' (n : ℕ) {D F : ℝ} (hD : 0 ≤ D) (hF : 0 ≤ F) : 0 ≤ Bbar32 n D F := by
  unfold Bbar32
  refine Real.rpow_nonneg (Finset.sum_nonneg fun k _ => ?_) _
  have hT := Tvarpi_nonneg D F hD hF
  positivity

theorem big_ineq : (16 : ℝ) * 10 ^ 25 / ((3 : ℝ) ^ 520) ^ 16 ≤ (1 / 10 ^ 40) ^ 32 := by
  have h : ((16 : ℚ) * 10 ^ 25 / ((3 : ℚ) ^ 520) ^ 16) ≤ (1 / 10 ^ 40) ^ 32 := by decide +kernel
  have h2 := (Rat.cast_le (K := ℝ)).2 h
  push_cast at h2
  exact h2

theorem Bbar32_le {n : ℕ} {D F : ℝ} (hD : 0 < D) (hF : 0 < F) (hn : 3 ^ 520 ≤ n) :
    Bbar32 n D F ≤ 1 / 10 ^ 40 := by
  have hT0 := Tvarpi_nonneg D F hD.le hF.le
  have hT1 := Tvarpi_le_one D F hD.le hF.le
  have hn' : ((3 ^ 520 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by
    refine le_trans ?_ hn'
    exact_mod_cast Nat.one_le_pow _ _ (by norm_num)
  have hpos : (0 : ℝ) < ((3 ^ 520 : ℕ) : ℝ) ^ 16 := by positivity
  unfold Bbar32
  refine rpow32_le (Finset.sum_nonneg fun k _ => ?_) (by positivity) ?_
  · have := hT0; positivity
  have hterm : ∀ k ∈ Finset.range 16,
      (assocStirling 32 (k + 1) : ℝ) * Tvarpi D F ^ k / (n : ℝ) ^ (31 - k) ≤
        10 ^ 25 / ((3 ^ 520 : ℕ) : ℝ) ^ 16 := by
    intro k hk
    have hk' : k < 16 := Finset.mem_range.1 hk
    have hA : (assocStirling 32 (k + 1) : ℝ) ≤ 10 ^ 25 := by
      exact_mod_cast assocStirling_le k hk'
    have hTk : Tvarpi D F ^ k ≤ 1 := pow_le_one₀ hT0 hT1
    have hnum : (assocStirling 32 (k + 1) : ℝ) * Tvarpi D F ^ k ≤ 10 ^ 25 := by
      calc _ ≤ (assocStirling 32 (k + 1) : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left hTk (Nat.cast_nonneg _)
        _ ≤ 10 ^ 25 := by simpa using hA
    have hden : ((3 ^ 520 : ℕ) : ℝ) ^ 16 ≤ (n : ℝ) ^ (31 - k) := by
      calc ((3 ^ 520 : ℕ) : ℝ) ^ 16 ≤ (n : ℝ) ^ 16 := pow_le_pow_left₀ (by positivity) hn' 16
        _ ≤ (n : ℝ) ^ (31 - k) := pow_le_pow_right₀ hn1 (by omega)
    calc _ ≤ 10 ^ 25 / (n : ℝ) ^ (31 - k) :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hpos hden
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have e : ((3 ^ 520 : ℕ) : ℝ) = (3 : ℝ) ^ 520 := by rw [Nat.cast_pow, Nat.cast_ofNat]
  rw [e, Nat.cast_ofNat, ← mul_div_assoc]
  exact big_ineq

theorem sigmaNorm_nonneg (d : ℕ) : (0 : ℝ) ≤ sigmaNorm d := by
  unfold sigmaNorm
  split_ifs <;> norm_num

theorem Dnext_le {d : ℕ} (row : Row d) {D F : ℝ} (hD : 0 < D) (hF : 0 < F) (hd : 2 ≤ d)
    (hh : 261 ≤ row.h) (hσD : (sigmaNorm d : ℝ) * D ≤ 100) :
    row.Dnext D F ≤ F + 1 / 10 ^ 30 := by
  unfold Row.Dnext nativeCap
  refine (min_le_right _ _).trans ?_
  have h260 : 260 ≤ row.h - 1 := by omega
  have h520 : 520 ≤ d * (row.h - 1) := by nlinarith
  have hn : 3 ^ 520 ≤ 3 ^ (d * (row.h - 1)) := Nat.pow_le_pow_right (by norm_num) h520
  have hB := Bbar32_le (D := D) (F := F) hD hF hn
  have hB0 := Bbar32_nonneg' (3 ^ (d * (row.h - 1))) hD.le hF.le
  have : (sigmaNorm d : ℝ) * D * Bbar32 (3 ^ (d * (row.h - 1))) D F ≤ 100 * (1 / 10 ^ 40) :=
    mul_le_mul hσD hB hB0 (by norm_num)
  have h2 : (100 : ℝ) * (1 / 10 ^ 40) ≤ 1 / 10 ^ 30 := by norm_num
  linarith

theorem Dnext_pos {d : ℕ} (row : Row d) {D F : ℝ} (hD : 0 < D) (hF : 0 < F) :
    0 < row.Dnext D F := by
  unfold Row.Dnext nativeCap
  refine lt_min hD ?_
  have hB0 := Bbar32_nonneg' (3 ^ (d * (row.h - 1))) hD.le hF.le
  have := sigmaNorm_nonneg d
  have : 0 ≤ (sigmaNorm d : ℝ) * D * Bbar32 (3 ^ (d * (row.h - 1))) D F := by positivity
  linarith

end GMCExplicitDelta.Certificates.Group4
