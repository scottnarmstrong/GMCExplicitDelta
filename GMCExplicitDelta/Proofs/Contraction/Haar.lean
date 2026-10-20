module

public import GMCExplicitDelta.Contract.Obligations
public import GMCExplicitDelta.Haar.TailsGeometric

/-! Contract-level summability and finite Haar sum bounds (H12). -/
@[expose] public section

namespace GMCExplicitDelta.Assembly

open Contract Haar Real
open scoped BigOperators

variable {d : ℕ}

/-- The source coefficient majorants, derived from the row obligations. -/
theorem haar_majorants (row : Row d) (hO : row.Obligations) :
    (1 < row.qs ∧ row.qs < 9 ∧ row.us < 3) ∧
    (∀ k, 1 ≤ k → row.haarL k ≤ row.L1sharp * (9 / 9 ^ k)) ∧
    (∀ k, 1 ≤ k → row.haarH k ≤ row.Hsharp) := by
  have hs0 : 0 < (row.s : ℝ) := by exact_mod_cast hO.par1.2.2.2.2.2.1
  have hs1 : (row.s : ℝ) < 1 / 2 := by
    have hs : 2 * row.s < 1 := by linarith only [hO.par1.2.2.2.2.2.2.1]
    have hsR : 2 * (row.s : ℝ) < 1 := by exact_mod_cast hs
    linarith only [hsR]
  have hq1 : 1 < row.qs := one_lt_rpow (by norm_num) (by linarith only [hs0])
  have hq3 : row.qs < 3 := by
    simpa only [Row.qs, rpow_one] using
      rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 3) (show 2 * (row.s : ℝ) < 1 by linarith only [hs1])
  have hu3 : row.us < 3 := by
    simpa only [Row.us, rpow_one] using
      rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 3) (show (row.s : ℝ) < 1 by linarith only [hs1])
  refine ⟨⟨hq1, hq3.trans (by norm_num), hu3⟩, ?_, ?_⟩
  · intro k hk
    by_cases hd : d = 2
    · simpa only [Row.L1sharp, ite_eq_left hd, one_mul] using (hO.geo2.1 hd).2.2.2 k hk |>.1
    · have hfirst : row.haarL 1 = row.etaOmega * (5 * π ^ 2 / 54) := by
        simp only [Row.haarL, hd, false_and, ite_false, pow_one, div_self (by norm_num : (9 : ℝ) ≠ 0), mul_one]
      rw [Row.L1sharp, ite_eq_right hd, hfirst, Row.haarL, ite_eq_right (by simp only [hd, false_and, not_false_eq_true])]
  · intro k hk
    by_cases hd : d = 2
    · have heta : row.etaOmega = 1 := by norm_num [Row.etaOmega, Row.omegaEff, hd]
      simpa only [Row.haarH, heta, hd, Nat.cast_ofNat, one_mul, Row.Hsharp, ite_true] using
        ((hO.geo2.1 hd).2.2.2 k hk).2
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
      exact mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg d)) 1) he

/-- Finite tail sums are bounded by the corresponding convergent shifted series. -/
theorem finite_tail_le {b : ℕ → ℝ} (hb : ∀ k, 0 ≤ b k) (K N : ℕ)
    (hs : Summable (fun j => b (K + 1 + j))) :
    ∑ k ∈ Finset.Ioc K N, b k ≤ ∑' j, b (K + 1 + j) := by
  have heq : Finset.Ioc K N = Finset.Ico (K + 1) (N + 1) := by ext k; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
  rw [heq, Finset.sum_Ico_eq_sum_range]
  exact hs.sum_le_tsum _ (fun _ _ => hb _)

theorem haarB_sums_proof (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations) :
    (∀ k, 0 ≤ row.haarB k) ∧
      (∀ N, ∑ k ∈ Finset.range N, row.haarB k ≤ row.Sb) ∧
      (∀ N, ∑ k ∈ Finset.Ioc row.Kprime N, row.haarB k ≤ row.Btail) ∧
      (∀ N, ∑ k ∈ Finset.Icc 1 N,
          row.haarB k * Real.sqrt ((k : ℝ) * row.yk k / (row.R : ℝ)) ≤ row.Sd) ∧
      row.Tg ≤ row.Ks * row.rhoS ^ (row.g + 1) / (1 - row.rhoS) := by
  have _hd := hd
  obtain ⟨⟨hq1, hq9, hu3⟩, hL, hH⟩ := haar_majorants row hO
  have hb := haarB_nonneg row
  have htail := haarB_tail_le row hq1 hq9 hu3 hL hH
  have hsum : Summable row.haarB := by
    apply (summable_nat_add_iff 1).1
    simpa only [zero_add, Nat.add_comm 1] using (htail 0).1
  have hR : 1 ≤ (row.R : ℝ) := by exact_mod_cast hO.par2.1.le
  have hw := haarB_weighted_tail_le row hq1 hq9 hR hO.geo2.2 hL hH 0
  refine ⟨hb, (fun N => hsum.sum_le_tsum _ (fun k _ => hb k)), ?_, ?_,
    (Tg_le row hq1 hq9 hO.geo2.2 hL hH).2⟩
  · intro N
    exact (finite_tail_le hb row.Kprime N (htail row.Kprime).1).trans (htail row.Kprime).2
  · intro N
    have h := finite_tail_le (b := fun k => row.haarB k * √((k : ℝ) * row.yk k / (row.R : ℝ)))
      (fun k => mul_nonneg (hb k) (sqrt_nonneg _)) 0 N (by
        simpa only [Nat.cast_add, Nat.cast_one, zero_add] using hw.1)
    have heq : Finset.Ioc 0 N = Finset.Icc 1 N := by ext k; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
    simpa only [heq, Nat.zero_add, Row.Sd, Nat.cast_add, Nat.cast_one, Nat.add_comm 1, add_comm 1] using h

end GMCExplicitDelta.Assembly
