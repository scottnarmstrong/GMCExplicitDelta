module

public import GMCExplicitDelta.Certificates.Group4Band

/-!
# The fixed-point matrix `bandUp` and its soundness

`Dom_bandUp`: every entry of the exact matrix `bandMatrix δ` lies in `[0, bandUp S dp dq / S]`
whenever `δ² = dp/dq`, `z_b < J + 4` and the explicit tail bound is `≤ 1/S`.
-/

@[expose] public section

open Matrix GMCNumerics GMCExplicitDelta.Contract

namespace GMCExplicitDelta.Certificates.Group4

/-- `S · 2𝐋` as a list matrix: diagonal `i²`, subdiagonal `i(2i-1)`. -/
def genL2 (S : ℕ) : List (List ℕ) :=
  (List.range 33).map fun i => (List.range 33).map fun j =>
    if j = i then S * (i * i) else if j + 1 = i then S * (i * (2 * i - 1)) else 0

/-- `𝖺s𝐋` rounded up (`s = δ² = dp/dq`). -/
def bandMs (S dp dq : ℕ) : List (List ℕ) :=
  scaleUp (1072331 * dp) (2 * 100000000 * dq) (genL2 S)

/-- `𝗎s𝐋` rounded up. -/
def bandUs (S dp dq : ℕ) : List (List ℕ) :=
  scaleUp (1812431 * dp) (2 * 500000000 * dq) (genL2 S)

/-- `(𝖺s𝐋)²/2` rounded up. -/
def bandT2 (S dp dq : ℕ) : List (List ℕ) :=
  scaleUp 1 2 (mulUp S 33 (bandMs S dp dq) (bandMs S dp dq))

/-- `I + 𝗎s𝐋 + c₂T₂ + c₃Σ + 1/S` from `T₂` and the series sum `acc`. -/
def bandFinish (S dp dq : ℕ) (T2 acc : List (List ℕ)) : List (List ℕ) :=
  addOne (addM (addM (addM (identUp S 33) (bandUs S dp dq)) (scaleUp 244017 250000 T2))
    (scaleUp 303489 500000 acc))

/-- The series sum `Σ_{n=3}^{J+2} (𝖺s𝐋)^n/n!` rounded up. -/
def bandSum (S dp dq J : ℕ) : List (List ℕ) :=
  (serAux S 33 (bandMs S dp dq) J 2 (bandT2 S dp dq) (zeroM 33)).2

/-- The fixed-point band matrix (`s = δ² = dp/dq`, series truncated after `J + 2` terms). -/
def bandUp (S dp dq J : ℕ) : List (List ℕ) :=
  bandFinish S dp dq (bandT2 S dp dq) (bandSum S dp dq J)

theorem bandSum_of_stages {S dp dq J1 J2 : ℕ} {T1 acc1 acc2 : List (List ℕ)}
    (h1 : serAux S 33 (bandMs S dp dq) J1 2 (bandT2 S dp dq) (zeroM 33) = (T1, acc1))
    (h2 : (serAux S 33 (bandMs S dp dq) J2 (2 + J1) T1 acc1).2 = acc2) :
    bandSum S dp dq (J1 + J2) = acc2 := by
  unfold bandSum
  rw [serAux_add, h1]
  exact h2

theorem WF_genL2 (S : ℕ) : WF 33 (genL2 S) := by
  refine ⟨by simp [genL2], ?_⟩
  intro r hr
  simp only [genL2, List.mem_map] at hr
  obtain ⟨a, -, rfl⟩ := hr
  simp

theorem getE_genL2 (S : ℕ) {i j : ℕ} (hi : i < 33) (hj : j < 33) :
    getE (genL2 S) i j =
      if j = i then S * (i * i) else if j + 1 = i then S * (i * (2 * i - 1)) else 0 := by
  simp [getE, genL2, List.getD_eq_getElem?_getD, hi, hj]

theorem Dom_genL2 {S : ℕ} (hS : 0 < S) :
    Dom S 33 ((2 : ℝ) • generatorMatrix) (genL2 S) := by
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  have key : ∀ i j : Fin 33, (2 : ℝ) * generatorMatrix i j = toReal S 33 (genL2 S) i j := by
    intro i j
    rw [generatorMatrix_entry]
    simp only [toReal, getE_genL2 S i.2 j.2]
    by_cases h1 : (j : ℕ) = i
    · have h2 : ¬ ((j : ℕ) + 1 = i) := by omega
      simp only [if_pos h1, if_neg h2, add_zero]
      push_cast
      field_simp
    · by_cases h2 : (j : ℕ) + 1 = i
      · have h3 : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) + 1 := by exact_mod_cast h2.symm
        have h4 : 2 * (i : ℕ) - 1 = 2 * (j : ℕ) + 1 := by omega
        simp only [if_neg h1, if_pos h2, zero_add]
        rw [h4]
        push_cast
        rw [h3]
        field_simp
        ring
      · simp only [if_neg h1, if_neg h2]; simp
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · simp only [Matrix.smul_apply, smul_eq_mul]
    exact mul_nonneg (by norm_num) (generatorMatrix_nonneg i j)
  · simp only [Matrix.smul_apply, smul_eq_mul]
    exact (key i j).le

theorem Dom_bandUp {S dp dq J : ℕ} (hS : 0 < S) (hdp : 0 < dp) (hdq : 0 < dq) {δ : ℝ}
    (hδ : δ ^ 2 = (dp : ℝ) / dq)
    (hz : 1520 * (proxyA : ℝ) * δ ^ 2 < (((J + 3 : ℕ) : ℝ) + 1))
    (htail : (ratioC3 : ℝ) * ((1520 * (proxyA : ℝ) * δ ^ 2) ^ (J + 3) / ((J + 3 : ℕ).factorial : ℝ) /
      (1 - (1520 * (proxyA : ℝ) * δ ^ 2) / (((J + 3 : ℕ) : ℝ) + 1))) ≤ 1 / (S : ℝ)) :
    Dom S 33 (bandMatrix δ) (bandUp S dp dq J) := by
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  have hdq' : (0 : ℝ) < dq := by exact_mod_cast hdq
  have hdp' : (0 : ℝ) < dp := by exact_mod_cast hdp
  have ha : (proxyA : ℝ) = 1072331 / 100000000 := by norm_num [proxyA]
  have hu : (varU : ℝ) = 1812431 / 500000000 := by norm_num [varU]
  have hc2 : (ratioC2 : ℝ) = ((244017 : ℕ) : ℝ) / ((250000 : ℕ) : ℝ) := by norm_num [ratioC2]
  have hc3 : (ratioC3 : ℝ) = ((303489 : ℕ) : ℝ) / ((500000 : ℕ) : ℝ) := by norm_num [ratioC3]
  have hδ2 : 0 ≤ δ ^ 2 := sq_nonneg δ
  have hap : 0 ≤ (proxyA : ℝ) * δ ^ 2 := by rw [ha]; positivity
  set z : ℝ := 1520 * (proxyA : ℝ) * δ ^ 2 with hzdef
  have hz0 : 0 ≤ z := by rw [hzdef]; nlinarith
  set Mr : Matrix (Fin 33) (Fin 33) ℝ := ((proxyA : ℝ) * δ ^ 2) • generatorMatrix with hMr
  have hMr0 : ∀ i j, 0 ≤ Mr i j := fun i j => by
    simp only [hMr, Matrix.smul_apply, smul_eq_mul]
    exact mul_nonneg hap (generatorMatrix_nonneg i j)
  have hMrRow : RowLe z Mr := by
    intro i
    simp only [hMr, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    calc _ ≤ (proxyA : ℝ) * δ ^ 2 * 1520 :=
          mul_le_mul_of_nonneg_left (generatorMatrix_rowsum i) hap
      _ = z := by rw [hzdef]; ring
  -- fixed-point data
  have hWFL := WF_genL2 S
  have hWFMs : WF 33 (scaleUp (1072331 * dp) (2 * 100000000 * dq) (genL2 S)) :=
    WF_scaleUp _ _ hWFL
  have hMd : Dom S 33 Mr (scaleUp (1072331 * dp) (2 * 100000000 * dq) (genL2 S)) := by
    have := Dom_scaleUp (p := 1072331 * dp) (q := 2 * 100000000 * dq) hS (by positivity)
      (Dom_genL2 hS)
    have e : Mr = (((1072331 * dp : ℕ) : ℝ) / ((2 * 100000000 * dq : ℕ) : ℝ)) •
        ((2 : ℝ) • generatorMatrix) := by
      rw [hMr, smul_smul, ha, hδ]; push_cast; congr 1; field_simp; ring
    rw [e]; exact this
  have hUd : Dom S 33 (((varU : ℝ) * δ ^ 2) • generatorMatrix)
      (scaleUp (1812431 * dp) (2 * 500000000 * dq) (genL2 S)) := by
    have := Dom_scaleUp (p := 1812431 * dp) (q := 2 * 500000000 * dq) hS (by positivity)
      (Dom_genL2 hS)
    have e : ((varU : ℝ) * δ ^ 2) • generatorMatrix =
        (((1812431 * dp : ℕ) : ℝ) / ((2 * 500000000 * dq : ℕ) : ℝ)) •
        ((2 : ℝ) • generatorMatrix) := by
      rw [smul_smul, hu, hδ]; push_cast; congr 1; field_simp; ring
    rw [e]; exact this
  set Ms := scaleUp (1072331 * dp) (2 * 100000000 * dq) (genL2 S) with hMs
  have hM2 : Dom S 33 (Mr * Mr) (mulUp S 33 Ms Ms) := Dom_mul hS hWFMs hWFMs hMd hMd
  have hT2 : Dom S 33 (((Nat.factorial 2 : ℕ) : ℝ)⁻¹ • Mr ^ 2)
      (scaleUp 1 2 (mulUp S 33 Ms Ms)) := by
    have := Dom_scaleUp (p := 1) (q := 2) hS (by norm_num) hM2
    have e : (((1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) • (Mr * Mr) = (((Nat.factorial 2 : ℕ) : ℝ))⁻¹ • Mr ^ 2 := by
      rw [pow_two]; congr 1; norm_num [Nat.factorial]
    rw [e] at this; exact this
  set T2 := scaleUp 1 2 (mulUp S 33 Ms Ms) with hT2def
  have hWFT2 : WF 33 T2 := WF_scaleUp _ _ (WF_mulUp hWFMs)
  have hser := Dom_serAux hS hWFMs hMd J 2 T2 (zeroM 33) hWFT2 (WF_zeroM 33) hT2 0
    (Dom_zeroM hS)
  have hWFacc := (WF_serAux (S := S) hWFMs J 2 T2 (zeroM 33) hWFT2 (WF_zeroM 33)).2
  set acc := (serAux S 33 Ms J 2 T2 (zeroM 33)).2 with hacc
  have hacc' := hser.2
  -- the truncated real matrix
  have hd1 := Dom_addM hS (Dom_one hS) hUd
  have hd2 := Dom_addM hS hd1 (Dom_scaleUp (p := 244017) (q := 250000) hS (by norm_num) hT2)
  have hd3 := Dom_addM hS hd2 (Dom_scaleUp (p := 303489) (q := 500000) hS (by norm_num) hacc')
  have hWF3 : WF 33 (addM (addM (addM (identUp S 33) (scaleUp (1812431 * dp) (2 * 500000000 * dq)
      (genL2 S))) (scaleUp 244017 250000 T2)) (scaleUp 303489 500000 acc)) :=
    WF_addM (WF_addM (WF_addM (WF_identUp S 33) (WF_scaleUp _ _ hWFL)) (WF_scaleUp _ _ hWFT2))
      (WF_scaleUp _ _ hWFacc)
  have hd4 := Dom_addOne hS hWF3 hd3
  have hbU : bandUp S dp dq J = addOne (addM (addM (addM (identUp S 33) (scaleUp (1812431 * dp)
      (2 * 500000000 * dq) (genL2 S))) (scaleUp 244017 250000 T2)) (scaleUp 303489 500000 acc)) :=
    rfl
  rw [hbU]
  -- entrywise facts about the exact matrix
  have hf0 : ∀ i j (n : ℕ), 0 ≤ (Mr ^ (n + 3)) i j / ((n + 3).factorial : ℝ) := fun i j n =>
    div_nonneg ((rowLe_pow hMr0 hz0 hMrRow (n + 3)).1 i j) (by positivity)
  have hfle : ∀ i j (n : ℕ), (Mr ^ (n + 3)) i j / ((n + 3).factorial : ℝ) ≤
      z ^ (n + 3) / ((n + 3).factorial : ℝ) := fun i j n =>
    div_le_div_of_nonneg_right (entry_le_pow hMr0 hz0 hMrRow (n + 3) i j) (by positivity)
  have hsum : ∀ i j, Summable (fun n : ℕ => (Mr ^ (n + 3)) i j / ((n + 3).factorial : ℝ)) :=
    fun i j => Summable.of_nonneg_of_le (hf0 i j) (hfle i j)
      ((summable_nat_add_iff 3).2 (Real.summable_pow_div_factorial z))
  have hbm : ∀ i j, bandMatrix δ i j =
      ((1 : Matrix (Fin 33) (Fin 33) ℝ) + ((varU : ℝ) * δ ^ 2) • generatorMatrix +
        ((ratioC2 : ℝ) / 2) • Mr ^ 2) i j +
      (ratioC3 : ℝ) * ∑' n : ℕ, (Mr ^ (n + 3)) i j / ((n + 3).factorial : ℝ) := fun i j => rfl
  have hc3nn : (0 : ℝ) ≤ ratioC3 := by rw [hc3]; norm_num
  have hhead : ∀ i j, 0 ≤ ((1 : Matrix (Fin 33) (Fin 33) ℝ) + ((varU : ℝ) * δ ^ 2) • generatorMatrix +
        ((ratioC2 : ℝ) / 2) • Mr ^ 2) i j := fun i j => by
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    have h1 : 0 ≤ (1 : Matrix (Fin 33) (Fin 33) ℝ) i j := by
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
    have h2 : 0 ≤ (varU : ℝ) * δ ^ 2 * generatorMatrix i j := by
      refine mul_nonneg (mul_nonneg (by rw [hu]; norm_num) hδ2) (generatorMatrix_nonneg i j)
    have h3 : 0 ≤ (ratioC2 : ℝ) / 2 * (Mr ^ 2) i j :=
      mul_nonneg (by rw [hc2]; norm_num) ((rowLe_pow hMr0 hz0 hMrRow 2).1 i j)
    linarith
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [hbm]
    exact add_nonneg (hhead i j) (mul_nonneg hc3nn (tsum_nonneg (hf0 i j)))
  · refine le_trans ?_ (hd4.2 i j)
    rw [hbm]
    have hsp := (hsum i j).sum_add_tsum_nat_add J
    have htl : ∑' m : ℕ, (Mr ^ (m + J + 3)) i j / ((m + J + 3).factorial : ℝ) ≤
        z ^ (J + 3) / ((J + 3 : ℕ).factorial : ℝ) / (1 - z / (((J + 3 : ℕ) : ℝ) + 1)) := by
      refine le_trans (((summable_nat_add_iff J).2 (hsum i j)).tsum_le_tsum
        (g := fun m : ℕ => z ^ (m + (J + 3)) / (((m + (J + 3)).factorial : ℕ) : ℝ)) (fun m => ?_)
        (tail_summable (J + 3) z)) (tail_le (J + 3) hz0 hz)
      have e : m + J + 3 = m + (J + 3) := by omega
      have := hfle i j (m + J)
      simp only [e] at this ⊢
      exact this
    have hT : (ratioC3 : ℝ) * ∑' m : ℕ, (Mr ^ (m + J + 3)) i j / ((m + J + 3).factorial : ℝ)
        ≤ 1 / (S : ℝ) :=
      (mul_le_mul_of_nonneg_left htl hc3nn).trans htail
    have hSum : ∑ k ∈ Finset.range J, (((2 + 1 + k).factorial : ℕ) : ℝ)⁻¹ * (Mr ^ (2 + 1 + k)) i j =
        ∑ n ∈ Finset.range J, (Mr ^ (n + 3)) i j / ((n + 3).factorial : ℝ) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [show 2 + 1 + k = k + 3 by omega, inv_mul_eq_div]
    rw [← hsp]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, Matrix.sum_apply,
      zero_add]
    have h2f : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num [Nat.factorial]
    rw [h2f, hSum]
    rw [hc2, hc3] at *
    rw [mul_add]
    linarith [hT]

end GMCExplicitDelta.Certificates.Group4
