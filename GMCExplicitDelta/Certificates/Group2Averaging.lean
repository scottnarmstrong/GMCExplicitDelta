module

public import GMCExplicitDelta.Contract.DerivedAveraging
public import GMCExplicitDelta.Numerics.Enclosures
public import Mathlib.Algebra.BigOperators.Field

/-!
# Numeric obligations, group 2: averaging constants

Generic bounds on `B̄₃₂(n, ϖ)` and the native cuts `𝔲_ℓ`, used by O.avg.5 and O.bad.2:
`Xsum T n = ∑_k 𝒜(32,k+1) T^k / n^{31-k}` is the radicand of `B̄₃₂`; it is monotone in `T`, bounded
crudely by `10^26/n^16` for `T ≤ 1`, and scales by `r^32` when `n` is multiplied by `m` with
`r²m ≥ 1`.
-/

@[expose] public section

open Real

namespace GMCExplicitDelta.Certificates

open GMCExplicitDelta.Contract

theorem root_le {a r : ℝ} {n : ℕ} (hn : n ≠ 0) (ha : 0 ≤ a) (hr : 0 ≤ r) (h : a ≤ r ^ n) :
    a ^ ((1 : ℝ) / n) ≤ r := by
  rw [one_div]
  calc a ^ ((n : ℝ)⁻¹) ≤ (r ^ n) ^ ((n : ℝ)⁻¹) := Real.rpow_le_rpow ha h (by positivity)
    _ = r := Real.pow_rpow_inv_natCast hr hn

/-- The radicand of `B̄₃₂`. -/
noncomputable def Xsum (T : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range 16, (assocStirling 32 (k + 1) : ℝ) * T ^ k / (n : ℝ) ^ (31 - k)


/-- The radicand of `B̄₃₂`, with the values `𝒜(32, k)` inserted. -/
theorem Xsum_eq (T : ℝ) (n : ℕ) : Xsum T n =
    (1 : ℝ) * T ^ 0 / (n : ℝ) ^ 31 +
    (2147483615 : ℝ) * T ^ 1 / (n : ℝ) ^ 30 +
    (308800190920486 : ℝ) * T ^ 2 / (n : ℝ) ^ 29 +
    (765011543314355365 : ℝ) * T ^ 3 / (n : ℝ) ^ 28 +
    (187128474745367109190 : ℝ) * T ^ 4 / (n : ℝ) ^ 27 +
    (9648191836041940120446 : ℝ) * T ^ 5 / (n : ℝ) ^ 26 +
    (154227582326730813420156 : ℝ) * T ^ 6 / (n : ℝ) ^ 25 +
    (948856977801169301069205 : ℝ) * T ^ 7 / (n : ℝ) ^ 24 +
    (2550133124516049612389850 : ℝ) * T ^ 8 / (n : ℝ) ^ 23 +
    (3217076814220214136741550 : ℝ) * T ^ 9 / (n : ℝ) ^ 22 +
    (1967326750353779714399500 : ℝ) * T ^ 10 / (n : ℝ) ^ 21 +
    (581105308935958505448750 : ℝ) * T ^ 11 / (n : ℝ) ^ 20 +
    (79198178493972888850500 : ℝ) * T ^ 12 / (n : ℝ) ^ 19 +
    (4449180413533177822500 : ℝ) * T ^ 13 / (n : ℝ) ^ 18 +
    (79318164037837725000 : ℝ) * T ^ 14 / (n : ℝ) ^ 17 +
    (191898783962510625 : ℝ) * T ^ 15 / (n : ℝ) ^ 16 := by
  have h0 : assocStirling 32 1 = 1 := by decide +kernel
  have h1 : assocStirling 32 2 = 2147483615 := by decide +kernel
  have h2 : assocStirling 32 3 = 308800190920486 := by decide +kernel
  have h3 : assocStirling 32 4 = 765011543314355365 := by decide +kernel
  have h4 : assocStirling 32 5 = 187128474745367109190 := by decide +kernel
  have h5 : assocStirling 32 6 = 9648191836041940120446 := by decide +kernel
  have h6 : assocStirling 32 7 = 154227582326730813420156 := by decide +kernel
  have h7 : assocStirling 32 8 = 948856977801169301069205 := by decide +kernel
  have h8 : assocStirling 32 9 = 2550133124516049612389850 := by decide +kernel
  have h9 : assocStirling 32 10 = 3217076814220214136741550 := by decide +kernel
  have h10 : assocStirling 32 11 = 1967326750353779714399500 := by decide +kernel
  have h11 : assocStirling 32 12 = 581105308935958505448750 := by decide +kernel
  have h12 : assocStirling 32 13 = 79198178493972888850500 := by decide +kernel
  have h13 : assocStirling 32 14 = 4449180413533177822500 := by decide +kernel
  have h14 : assocStirling 32 15 = 79318164037837725000 := by decide +kernel
  have h15 : assocStirling 32 16 = 191898783962510625 := by decide +kernel
  unfold Xsum
  simp [Finset.sum_range_succ, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]

theorem Bbar32_eq (n : ℕ) (D F : ℝ) : Bbar32 n D F = Xsum (Tvarpi D F) n ^ ((1 : ℝ) / 32) := rfl

theorem Xsum_nonneg {T : ℝ} (hT : 0 ≤ T) (n : ℕ) : 0 ≤ Xsum T n := by
  unfold Xsum
  exact Finset.sum_nonneg fun k _ => by positivity

theorem Xsum_mono {T T' : ℝ} (hT : 0 ≤ T) (hTT : T ≤ T') (n : ℕ) : Xsum T n ≤ Xsum T' n := by
  unfold Xsum
  refine Finset.sum_le_sum fun k _ => ?_
  gcongr

theorem Tvarpi_nonneg (D F : ℝ) (hD : 0 < D) (hF : 0 ≤ F) : 0 ≤ Tvarpi D F := by
  unfold Tvarpi varpi
  exact Real.rpow_nonneg (le_min (div_nonneg hF hD.le) zero_le_one) _

theorem Tvarpi_le_one (D F : ℝ) (hD : 0 < D) (hF : 0 ≤ F) : Tvarpi D F ≤ 1 := by
  unfold Tvarpi varpi
  exact Real.rpow_le_one (le_min (div_nonneg hF hD.le) zero_le_one) (min_le_right _ _)
    (by norm_num)

theorem Tvarpi_le (D F Tp : ℝ) (hD : 0 < D) (hF : 0 ≤ F) (hFD : F ≤ D) (hTp : 0 ≤ Tp)
    (h : (F / D) ^ 32 ≤ Tp ^ 31) : Tvarpi D F ≤ Tp := by
  have hv : varpi D F = F / D := by
    unfold varpi; exact min_eq_left ((div_le_one hD).2 hFD)
  have hFD0 : 0 ≤ F / D := div_nonneg hF hD.le
  have h31 : (Tvarpi D F) ^ 31 = (F / D) ^ 32 := by
    unfold Tvarpi
    rw [hv, ← Real.rpow_natCast, ← Real.rpow_mul hFD0]
    norm_num
  have hT0 := Tvarpi_nonneg D F hD hF
  exact (pow_le_pow_iff_left₀ hT0 hTp (by norm_num : (31 : ℕ) ≠ 0)).1 (by rw [h31]; exact h)

theorem Bbar32_nonneg' (n : ℕ) {D F : ℝ} (hD : 0 < D) (hF : 0 ≤ F) : 0 ≤ Bbar32 n D F := by
  rw [Bbar32_eq]
  exact Real.rpow_nonneg (Xsum_nonneg (Tvarpi_nonneg D F hD hF) n) _

/-- `B̄₃₂(n, ϖ) ≤ r` from a rational `T_+` with `T_+^{31} ≥ (F/D)^{32}` (O.avg.3). -/
theorem Bbar32_le {n : ℕ} {D F Tp r : ℝ} (hD : 0 < D) (hF : 0 ≤ F) (hFD : F ≤ D) (hTp : 0 ≤ Tp)
    (hT : (F / D) ^ 32 ≤ Tp ^ 31) (hr : 0 ≤ r) (hX : Xsum Tp n ≤ r ^ 32) :
    Bbar32 n D F ≤ r := by
  rw [Bbar32_eq]
  have hT0 := Tvarpi_nonneg D F hD hF
  have := root_le (n := 32) (by norm_num) (Xsum_nonneg hT0 n) hr
    ((Xsum_mono hT0 (Tvarpi_le D F Tp hD hF hFD hTp hT) n).trans hX)
  simpa using this

theorem stirling_sum_le : (∑ k ∈ Finset.range 16, assocStirling 32 (k + 1)) ≤ 10 ^ 26 := by
  decide +kernel

theorem Xsum_crude {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    Xsum T n ≤ 10 ^ 26 / (n : ℝ) ^ 16 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) ^ 16 := by positivity
  calc Xsum T n ≤ ∑ k ∈ Finset.range 16, (assocStirling 32 (k + 1) : ℝ) / (n : ℝ) ^ 16 := by
        unfold Xsum
        refine Finset.sum_le_sum fun k hk => ?_
        have hk' : k < 16 := Finset.mem_range.1 hk
        have h1 : T ^ k ≤ 1 := pow_le_one₀ hT0 hT1
        have h2 : (n : ℝ) ^ 16 ≤ (n : ℝ) ^ (31 - k) := pow_le_pow_right₀ hn' (by omega)
        have hA : (0 : ℝ) ≤ assocStirling 32 (k + 1) := Nat.cast_nonneg _
        calc (assocStirling 32 (k + 1) : ℝ) * T ^ k / (n : ℝ) ^ (31 - k)
            ≤ (assocStirling 32 (k + 1) : ℝ) * 1 / (n : ℝ) ^ (31 - k) := by gcongr
          _ ≤ (assocStirling 32 (k + 1) : ℝ) / (n : ℝ) ^ 16 := by
              rw [mul_one]; gcongr
    _ = (∑ k ∈ Finset.range 16, (assocStirling 32 (k + 1) : ℝ)) / (n : ℝ) ^ 16 := by
        rw [Finset.sum_div]
    _ ≤ 10 ^ 26 / (n : ℝ) ^ 16 := by
        gcongr
        exact_mod_cast stirling_sum_le

/-- Crude bound `B̄₃₂(n) ≤ r` when `10^26 ≤ r^32 n^16`. -/
theorem Bbar32_crude {n : ℕ} {D F r : ℝ} (hD : 0 < D) (hF : 0 ≤ F) (hn : 1 ≤ n) (hr : 0 ≤ r)
    (h : 10 ^ 26 ≤ r ^ 32 * (n : ℝ) ^ 16) : Bbar32 n D F ≤ r := by
  rw [Bbar32_eq]
  have hn' : (0 : ℝ) < (n : ℝ) ^ 16 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hT0 := Tvarpi_nonneg D F hD hF
  have := root_le (n := 32) (by norm_num) (Xsum_nonneg hT0 n) hr
    ((Xsum_crude hT0 (Tvarpi_le_one D F hD hF) hn).trans (by rw [div_le_iff₀ hn']; exact h))
  simpa using this

theorem Xsum_scale {T : ℝ} (hT0 : 0 ≤ T) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) {r : ℝ}
    (h : 1 ≤ r ^ 2 * m) : Xsum T (m * n) ≤ r ^ 32 * Xsum T n := by
  unfold Xsum
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k hk => ?_
  have hk' : k < 16 := Finset.mem_range.1 hk
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have key : 1 ≤ r ^ 32 * (m : ℝ) ^ (31 - k) := by
    calc (1 : ℝ) ≤ (r ^ 2 * m) ^ 16 := one_le_pow₀ h
      _ = r ^ 32 * (m : ℝ) ^ 16 := by ring
      _ ≤ r ^ 32 * (m : ℝ) ^ (31 - k) := by
          gcongr
          omega
  have hmpos : (0 : ℝ) < (m : ℝ) ^ (31 - k) := by positivity
  have hnpos : (0 : ℝ) < (n : ℝ) ^ (31 - k) := by positivity
  have hX : 0 ≤ (assocStirling 32 (k + 1) : ℝ) * T ^ k / (n : ℝ) ^ (31 - k) := by positivity
  have e : (assocStirling 32 (k + 1) : ℝ) * T ^ k / ((m * n : ℕ) : ℝ) ^ (31 - k) =
      ((assocStirling 32 (k + 1) : ℝ) * T ^ k / (n : ℝ) ^ (31 - k)) / (m : ℝ) ^ (31 - k) := by
    push_cast
    rw [mul_pow]
    field_simp
  rw [e, div_le_iff₀ hmpos]
  calc _ = _ * 1 := (mul_one _).symm
    _ ≤ _ * (r ^ 32 * (m : ℝ) ^ (31 - k)) := mul_le_mul_of_nonneg_left key hX
    _ = _ := by ring

theorem Bbar32_scale {m n : ℕ} {D F r : ℝ} (hD : 0 < D) (hF : 0 ≤ F) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hr : 0 ≤ r) (h : 1 ≤ r ^ 2 * m) : Bbar32 (m * n) D F ≤ r * Bbar32 n D F := by
  rw [Bbar32_eq, Bbar32_eq]
  have hT0 := Tvarpi_nonneg D F hD hF
  have hX0 := Xsum_nonneg hT0 n
  calc Xsum (Tvarpi D F) (m * n) ^ ((1 : ℝ) / 32)
      ≤ (r ^ 32 * Xsum (Tvarpi D F) n) ^ ((1 : ℝ) / 32) :=
        Real.rpow_le_rpow (Xsum_nonneg hT0 _) (Xsum_scale hT0 hm hn h) (by norm_num)
    _ = r * Xsum (Tvarpi D F) n ^ ((1 : ℝ) / 32) := by
        rw [Real.mul_rpow (by positivity) hX0]
        congr 1
        rw [one_div]
        exact_mod_cast Real.pow_rpow_inv_natCast hr (by norm_num : (32 : ℕ) ≠ 0)

theorem Bbar32_scale_iter {m n : ℕ} {D F r : ℝ} (hD : 0 < D) (hF : 0 ≤ F) (hm : 1 ≤ m)
    (hn : 1 ≤ n) (hr : 0 ≤ r) (h : 1 ≤ r ^ 2 * m) (j : ℕ) :
    Bbar32 (m ^ j * n) D F ≤ r ^ j * Bbar32 n D F := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hmj : 1 ≤ m ^ j * n := Nat.mul_pos (pow_pos hm _) hn
    have e : m ^ (j + 1) * n = m * (m ^ j * n) := by ring
    rw [e]
    calc Bbar32 (m * (m ^ j * n)) D F ≤ r * Bbar32 (m ^ j * n) D F :=
          Bbar32_scale hD hF hm hmj hr h
      _ ≤ r * (r ^ j * Bbar32 n D F) := by gcongr
      _ = r ^ (j + 1) * Bbar32 n D F := by ring

/-! ### The native cuts -/

theorem sigmaNorm_nonneg (d : ℕ) : (0 : ℝ) ≤ (sigmaNorm d : ℝ) := by
  unfold sigmaNorm
  split_ifs <;> norm_num

theorem frakU_le_one (d ℓ : ℕ) (D F : ℝ) : frakU d ℓ D F ≤ 1 := by
  unfold frakU
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

theorem frakU_nonneg (d ℓ : ℕ) {D F : ℝ} (hD : 0 < D) (hF : 0 ≤ F) : 0 ≤ frakU d ℓ D F := by
  unfold frakU
  split_ifs
  · norm_num
  · exact le_min zero_le_one (mul_nonneg (sigmaNorm_nonneg d) (Bbar32_nonneg' _ hD hF))

theorem frakU_le_sigma {d ℓ : ℕ} (hℓ : 1 ≤ ℓ) (D F : ℝ) :
    frakU d ℓ D F ≤ (sigmaNorm d : ℝ) * Bbar32 (3 ^ (d * (ℓ - 1))) D F := by
  unfold frakU
  split_ifs with h
  · omega
  · exact min_le_right _ _


/-! ### The series `S_∞` -/

theorem geom_partial_le {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) (m : ℕ) :
    ∑ j ∈ Finset.range m, q ^ j ≤ 1 / (1 - q) := by
  have h := geom_sum_mul_neg q m
  have hq : 0 < 1 - q := by linarith
  rw [le_div_iff₀ hq, h]
  have : 0 ≤ q ^ m := pow_nonneg h0 m
  linarith

theorem frakU_tail {d : ℕ} {D F r U : ℝ} (hD : 0 < D) (hF : 0 ≤ F) (ℓ1 : ℕ) (hr : 0 ≤ r)
    (hr2 : 1 ≤ r ^ 2 * ((3 ^ d : ℕ) : ℝ))
    (hU : (sigmaNorm d : ℝ) * Bbar32 (3 ^ (d * ℓ1)) D F ≤ U) (j : ℕ) :
    frakU d (ℓ1 + 1 + j) D F ≤ r ^ j * U := by
  have hℓ : 1 ≤ ℓ1 + 1 + j := by omega
  have e1 : ℓ1 + 1 + j - 1 = ℓ1 + j := by omega
  have e2 : 3 ^ (d * (ℓ1 + j)) = (3 ^ d) ^ j * 3 ^ (d * ℓ1) := by
    rw [Nat.mul_add, pow_add, pow_mul 3 d j, mul_comm]
  have hm : 1 ≤ 3 ^ d := Nat.one_le_pow _ _ (by norm_num)
  have hn : 1 ≤ 3 ^ (d * ℓ1) := Nat.one_le_pow _ _ (by norm_num)
  have hs := sigmaNorm_nonneg d
  calc frakU d (ℓ1 + 1 + j) D F
      ≤ (sigmaNorm d : ℝ) * Bbar32 (3 ^ (d * (ℓ1 + 1 + j - 1))) D F := frakU_le_sigma hℓ D F
    _ = (sigmaNorm d : ℝ) * Bbar32 ((3 ^ d) ^ j * 3 ^ (d * ℓ1)) D F := by rw [e1, e2]
    _ ≤ (sigmaNorm d : ℝ) * (r ^ j * Bbar32 (3 ^ (d * ℓ1)) D F) := by
        gcongr
        exact Bbar32_scale_iter hD hF hm hn hr hr2 j
    _ = r ^ j * ((sigmaNorm d : ℝ) * Bbar32 (3 ^ (d * ℓ1)) D F) := by ring
    _ ≤ r ^ j * U := by gcongr

/-- `S_∞ ≤ P + U ŷ^{ℓ₁+1}/(1 - rŷ)`, from bounds of the first `ℓ₁ + 1` cuts and the ratio bound. -/
theorem Sinf_le {d : ℕ} (row : Row d) {D F : ℝ} (hD : 0 < D) (hF : 0 ≤ F)
    {yh r U P : ℝ} {ℓ1 : ℕ} (hx : 0 < row.xHist) (hy : row.xHist⁻¹ ≤ yh)
    (hr : 0 ≤ r) (hr2 : 1 ≤ r ^ 2 * ((3 ^ d : ℕ) : ℝ)) (hry : r * yh < 1)
    (hU : (sigmaNorm d : ℝ) * Bbar32 (3 ^ (d * ℓ1)) D F ≤ U)
    (hP : ∑ ℓ ∈ Finset.range (ℓ1 + 1), frakU d ℓ D F * yh ^ ℓ ≤ P) :
    row.Sinf D F ≤ P + U * yh ^ (ℓ1 + 1) / (1 - r * yh) := by
  have hy0 : 0 < yh := lt_of_lt_of_le (inv_pos.2 hx) hy
  have hq : 0 < 1 - r * yh := by linarith
  have hU0 : 0 ≤ U := le_trans (mul_nonneg (sigmaNorm_nonneg d) (Bbar32_nonneg' _ hD hF)) hU
  have hg0 : ∀ ℓ, 0 ≤ frakU d ℓ D F * yh ^ ℓ := fun ℓ =>
    mul_nonneg (frakU_nonneg d ℓ hD hF) (pow_nonneg hy0.le _)
  have hf0 : ∀ ℓ, 0 ≤ frakU d ℓ D F * row.xHist⁻¹ ^ ℓ := fun ℓ =>
    mul_nonneg (frakU_nonneg d ℓ hD hF) (pow_nonneg (inv_pos.2 hx).le _)
  have htail0 : 0 ≤ U * yh ^ (ℓ1 + 1) / (1 - r * yh) := by positivity
  unfold Row.Sinf
  refine Real.tsum_le_of_sum_range_le hf0 fun n => ?_
  have hfg : ∑ i ∈ Finset.range n, frakU d i D F * row.xHist⁻¹ ^ i ≤
      ∑ i ∈ Finset.range n, frakU d i D F * yh ^ i :=
    Finset.sum_le_sum fun i _ => by
      have := frakU_nonneg d i hD hF
      gcongr
  refine hfg.trans ?_
  rcases le_total n (ℓ1 + 1) with hn | hn
  · calc ∑ i ∈ Finset.range n, frakU d i D F * yh ^ i
        ≤ ∑ i ∈ Finset.range (ℓ1 + 1), frakU d i D F * yh ^ i :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn) fun i _ _ => hg0 i
      _ ≤ P + _ := by linarith
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [Finset.sum_range_add]
    have hterm : ∀ j, frakU d (ℓ1 + 1 + j) D F * yh ^ (ℓ1 + 1 + j) ≤
        (U * yh ^ (ℓ1 + 1)) * (r * yh) ^ j := fun j => by
      have h1 := frakU_tail hD hF ℓ1 hr hr2 hU j
      calc frakU d (ℓ1 + 1 + j) D F * yh ^ (ℓ1 + 1 + j)
          ≤ (r ^ j * U) * yh ^ (ℓ1 + 1 + j) := by gcongr
        _ = (U * yh ^ (ℓ1 + 1)) * (r * yh) ^ j := by ring
    have hsum : ∑ j ∈ Finset.range m, frakU d (ℓ1 + 1 + j) D F * yh ^ (ℓ1 + 1 + j) ≤
        U * yh ^ (ℓ1 + 1) / (1 - r * yh) := by
      calc _ ≤ ∑ j ∈ Finset.range m, (U * yh ^ (ℓ1 + 1)) * (r * yh) ^ j :=
            Finset.sum_le_sum fun j _ => hterm j
        _ = (U * yh ^ (ℓ1 + 1)) * ∑ j ∈ Finset.range m, (r * yh) ^ j := by rw [Finset.mul_sum]
        _ ≤ (U * yh ^ (ℓ1 + 1)) * (1 / (1 - r * yh)) := by
            gcongr
            exact geom_partial_le (by positivity) hry m
        _ = _ := by ring
    linarith

/-- A bound for `σ_d B̄₃₂(n, ϖ)` from the radicand at `T_+`. -/
theorem sigma_Bbar_le {d n : ℕ} {D F Tp r u : ℝ} (hD : 0 < D) (hF : 0 ≤ F) (hFD : F ≤ D)
    (hTp : 0 ≤ Tp) (hT : (F / D) ^ 32 ≤ Tp ^ 31) (hr : 0 ≤ r) (hX : Xsum Tp n ≤ r ^ 32)
    (hu : (sigmaNorm d : ℝ) * r ≤ u) : (sigmaNorm d : ℝ) * Bbar32 n D F ≤ u :=
  (mul_le_mul_of_nonneg_left (Bbar32_le hD hF hFD hTp hT hr hX) (sigmaNorm_nonneg d)).trans hu

theorem frakU_le_of {d ℓ : ℕ} (hℓ : 1 ≤ ℓ) {D F Tp r u : ℝ} (hD : 0 < D) (hF : 0 ≤ F)
    (hFD : F ≤ D) (hTp : 0 ≤ Tp) (hT : (F / D) ^ 32 ≤ Tp ^ 31) (hr : 0 ≤ r)
    (hX : Xsum Tp (3 ^ (d * (ℓ - 1))) ≤ r ^ 32) (hu : (sigmaNorm d : ℝ) * r ≤ u) :
    frakU d ℓ D F ≤ u :=
  (frakU_le_sigma hℓ D F).trans (sigma_Bbar_le hD hF hFD hTp hT hr hX hu)

/-- O.avg.5 from the crude bound. -/
theorem frakU_twelve_lt_one {d : ℕ} {D F : ℝ} (hD : 0 < D) (hF : 0 ≤ F)
    (hσ : (sigmaNorm d : ℝ) < 2)
    (hn : 10 ^ 26 ≤ (1 / 2 : ℝ) ^ 32 * ((3 ^ (d * (12 - 1)) : ℕ) : ℝ) ^ 16) :
    frakU d 12 D F < 1 := by
  have hB := Bbar32_crude hD hF (Nat.one_le_pow _ _ (by norm_num)) (by norm_num) hn
  have hs := sigmaNorm_nonneg d
  calc frakU d 12 D F ≤ (sigmaNorm d : ℝ) * Bbar32 (3 ^ (d * (12 - 1))) D F :=
        frakU_le_sigma (by norm_num) D F
    _ ≤ (sigmaNorm d : ℝ) * (1 / 2) := by gcongr
    _ < 1 := by linarith

end GMCExplicitDelta.Certificates
