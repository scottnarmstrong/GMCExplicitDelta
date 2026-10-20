module

public import GMCExplicitDelta.Assembly.Scaling
public import GMCExplicitDelta.Insertion.CoshGeneratorPoly

/-!
# R4(g): degree-graded scaling of the band operator

`bandRow δ h r ≤ λ^{32-r} bandRow δ_* h r` for `δ² = λδ_*²`, `0 < λ ≤ 1`: the generator matrix is
lower bidiagonal with nonnegative entries, so the `(i,j)` entry of every power of `s𝐋` carries a
factor `s^n` with `n ≥ i - j`.
-/

@[expose] public section

open Matrix

namespace GMCExplicitDelta.Assembly

open Contract

/-- Nonnegative lower triangular matrices. -/
def TriNN (M : Matrix (Fin 33) (Fin 33) ℝ) : Prop :=
  (∀ i j, 0 ≤ M i j) ∧ ∀ i j : Fin 33, i < j → M i j = 0

/-- `M ≤ l^{i-j} M'` entrywise. -/
def DomBy (l : ℝ) (M M' : Matrix (Fin 33) (Fin 33) ℝ) : Prop :=
  ∀ i j : Fin 33, M i j ≤ l ^ ((i : ℕ) - (j : ℕ)) * M' i j

theorem TriNN.one : TriNN (1 : Matrix (Fin 33) (Fin 33) ℝ) := by
  refine ⟨fun i j => ?_, fun i j h => ?_⟩
  · by_cases h : i = j <;> simp [Matrix.one_apply, h]
  · simp [Matrix.one_apply, h.ne]

theorem TriNN.mul {A B : Matrix (Fin 33) (Fin 33) ℝ} (hA : TriNN A) (hB : TriNN B) :
    TriNN (A * B) := by
  refine ⟨fun i j => ?_, fun i j hij => ?_⟩
  · rw [Matrix.mul_apply]; exact Finset.sum_nonneg fun k _ => mul_nonneg (hA.1 _ _) (hB.1 _ _)
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases h : i < k
    · rw [hA.2 i k h, zero_mul]
    · rw [hB.2 k j (lt_of_le_of_lt (not_lt.mp h) hij), mul_zero]

theorem TriNN.pow {A : Matrix (Fin 33) (Fin 33) ℝ} (hA : TriNN A) (n : ℕ) : TriNN (A ^ n) := by
  induction n with
  | zero => simpa using TriNN.one
  | succ n ih => rw [pow_succ]; exact ih.mul hA

theorem DomBy.one {l : ℝ} (hl0 : 0 ≤ l) : DomBy l (1 : Matrix (Fin 33) (Fin 33) ℝ) 1 := by
  intro i j
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply, h]

theorem DomBy.mul {l : ℝ} (hl0 : 0 ≤ l) {A A' B B' : Matrix (Fin 33) (Fin 33) ℝ}
    (hA : TriNN A) (hA' : TriNN A') (hB : TriNN B) (hB' : TriNN B')
    (hAA : DomBy l A A') (hBB : DomBy l B B') : DomBy l (A * B) (A' * B') := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases h1 : i < k
  · rw [hA.2 i k h1, zero_mul]
    exact mul_nonneg (pow_nonneg hl0 _) (mul_nonneg (hA'.1 _ _) (hB'.1 _ _))
  by_cases h2 : k < j
  · rw [hB.2 k j h2, mul_zero]
    exact mul_nonneg (pow_nonneg hl0 _) (mul_nonneg (hA'.1 _ _) (hB'.1 _ _))
  have hik : (k : ℕ) ≤ i := not_lt.mp h1
  have hkj : (j : ℕ) ≤ k := not_lt.mp h2
  calc A i k * B k j ≤ (l ^ ((i : ℕ) - (k : ℕ)) * A' i k) * (l ^ ((k : ℕ) - (j : ℕ)) * B' k j) :=
        mul_le_mul (hAA i k) (hBB k j) (hB.1 _ _) (mul_nonneg (pow_nonneg hl0 _) (hA'.1 _ _))
    _ = l ^ ((i : ℕ) - (j : ℕ)) * (A' i k * B' k j) := by
        have : (i : ℕ) - (j : ℕ) = ((i : ℕ) - (k : ℕ)) + ((k : ℕ) - (j : ℕ)) := by omega
        rw [this, pow_add]; ring

theorem DomBy.pow {l : ℝ} (hl0 : 0 ≤ l) {A A' : Matrix (Fin 33) (Fin 33) ℝ}
    (hA : TriNN A) (hA' : TriNN A') (h : DomBy l A A') (n : ℕ) : DomBy l (A ^ n) (A' ^ n) := by
  induction n with
  | zero => simpa using DomBy.one hl0
  | succ n ih => rw [pow_succ, pow_succ]; exact DomBy.mul hl0 (hA.pow n) (hA'.pow n) hA hA' ih h

/-! ### The generator matrix -/

theorem generatorMatrix_entry (i j : Fin 33) :
    generatorMatrix i j =
      (if (j : ℕ) = i then (j : ℝ) ^ 2 / 2 else 0) +
        (if (j : ℕ) + 1 = i then ((j : ℝ) + 1) * (2 * j + 1) / 2 else 0) := by
  rw [generatorMatrix_apply, Insertion.coeff_coshL]
  simp only [Polynomial.coeff_X_pow]
  by_cases h1 : (j : ℕ) = i
  · have : (j : ℕ) + 1 ≠ i := by omega
    simp [h1, this]
  · by_cases h2 : (j : ℕ) + 1 = i
    · have : (i : ℕ) ≠ j := fun h => h1 h.symm
      simp [h1, h2, this]
    · have : (i : ℕ) ≠ j := fun h => h1 h.symm
      have : (i : ℕ) ≠ j + 1 := fun h => h2 h.symm
      simp [h1, h2, *]

theorem generatorMatrix_triNN : TriNN generatorMatrix := by
  refine ⟨fun i j => ?_, fun i j hij => ?_⟩
  · rw [generatorMatrix_entry]
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    split_ifs <;> positivity
  · rw [generatorMatrix_entry]
    have h : (i : ℕ) < j := hij
    have h1 : (j : ℕ) ≠ i := by omega
    have h2 : (j : ℕ) + 1 ≠ i := by omega
    simp [h1, h2]

theorem generatorMatrix_le (i j : Fin 33) : generatorMatrix i j ≤ 1008 := by
  rw [generatorMatrix_entry]
  have hi : (i : ℕ) ≤ 32 := by omega
  have hj : (j : ℕ) ≤ 32 := by omega
  have hj' : (j : ℝ) ≤ 32 := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  by_cases h1 : (j : ℕ) = i
  · have : (j : ℕ) + 1 ≠ i := by omega
    rw [if_pos h1, if_neg this, add_zero]
    nlinarith
  · by_cases h2 : (j : ℕ) + 1 = i
    · have hj31 : (j : ℝ) ≤ 31 := by
        have : (j : ℕ) ≤ 31 := by omega
        exact_mod_cast this
      rw [if_neg h1, if_pos h2, zero_add]
      nlinarith
    · simp [h1, h2]

/-- `(𝐋^n)_{ij} = 0` when `j + n < i`. -/
theorem generatorMatrix_pow_eq_zero (n : ℕ) (i j : Fin 33) (h : (j : ℕ) + n < i) :
    (generatorMatrix ^ n) i j = 0 := by
  induction n generalizing i with
  | zero =>
    have : i ≠ j := fun e => by subst e; omega
    simp [Matrix.one_apply, this]
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : (j : ℕ) + n < k
    · rw [ih k hk, mul_zero]
    · have : generatorMatrix i k = 0 := by
        rw [generatorMatrix_entry]
        have h1 : (k : ℕ) ≠ i := by omega
        have h2 : (k : ℕ) + 1 ≠ i := by omega
        simp [h1, h2]
      rw [this, zero_mul]

theorem generatorMatrix_pow_le (n : ℕ) (i j : Fin 33) :
    (generatorMatrix ^ n) i j ≤ 33264 ^ n := by
  induction n generalizing i with
  | zero =>
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply]
    calc ∑ k, generatorMatrix i k * (generatorMatrix ^ n) k j
        ≤ ∑ _k : Fin 33, (1008 : ℝ) * 33264 ^ n := by
          refine Finset.sum_le_sum fun k _ => ?_
          exact mul_le_mul (generatorMatrix_le i k) (ih k) ((generatorMatrix_triNN.pow n).1 _ _)
            (by norm_num)
      _ = 33264 ^ (n + 1) := by simp [Finset.sum_const]; ring

/-! ### The band matrix -/

theorem bandMatrix_apply' (δ : ℝ) (i j : Fin 33) :
    bandMatrix δ i j =
      (1 : Matrix (Fin 33) (Fin 33) ℝ) i j + (varU : ℝ) * δ ^ 2 * (generatorMatrix ^ 1) i j +
        (ratioC2 : ℝ) / 2 * ((proxyA : ℝ) * δ ^ 2) ^ 2 * (generatorMatrix ^ 2) i j +
        (ratioC3 : ℝ) * ∑' n : ℕ, (proxyA : ℝ) ^ (n + 3) / ((n + 3).factorial : ℝ) *
          (δ ^ 2) ^ (n + 3) * (generatorMatrix ^ (n + 3)) i j := by
  unfold bandMatrix
  simp only [Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, smul_pow, pow_one]
  congr 2
  · rw [pow_two (generatorMatrix)]
    ring
  · congr 1
    ext n
    ring

theorem bandTerm_summable (a s : ℝ) (i j : Fin 33) :
    Summable fun n : ℕ => a ^ (n + 3) / ((n + 3).factorial : ℝ) * s ^ (n + 3) *
      (generatorMatrix ^ (n + 3)) i j := by
  have h1 : Summable fun m : ℕ => (|a * s| * 33264) ^ m / (m.factorial : ℝ) :=
    Real.summable_pow_div_factorial _
  have h2 : Summable fun n : ℕ => (|a * s| * 33264) ^ (n + 3) / ((n + 3).factorial : ℝ) :=
    (summable_nat_add_iff 3).mpr h1
  refine Summable.of_norm_bounded h2 fun n => ?_
  have hn := (generatorMatrix_triNN.pow (n + 3)).1 i j
  have hle := generatorMatrix_pow_le (n + 3) i j
  have hf : (0 : ℝ) < ((n + 3).factorial : ℝ) := by positivity
  rw [Real.norm_eq_abs]
  have : a ^ (n + 3) / ((n + 3).factorial : ℝ) * s ^ (n + 3) *
      (generatorMatrix ^ (n + 3)) i j =
      (a * s) ^ (n + 3) * (generatorMatrix ^ (n + 3)) i j / ((n + 3).factorial : ℝ) := by
    rw [mul_pow]; ring
  rw [this, abs_div, abs_mul, abs_pow, abs_of_pos hf, abs_of_nonneg hn, mul_pow]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hle (pow_nonneg (abs_nonneg _) _)) hf.le

theorem bandTerm_nonneg {a s : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (i j : Fin 33) (n : ℕ) :
    0 ≤ a ^ (n + 3) / ((n + 3).factorial : ℝ) * s ^ (n + 3) * (generatorMatrix ^ (n + 3)) i j :=
  mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hs _))
    ((generatorMatrix_triNN.pow _).1 _ _)

theorem varU_nonneg : (0 : ℝ) ≤ varU := by unfold varU; norm_num
theorem ratioC2_nonneg : (0 : ℝ) ≤ ratioC2 := by unfold ratioC2; norm_num
theorem ratioC3_nonneg : (0 : ℝ) ≤ ratioC3 := by unfold ratioC3; norm_num

theorem bandMatrix_triNN (δ : ℝ) : TriNN (bandMatrix δ) := by
  have hL := generatorMatrix_triNN
  have hp := proxyA_pos
  have hs : 0 ≤ δ ^ 2 := sq_nonneg δ
  refine ⟨fun i j => ?_, fun i j hij => ?_⟩
  · rw [bandMatrix_apply']
    have h0 := (TriNN.one).1 i j
    have h1 := (hL.pow 1).1 i j
    have h2 := (hL.pow 2).1 i j
    have h3 : 0 ≤ ∑' n : ℕ, (proxyA : ℝ) ^ (n + 3) / ((n + 3).factorial : ℝ) *
        (δ ^ 2) ^ (n + 3) * (generatorMatrix ^ (n + 3)) i j :=
      tsum_nonneg fun n => bandTerm_nonneg hp.le hs i j n
    have := varU_nonneg; have := ratioC2_nonneg; have := ratioC3_nonneg
    positivity
  · rw [bandMatrix_apply']
    have e1 := (TriNN.one).2 i j hij
    have e2 := (hL.pow 1).2 i j hij
    have e3 := (hL.pow 2).2 i j hij
    have e4 : (∑' n : ℕ, (proxyA : ℝ) ^ (n + 3) / ((n + 3).factorial : ℝ) *
        (δ ^ 2) ^ (n + 3) * (generatorMatrix ^ (n + 3)) i j) = 0 := by
      simp only [(hL.pow _).2 i j hij, mul_zero, tsum_zero]
    rw [e1, e2, e3, e4]; ring

/-- The degree-grading step: if `x = 0` or `k ≤ n` then `(l s')^n x ≤ l^k (s'^n x)`. -/
theorem pow_mul_le_of_le {l s' x : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hs' : 0 ≤ s') (hx : 0 ≤ x)
    (n k : ℕ) (h : x = 0 ∨ k ≤ n) : (l * s') ^ n * x ≤ l ^ k * (s' ^ n * x) := by
  rcases h with h | h
  · simp [h]
  · rw [mul_pow, mul_assoc]
    have h1 : l ^ n ≤ l ^ k := pow_le_pow_of_le_one hl0 hl1 h
    have h2 : 0 ≤ s' ^ n * x := mul_nonneg (pow_nonneg hs' _) hx
    calc l ^ n * (s' ^ n * x) ≤ l ^ k * (s' ^ n * x) := mul_le_mul_of_nonneg_right h1 h2
      _ = _ := rfl

theorem generatorMatrix_pow_zero_or (n : ℕ) (i j : Fin 33) :
    (generatorMatrix ^ n) i j = 0 ∨ (i : ℕ) - (j : ℕ) ≤ n := by
  by_cases h : (j : ℕ) + n < i
  · exact Or.inl (generatorMatrix_pow_eq_zero n i j h)
  · exact Or.inr (by omega)

theorem bandMatrix_domBy {δ δ' l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hδ : δ ^ 2 = l * δ' ^ 2) :
    DomBy l (bandMatrix δ) (bandMatrix δ') := by
  intro i j
  have hp := proxyA_pos
  have hs' : 0 ≤ δ' ^ 2 := sq_nonneg δ'
  have hs : 0 ≤ δ ^ 2 := sq_nonneg δ
  have hL := generatorMatrix_triNN
  rw [bandMatrix_apply', bandMatrix_apply']
  have c1 : (1 : Matrix (Fin 33) (Fin 33) ℝ) i j ≤ l ^ ((i : ℕ) - (j : ℕ)) * (1 : Matrix _ _ ℝ) i j := by
    exact DomBy.one hl0 i j
  have key : ∀ (c : ℝ) (n : ℕ), 0 ≤ c →
      c * (δ ^ 2) ^ n * (generatorMatrix ^ n) i j ≤
        l ^ ((i : ℕ) - (j : ℕ)) * (c * (δ' ^ 2) ^ n * (generatorMatrix ^ n) i j) := by
    intro c n hc
    have := pow_mul_le_of_le hl0 hl1 hs' ((hL.pow n).1 i j) n ((i : ℕ) - (j : ℕ))
      (generatorMatrix_pow_zero_or n i j)
    rw [hδ]
    calc c * (l * δ' ^ 2) ^ n * (generatorMatrix ^ n) i j
        = c * ((l * δ' ^ 2) ^ n * (generatorMatrix ^ n) i j) := by ring
      _ ≤ c * (l ^ ((i : ℕ) - (j : ℕ)) * ((δ' ^ 2) ^ n * (generatorMatrix ^ n) i j)) :=
          mul_le_mul_of_nonneg_left this hc
      _ = _ := by ring
  have c2 := key (varU : ℝ) 1 varU_nonneg
  have c3 := key ((ratioC2 : ℝ) / 2 * (proxyA : ℝ) ^ 2) 2 (by
    have := ratioC2_nonneg; positivity)
  have c4 : ∑' n : ℕ, (proxyA : ℝ) ^ (n + 3) / ((n + 3).factorial : ℝ) *
        (δ ^ 2) ^ (n + 3) * (generatorMatrix ^ (n + 3)) i j ≤
      l ^ ((i : ℕ) - (j : ℕ)) * ∑' n : ℕ, (proxyA : ℝ) ^ (n + 3) / ((n + 3).factorial : ℝ) *
        (δ' ^ 2) ^ (n + 3) * (generatorMatrix ^ (n + 3)) i j := by
    rw [← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun n => ?_) (bandTerm_summable _ _ i j)
      ((bandTerm_summable _ _ i j).mul_left _)
    have := key ((proxyA : ℝ) ^ (n + 3) / ((n + 3).factorial : ℝ)) (n + 3) (by positivity)
    exact this
  have e3 : (ratioC2 : ℝ) / 2 * ((proxyA : ℝ) * δ ^ 2) ^ 2 * (generatorMatrix ^ 2) i j =
      ((ratioC2 : ℝ) / 2 * (proxyA : ℝ) ^ 2) * (δ ^ 2) ^ 2 * (generatorMatrix ^ 2) i j := by ring
  have e3' : (ratioC2 : ℝ) / 2 * ((proxyA : ℝ) * δ' ^ 2) ^ 2 * (generatorMatrix ^ 2) i j =
      ((ratioC2 : ℝ) / 2 * (proxyA : ℝ) ^ 2) * (δ' ^ 2) ^ 2 * (generatorMatrix ^ 2) i j := by ring
  have e2 : (varU : ℝ) * δ ^ 2 * (generatorMatrix ^ 1) i j =
      (varU : ℝ) * (δ ^ 2) ^ 1 * (generatorMatrix ^ 1) i j := by ring
  have e2' : (varU : ℝ) * δ' ^ 2 * (generatorMatrix ^ 1) i j =
      (varU : ℝ) * (δ' ^ 2) ^ 1 * (generatorMatrix ^ 1) i j := by ring
  have c3n := ratioC3_nonneg
  rw [e3, e2, e3', e2']
  nlinarith [mul_le_mul_of_nonneg_left c4 c3n]

theorem bandRow_nonneg (δ : ℝ) (h : ℕ) (r : Fin 33) : 0 ≤ bandRow δ h r :=
  ((bandMatrix_triNN δ).pow h).1 _ _

theorem bandRow_le {δ δ' l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hδ : δ ^ 2 = l * δ' ^ 2)
    (h : ℕ) (r : Fin 33) :
    bandRow δ h r ≤ l ^ (32 - (r : ℕ)) * bandRow δ' h r := by
  have := DomBy.pow hl0 (bandMatrix_triNN δ) (bandMatrix_triNN δ')
    (bandMatrix_domBy hl0 hl1 hδ) h 32 r
  simpa [bandRow] using this

end GMCExplicitDelta.Assembly
