module

public import GMCExplicitDelta.Certificates.Group4Fixed
public import GMCExplicitDelta.Contract.DerivedFresh
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# The band operator `𝐐(δ)` is dominated by an explicit fixed-point matrix

`bandUp S dp dq` is the fixed-point matrix `I + 𝗎s𝐋 + c₂T₂ + c₃∑_{n=3}^{64}T_n + 1/S` (all rounded
up), where `T_n = (𝖺s𝐋)^n/n!` and `s = δ² = dp/dq`; the last `1/S` absorbs the tail
`c₃∑_{n>64}(𝖺s𝐋)^n/n!`, bounded through `‖𝖺s𝐋‖_∞ ≤ z_b = 1520𝖺s < 66`.
-/

@[expose] public section

open Matrix GMCNumerics GMCExplicitDelta.Contract

namespace GMCExplicitDelta.Certificates.Group4

/-! ### The generator matrix -/

theorem generatorMatrix_entry (i j : Fin 33) :
    generatorMatrix i j =
      (if (j : ℕ) = i then ((i : ℕ) : ℝ) ^ 2 / 2 else 0) +
        (if (j : ℕ) + 1 = i then ((i : ℕ) : ℝ) * (2 * ((i : ℕ) : ℝ) - 1) / 2 else 0) := by
  rw [generatorMatrix_apply, GMCExplicitDelta.Insertion.coeff_coshL]
  simp only [Polynomial.coeff_X_pow]
  by_cases h1 : (j : ℕ) = i
  · have h2 : ¬ ((j : ℕ) + 1 = i) := by omega
    simp [h1]
  · by_cases h2 : (j : ℕ) + 1 = i
    · have h3 : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) + 1 := by exact_mod_cast h2.symm
      simp only [h1, h2, if_true, if_false]
      rw [h3]
      ring
    · simp [h1, h2]

theorem generatorMatrix_nonneg (i j : Fin 33) : 0 ≤ generatorMatrix i j := by
  rw [generatorMatrix_entry]
  have hi : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
  apply add_nonneg
  · split_ifs <;> positivity
  · split_ifs with h
    · have h1 : (1 : ℝ) ≤ ((i : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ (i : ℕ))
      have : 0 ≤ 2 * ((i : ℕ) : ℝ) - 1 := by linarith
      positivity
    · exact le_rfl

theorem generatorMatrix_rowsum (i : Fin 33) : ∑ j, generatorMatrix i j ≤ 1520 := by
  have hi0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
  have hi32 : ((i : ℕ) : ℝ) ≤ 32 := by exact_mod_cast (by omega : (i : ℕ) ≤ 32)
  simp only [generatorMatrix_entry, Finset.sum_add_distrib]
  have hA : ∑ j : Fin 33, (if (j : ℕ) = i then ((i : ℕ) : ℝ) ^ 2 / 2 else 0)
      = ((i : ℕ) : ℝ) ^ 2 / 2 := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      have : (b : ℕ) ≠ i := fun h => hb (Fin.ext h)
      simp [this]
    · simp
  have hB : ∑ j : Fin 33, (if (j : ℕ) + 1 = i then ((i : ℕ) : ℝ) * (2 * ((i : ℕ) : ℝ) - 1) / 2
      else 0) ≤ ((i : ℕ) : ℝ) * (2 * ((i : ℕ) : ℝ) - 1) / 2 := by
    by_cases h0 : (i : ℕ) = 0
    · have : ∀ j : Fin 33, ¬ ((j : ℕ) + 1 = i) := fun j => by omega
      simp [this, h0]
    · have h1 : (1 : ℝ) ≤ ((i : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ (i : ℕ))
      have hc : 0 ≤ ((i : ℕ) : ℝ) * (2 * ((i : ℕ) : ℝ) - 1) / 2 := by
        have : 0 ≤ 2 * ((i : ℕ) : ℝ) - 1 := by linarith
        positivity
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      have hcard : (Finset.univ.filter fun j : Fin 33 => (j : ℕ) + 1 = i).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha b hb
        simp only [Finset.mem_filter] at ha hb
        exact Fin.ext (by omega)
      have : ((Finset.univ.filter fun j : Fin 33 => (j : ℕ) + 1 = i).card : ℝ) ≤ 1 := by
        exact_mod_cast hcard
      nlinarith
  rw [hA]
  nlinarith

/-! ### Row sums of powers -/

/-- Row-sum bound of a nonnegative matrix. -/
def RowLe {n : ℕ} (z : ℝ) (X : Matrix (Fin n) (Fin n) ℝ) : Prop := ∀ i, ∑ j, X i j ≤ z

theorem rowLe_mul {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ} {za zb : ℝ}
    (hA0 : ∀ i j, 0 ≤ A i j) (hzb : 0 ≤ zb)
    (hA : RowLe za A) (hB : RowLe zb B) : RowLe (za * zb) (A * B) := by
  intro i
  simp only [Matrix.mul_apply]
  rw [Finset.sum_comm]
  have : ∀ k, ∑ j, A i k * B k j ≤ A i k * zb := fun k => by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hB k) (hA0 i k)
  refine (Finset.sum_le_sum fun k _ => this k).trans ?_
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (hA i) hzb

theorem rowLe_pow {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} (hX0 : ∀ i j, 0 ≤ X i j) {z : ℝ}
    (hz : 0 ≤ z) (hX : RowLe z X) :
    ∀ k : ℕ, (∀ i j, 0 ≤ (X ^ k) i j) ∧ RowLe (z ^ k) (X ^ k) := by
  intro k
  induction k with
  | zero =>
    refine ⟨fun i j => ?_, fun i => ?_⟩
    · by_cases h : i = j <;> simp [Matrix.one_apply, h]
    · simp [Matrix.one_apply]
  | succ k ih =>
    refine ⟨fun i j => ?_, ?_⟩
    · rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun l _ => mul_nonneg (ih.1 i l) (hX0 l j)
    · rw [pow_succ, pow_succ]
      exact rowLe_mul (fun i j => ih.1 i j) hz ih.2 hX

theorem entry_le_pow {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} (hX0 : ∀ i j, 0 ≤ X i j) {z : ℝ}
    (hz : 0 ≤ z) (hX : RowLe z X) (k : ℕ) (i j : Fin n) : (X ^ k) i j ≤ z ^ k :=
  ((Finset.single_le_sum (fun l _ => (rowLe_pow hX0 hz hX k).1 i l) (Finset.mem_univ j)).trans
    ((rowLe_pow hX0 hz hX k).2 i))

/-! ### The tail of the exponential series -/

theorem tail_summable (N : ℕ) (z : ℝ) :
    Summable (fun m : ℕ => z ^ (m + N) / ((m + N).factorial : ℝ)) :=
  (summable_nat_add_iff N).2 (Real.summable_pow_div_factorial z)

theorem tail_le (N : ℕ) {z : ℝ} (hz0 : 0 ≤ z) (hz : z < N + 1) :
    ∑' m : ℕ, z ^ (m + N) / ((m + N).factorial : ℝ) ≤
      z ^ N / (N.factorial : ℝ) / (1 - z / (N + 1)) := by
  have hN : (0 : ℝ) < N + 1 := by positivity
  have hr0 : 0 ≤ z / (N + 1) := by positivity
  have hr1 : z / (N + 1) < 1 := by rw [div_lt_one hN]; exact hz
  have hg : Summable (fun m : ℕ => z ^ N / (N.factorial : ℝ) * (z / (N + 1)) ^ m) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hle : ∀ m : ℕ, z ^ (m + N) / ((m + N).factorial : ℝ) ≤
      z ^ N / (N.factorial : ℝ) * (z / (N + 1)) ^ m := by
    intro m
    have hf : (N.factorial * (N + 1) ^ m : ℕ) ≤ (N + m).factorial :=
      Nat.factorial_mul_pow_le_factorial
    have hf' : (N.factorial : ℝ) * (N + 1) ^ m ≤ ((m + N).factorial : ℝ) := by
      rw [Nat.add_comm m N]; exact_mod_cast hf
    have hpos : (0 : ℝ) < N.factorial * (N + 1) ^ m := by positivity
    calc z ^ (m + N) / ((m + N).factorial : ℝ)
        ≤ z ^ (m + N) / (N.factorial * (N + 1) ^ m) :=
          div_le_div_of_nonneg_left (by positivity) hpos hf'
      _ = z ^ N / (N.factorial : ℝ) * (z / (N + 1)) ^ m := by
          rw [div_pow, pow_add]; field_simp
  calc ∑' m : ℕ, z ^ (m + N) / ((m + N).factorial : ℝ)
      ≤ ∑' m : ℕ, z ^ N / (N.factorial : ℝ) * (z / (N + 1)) ^ m :=
        (tail_summable N z).tsum_le_tsum hle hg
    _ = z ^ N / (N.factorial : ℝ) / (1 - z / (N + 1)) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]; ring

end GMCExplicitDelta.Certificates.Group4
