module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Field

/-!
# Trigonometric core of the source variance lemma

* An explicit positive quadrature on the nodes `θ_k = (2k+1) π/(n+1)`, `1 ≤ k ≤ n-1`, giving
  `c₁ ≤ c₀ cos (π/(n+1))` for coefficients of a nonnegative trigonometric polynomial at the nodes.
* Fejér positivity of a finitely supported positive semidefinite Toeplitz symbol.
* The limit `2 n² (1 - cos (π/(n+1))) → π²`.
-/

@[expose] public section

namespace GMCExplicitDelta.Source

open Finset Real Filter Topology

/-! ### Quadrature -/

/-- The base angle `π/(n+1)`. -/
noncomputable def alpha (n : ℕ) : ℝ := π / ((n : ℝ) + 1)

/-- The quadrature node `(2k+1) π/(n+1)`. -/
noncomputable def node (n k : ℕ) : ℝ := (2 * (k : ℝ) + 1) * alpha n

/-- The quadrature weight `1 - cos θ_k / cos α`. -/
noncomputable def weight (n k : ℕ) : ℝ := 1 - cos (node n k) / cos (alpha n)

lemma alpha_pos (n : ℕ) : 0 < alpha n := by unfold alpha; positivity

lemma alpha_mul (n : ℕ) : alpha n * ((n : ℝ) + 1) = π := by
  unfold alpha; field_simp

lemma alpha_lt_pi_half {n : ℕ} (hn : 2 ≤ n) : alpha n < π / 2 := by
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have := alpha_mul n
  nlinarith [alpha_pos n, pi_pos]

lemma cos_alpha_pos {n : ℕ} (hn : 2 ≤ n) : 0 < cos (alpha n) :=
  cos_pos_of_mem_Ioo ⟨by linarith [alpha_pos n, pi_pos], alpha_lt_pi_half hn⟩

lemma sum_cos_full (n j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ n) :
    ∑ k ∈ range (n + 1), cos ((j : ℝ) * node n k) = 0 := by
  have hs : 0 < sin ((j : ℝ) * alpha n) := by
    apply sin_pos_of_pos_of_lt_pi
    · exact mul_pos (by exact_mod_cast hj1) (alpha_pos n)
    · have h1 : (j : ℝ) ≤ n := by exact_mod_cast hj2
      have := alpha_mul n
      nlinarith [alpha_pos n]
  have key : ∀ k : ℕ, 2 * sin ((j : ℝ) * alpha n) * cos ((j : ℝ) * node n k) =
      sin (2 * ((k + 1 : ℕ) : ℝ) * ((j : ℝ) * alpha n)) - sin (2 * (k : ℝ) * ((j : ℝ) * alpha n)) := by
    intro k
    have h1 : (j : ℝ) * node n k = 2 * k * ((j : ℝ) * alpha n) + (j : ℝ) * alpha n := by
      simp only [node]; ring
    have h2 : 2 * ((k + 1 : ℕ) : ℝ) * ((j : ℝ) * alpha n) =
        (2 * k * ((j : ℝ) * alpha n) + (j : ℝ) * alpha n) + (j : ℝ) * alpha n := by
      push_cast; ring
    have h3 : 2 * (k : ℝ) * ((j : ℝ) * alpha n) =
        (2 * k * ((j : ℝ) * alpha n) + (j : ℝ) * alpha n) - (j : ℝ) * alpha n := by ring
    rw [h1, h2, h3, sin_add, sin_sub]; ring_nf
  have h : 2 * sin ((j : ℝ) * alpha n) * ∑ k ∈ range (n + 1), cos ((j : ℝ) * node n k) = 0 := by
    rw [Finset.mul_sum, Finset.sum_congr rfl (fun k _ => key k),
      Finset.sum_range_sub (fun k : ℕ => sin (2 * (k : ℝ) * ((j : ℝ) * alpha n)))]
    have : 2 * ((n + 1 : ℕ) : ℝ) * ((j : ℝ) * alpha n) = ((2 * j : ℕ) : ℝ) * π := by
      rw [← alpha_mul n]; push_cast; ring
    rw [this, sin_nat_mul_pi]; simp
  rcases mul_eq_zero.mp h with h | h
  · linarith
  · exact h

/-- (Q1) -/
theorem sum_cos_node (n j : ℕ) (hn : 2 ≤ n) (hj1 : 1 ≤ j) (hj2 : j ≤ n) :
    ∑ k ∈ Ico 1 n, cos ((j : ℝ) * node n k) = -2 * cos ((j : ℝ) * alpha n) := by
  have hfull := sum_cos_full n j hj1 hj2
  have hf0 : cos ((j : ℝ) * node n 0) = cos ((j : ℝ) * alpha n) := by simp [node]
  have hfn : cos ((j : ℝ) * node n n) = cos ((j : ℝ) * alpha n) := by
    have : node n n = 2 * π - alpha n := by
      unfold node; rw [← alpha_mul n]; ring
    rw [this, show (j : ℝ) * (2 * π - alpha n) = j * (2 * π) - j * alpha n by ring]
    exact cos_nat_mul_two_pi_sub _ _
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [Finset.sum_range_succ, Finset.sum_range_succ' _ (m + 1), hf0, hfn] at hfull
  rw [Finset.sum_Ico_eq_sum_range]
  have e : m + 2 - 1 = m + 1 := by omega
  rw [e]
  have : ∑ k ∈ range (m + 1), cos ((j : ℝ) * node (m + 2) (1 + k)) =
      ∑ k ∈ range (m + 1), cos ((j : ℝ) * node (m + 2) (k + 1)) :=
    Finset.sum_congr rfl fun k _ => by rw [Nat.add_comm 1 k]
  rw [this]; linarith

lemma sum_cos_node_one (n : ℕ) (hn : 2 ≤ n) :
    ∑ k ∈ Ico 1 n, cos (node n k) = -2 * cos (alpha n) := by
  simpa using sum_cos_node n 1 hn le_rfl (by omega)

lemma sum_cos_node_two (n : ℕ) (hn : 2 ≤ n) :
    ∑ k ∈ Ico 1 n, cos (2 * node n k) = -2 * cos (2 * alpha n) := by
  simpa using sum_cos_node n 2 hn (by omega) hn

lemma cos_mul_cos_succ (θ : ℝ) (i : ℕ) :
    cos θ * cos (((i + 1 : ℕ) : ℝ) * θ) = (cos (((i + 2 : ℕ) : ℝ) * θ) + cos ((i : ℝ) * θ)) / 2 := by
  have h1 : ((i + 2 : ℕ) : ℝ) * θ = (((i + 1 : ℕ) : ℝ) * θ) + θ := by push_cast; ring
  have h2 : (i : ℝ) * θ = (((i + 1 : ℕ) : ℝ) * θ) - θ := by push_cast; ring
  rw [h1, h2, cos_add, cos_sub]; ring

lemma sum_weight_mul (n : ℕ) (_hn : 2 ≤ n) (g : ℕ → ℝ) :
    ∑ k ∈ Ico 1 n, weight n k * g k =
      ∑ k ∈ Ico 1 n, g k - (∑ k ∈ Ico 1 n, cos (node n k) * g k) / cos (alpha n) := by
  rw [Finset.sum_div, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold weight; ring

/-- (Q2), `2 ≤ j ≤ n - 1`. -/
theorem sum_weight_cos_eq_zero (n j : ℕ) (hn : 2 ≤ n) (hj1 : 2 ≤ j) (hj2 : j + 1 ≤ n) :
    ∑ k ∈ Ico 1 n, weight n k * cos ((j : ℝ) * node n k) = 0 := by
  have hc := cos_alpha_pos hn
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [sum_weight_mul n hn (fun k => cos (((i + 1 : ℕ) : ℝ) * node n k))]
  have hprod : ∑ k ∈ Ico 1 n, cos (node n k) * cos (((i + 1 : ℕ) : ℝ) * node n k) =
      (∑ k ∈ Ico 1 n, cos (((i + 2 : ℕ) : ℝ) * node n k) +
        ∑ k ∈ Ico 1 n, cos ((i : ℝ) * node n k)) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun k _ => cos_mul_cos_succ _ _
  rw [hprod, sum_cos_node n (i + 2) hn (by omega) (by omega), sum_cos_node n i hn (by omega) (by omega),
    sum_cos_node n (i + 1) hn (by omega) (by omega)]
  have := cos_mul_cos_succ (alpha n) i
  have h2 : cos (((i + 2 : ℕ) : ℝ) * alpha n) =
      2 * cos (alpha n) * cos (((i + 1 : ℕ) : ℝ) * alpha n) - cos ((i : ℝ) * alpha n) := by
    linarith
  rw [h2]; field_simp; ring

/-- (Q2), `Σ W_k = n + 1`. -/
theorem sum_weight (n : ℕ) (hn : 2 ≤ n) :
    ∑ k ∈ Ico 1 n, weight n k = (n : ℝ) + 1 := by
  have hc := cos_alpha_pos hn
  have := sum_weight_mul n hn (fun _ => 1)
  simp only [mul_one] at this
  rw [this, sum_cos_node_one n hn]
  simp [Nat.card_Ico, Nat.cast_sub (show 1 ≤ n by omega)]
  field_simp
  ring

/-- (Q2), `Σ W_k cos θ_k = -(n+1)/(2 cos α)`. -/
theorem sum_weight_cos_one (n : ℕ) (hn : 2 ≤ n) :
    ∑ k ∈ Ico 1 n, weight n k * cos (node n k) = -((n : ℝ) + 1) / (2 * cos (alpha n)) := by
  have hc := cos_alpha_pos hn
  rw [sum_weight_mul n hn (fun k => cos (node n k))]
  have hsq : ∑ k ∈ Ico 1 n, cos (node n k) * cos (node n k) =
      ((n : ℝ) - 1) / 2 + (∑ k ∈ Ico 1 n, cos (2 * node n k)) / 2 := by
    have : ∀ k ∈ Ico 1 n, cos (node n k) * cos (node n k) =
        1 / 2 + cos (2 * node n k) / 2 := fun k _ => by
      rw [← sq, cos_sq]
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_div]
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub (show 1 ≤ n by omega)]
    push_cast
    ring
  rw [hsq, sum_cos_node_one n hn, sum_cos_node_two n hn, cos_two_mul]
  field_simp
  ring

lemma weight_pos (n : ℕ) (hn : 2 ≤ n) (k : ℕ) (hk : k ∈ Ico 1 n) : 0 < weight n k := by
  have hc := cos_alpha_pos hn
  obtain ⟨hk1, hkn⟩ := Finset.mem_Ico.mp hk
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hkn' : (k : ℝ) + 1 ≤ n := by exact_mod_cast hkn
  have ha := alpha_pos n
  have hm := alpha_mul n
  have hlt1 : alpha n < node n k := by unfold node; nlinarith
  have hlt2 : node n k < 2 * π - alpha n := by
    unfold node
    nlinarith [mul_nonneg (sub_nonneg.mpr hkn') ha.le]
  have hcos : cos (node n k) < cos (alpha n) := by
    by_cases hle : node n k ≤ π
    · exact cos_lt_cos_of_nonneg_of_le_pi ha.le hle hlt1
    · push Not at hle
      rw [← cos_two_pi_sub (node n k)]
      exact cos_lt_cos_of_nonneg_of_le_pi ha.le (by linarith) (by linarith)
  unfold weight
  have : cos (node n k) / cos (alpha n) < 1 := by rw [div_lt_one hc]; exact hcos
  linarith

/-- (Q3), the exact quadrature identity. -/
theorem quadrature_sum (n : ℕ) (hn : 2 ≤ n) (c : ℕ → ℝ) :
    ∑ k ∈ Ico 1 n, weight n k * (c 0 + 2 * ∑ j ∈ Ico 1 n, c j * cos ((j : ℝ) * node n k)) =
      ((n : ℝ) + 1) * (c 0 - c 1 / cos (alpha n)) := by
  have hc := cos_alpha_pos hn
  have e : ∀ k, weight n k * (c 0 + 2 * ∑ j ∈ Ico 1 n, c j * cos ((j : ℝ) * node n k)) =
      c 0 * weight n k + 2 * ∑ j ∈ Ico 1 n, c j * (weight n k * cos ((j : ℝ) * node n k)) := by
    intro k
    rw [mul_add, mul_comm _ (c 0)]
    congr 1
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [Finset.sum_congr rfl fun k _ => e k, Finset.sum_add_distrib, ← Finset.mul_sum, sum_weight n hn,
    ← Finset.mul_sum, Finset.sum_comm]
  have h2 : ∑ j ∈ Ico 1 n, ∑ k ∈ Ico 1 n, c j * (weight n k * cos ((j : ℝ) * node n k)) =
      c 1 * (-((n : ℝ) + 1) / (2 * cos (alpha n))) := by
    rw [Finset.sum_eq_single 1]
    · rw [← Finset.mul_sum]
      have := sum_weight_cos_one n hn
      simpa using congrArg (c 1 * ·) this
    · intro j hj hj1
      rw [← Finset.mul_sum, sum_weight_cos_eq_zero n j hn _ _]
      · simp
      · have := (Finset.mem_Ico.mp hj).1; omega
      · have := (Finset.mem_Ico.mp hj).2; omega
    · intro h; exact absurd (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩) h
  rw [h2]
  field_simp
  ring

/-- (Q3) -/
theorem coeff_le_of_nonneg_at_nodes (n : ℕ) (hn : 2 ≤ n) (c : ℕ → ℝ)
    (h : ∀ k ∈ Ico 1 n, 0 ≤ c 0 + 2 * ∑ j ∈ Ico 1 n, c j * cos ((j : ℝ) * node n k)) :
    c 1 ≤ c 0 * cos (π / ((n : ℝ) + 1)) := by
  have hc := cos_alpha_pos hn
  have hq := quadrature_sum n hn c
  have hnn : 0 ≤ ∑ k ∈ Ico 1 n, weight n k *
      (c 0 + 2 * ∑ j ∈ Ico 1 n, c j * cos ((j : ℝ) * node n k)) :=
    Finset.sum_nonneg fun k hk => mul_nonneg (weight_pos n hn k hk).le (h k hk)
  rw [hq] at hnn
  have h1 : 0 ≤ c 0 - c 1 / cos (alpha n) := by
    by_contra hneg
    push Not at hneg
    have : ((n : ℝ) + 1) * (c 0 - c 1 / cos (alpha n)) < 0 :=
      mul_neg_of_pos_of_neg (by positivity) hneg
    linarith
  have h2 : c 1 / cos (alpha n) ≤ c 0 := by linarith
  rw [div_le_iff₀ hc] at h2
  exact h2

/-! ### Fejér positivity -/

/-- The term `c d cos (d θ)`. -/
noncomputable def ftTerm (c : ℤ → ℝ) (θ : ℝ) (d : ℤ) : ℝ := c d * cos ((d : ℝ) * θ)

/-- The double sum `Σ_{j,l<N} c(j-l) cos((j-l)θ)`. -/
noncomputable def ftSum (c : ℤ → ℝ) (θ : ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ range N, ∑ l ∈ range N, ftTerm c θ ((j : ℤ) - (l : ℤ))

lemma ftSum_succ (c : ℤ → ℝ) (θ : ℝ) (heven : ∀ k, c (-k) = c k) (N : ℕ) :
    ftSum c θ (N + 1) = ftSum c θ N + ftTerm c θ 0 +
      2 * ∑ l ∈ range N, ftTerm c θ ((N : ℤ) - (l : ℤ)) := by
  have hev : ∀ d, ftTerm c θ (-d) = ftTerm c θ d := fun d => by
    simp [ftTerm, heven, cos_neg]
  unfold ftSum
  rw [Finset.sum_range_succ]
  simp only [Finset.sum_range_succ _ N, Finset.sum_add_distrib]
  have h1 : ∑ x ∈ range N, ftTerm c θ ((x : ℤ) - (N : ℤ)) =
      ∑ l ∈ range N, ftTerm c θ ((N : ℤ) - (l : ℤ)) :=
    Finset.sum_congr rfl fun x _ => by rw [← hev]; congr 1; ring
  rw [h1, sub_self]; ring

lemma ftSum_row (c : ℤ → ℝ) (θ : ℝ) (n N : ℕ) (hsupp : ∀ k : ℤ, n ≤ k.natAbs → c k = 0)
    (hN : n ≤ N) :
    ∑ l ∈ range N, ftTerm c θ ((N : ℤ) - (l : ℤ)) = ∑ d ∈ Ico 1 n, ftTerm c θ (d : ℤ) := by
  have hz : ∀ d : ℤ, n ≤ d.natAbs → ftTerm c θ d = 0 := fun d hd => by simp [ftTerm, hsupp d hd]
  have h1 : ∑ l ∈ range N, ftTerm c θ ((N : ℤ) - (l : ℤ)) =
      ∑ l ∈ range N, ftTerm c θ (((l + 1 : ℕ) : ℤ)) := by
    rw [← Finset.sum_range_reflect (fun l : ℕ => ftTerm c θ (((l + 1 : ℕ) : ℤ))) N]
    refine Finset.sum_congr rfl fun l hl => ?_
    have := Finset.mem_range.mp hl
    congr 1; omega
  rw [h1]
  have h2 : ∑ l ∈ range N, ftTerm c θ (((l + 1 : ℕ) : ℤ)) =
      ∑ l ∈ range (n - 1), ftTerm c θ (((l + 1 : ℕ) : ℤ)) := by
    symm
    refine Finset.sum_subset (Finset.range_mono (by omega)) fun l _ hl => hz _ ?_
    have := Finset.mem_range.not.mp hl
    simp only [Int.natAbs_natCast]; omega
  rw [h2, Finset.sum_Ico_eq_sum_range]
  exact Finset.sum_congr rfl fun l _ => by congr 1; push_cast; ring

/-- Fejér positivity from positive semidefiniteness. -/
theorem fejer_nonneg (n : ℕ) (c : ℤ → ℝ) (heven : ∀ k, c (-k) = c k)
    (hsupp : ∀ k : ℤ, n ≤ k.natAbs → c k = 0)
    (hpsd : ∀ (N : ℕ) (x : Fin N → ℝ),
      0 ≤ ∑ j, ∑ l, x j * x l * c (((j : ℕ) : ℤ) - ((l : ℕ) : ℤ))) (θ : ℝ) :
    0 ≤ c 0 + 2 * ∑ j ∈ Ico 1 n, c (j : ℤ) * cos ((j : ℝ) * θ) := by
  have hG : ∀ N, 0 ≤ ftSum c θ N := by
    intro N
    have hfin : ∀ F : ℕ → ℕ → ℝ, ∑ j : Fin N, ∑ l : Fin N, F j l =
        ∑ j ∈ range N, ∑ l ∈ range N, F j l := by
      intro F
      rw [← Fin.sum_univ_eq_sum_range (fun j => ∑ l ∈ range N, F j l) N]
      exact Finset.sum_congr rfl fun j _ => Fin.sum_univ_eq_sum_range (fun l => F (j : ℕ) l) N
    have h1 := hpsd N (fun i => cos ((i : ℕ) * θ))
    have h2 := hpsd N (fun i => sin ((i : ℕ) * θ))
    rw [hfin (fun j l => cos ((j : ℝ) * θ) * cos ((l : ℝ) * θ) * c ((j : ℤ) - (l : ℤ)))] at h1
    rw [hfin (fun j l => sin ((j : ℝ) * θ) * sin ((l : ℝ) * θ) * c ((j : ℤ) - (l : ℤ)))] at h2
    have := add_nonneg h1 h2
    rw [← Finset.sum_add_distrib] at this
    unfold ftSum
    refine this.trans_eq (Finset.sum_congr rfl fun j _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [ftTerm]
    push_cast
    rw [sub_mul, cos_sub]; ring
  set S := ftTerm c θ 0 + 2 * ∑ d ∈ Ico 1 n, ftTerm c θ (d : ℤ) with hS
  have hstep : ∀ m, ftSum c θ (n + m) = ftSum c θ n + m * S := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [← add_assoc, ftSum_succ c θ heven, ih, ftSum_row c θ n (n + m) hsupp (by omega), hS]
      push_cast; ring
  have hS0 : 0 ≤ S := by
    by_contra hneg
    push Not at hneg
    obtain ⟨m, hm⟩ := exists_nat_gt (ftSum c θ n / (-S))
    have := hG (n + m)
    rw [hstep] at this
    rw [div_lt_iff₀ (by linarith)] at hm
    nlinarith
  have : S = c 0 + 2 * ∑ j ∈ Ico 1 n, c (j : ℤ) * cos ((j : ℝ) * θ) := by
    simp [hS, ftTerm]
  rwa [this] at hS0

/-! ### The limit -/

lemma two_mul_sq_one_sub_cos_eq (n : ℕ) :
    2 * (n : ℝ) ^ 2 * (1 - cos (π / ((n : ℝ) + 1))) =
      (2 * n * sin ((π / 2) * (1 / ((n : ℝ) + 1)))) ^ 2 := by
  have h : π / ((n : ℝ) + 1) = 2 * ((π / 2) * (1 / ((n : ℝ) + 1))) := by ring
  rw [h, cos_two_mul]
  have := sin_sq_add_cos_sq ((π / 2) * (1 / ((n : ℝ) + 1)))
  nlinarith

/-- The limit `2 n² (1 - cos (π/(n+1))) → π²`. -/
theorem tendsto_two_mul_sq_one_sub_cos :
    Tendsto (fun n : ℕ => 2 * (n : ℝ) ^ 2 * (1 - cos (π / ((n : ℝ) + 1)))) atTop (𝓝 (π ^ 2)) := by
  have hu : Tendsto (fun n : ℕ => π * ((n : ℝ) / ((n : ℝ) + 1))) atTop (𝓝 π) := by
    simpa using (tendsto_natCast_div_add_atTop (1 : ℝ)).const_mul π
  have hy : Tendsto (fun n : ℕ => (π / 2) * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (π / 2)
  have hl : Tendsto (fun n : ℕ => π * ((n : ℝ) / ((n : ℝ) + 1)) *
      (1 - ((π / 2) * (1 / ((n : ℝ) + 1))) ^ 2 / 4)) atTop (𝓝 π) := by
    have := hu.mul ((tendsto_const_nhds (x := (1 : ℝ))).sub ((hy.pow 2).div_const 4))
    simpa using this
  have ha : Tendsto (fun n : ℕ => 2 * (n : ℝ) * sin ((π / 2) * (1 / ((n : ℝ) + 1)))) atTop (𝓝 π) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hy0 : 0 < (π / 2) * (1 / ((n : ℝ) + 1)) := by positivity
      have := sin_gt_sub_cube hy0
      have e : π * ((n : ℝ) / ((n : ℝ) + 1)) = 2 * n * ((π / 2) * (1 / ((n : ℝ) + 1))) := by
        field_simp
      rw [e]
      have hn0 : (0 : ℝ) ≤ 2 * n := by positivity
      have h3 : 0 ≤ ((π / 2) * (1 / ((n : ℝ) + 1))) ^ 3 := by positivity
      have h4 : (π / 2) * (1 / ((n : ℝ) + 1)) - ((π / 2) * (1 / ((n : ℝ) + 1))) ^ 3 / 4 ≤
          sin ((π / 2) * (1 / ((n : ℝ) + 1))) := by linarith
      have := mul_le_mul_of_nonneg_left h4 hn0
      linarith
    · filter_upwards with n
      have hy0 : 0 ≤ (π / 2) * (1 / ((n : ℝ) + 1)) := by positivity
      have e : π * ((n : ℝ) / ((n : ℝ) + 1)) = 2 * n * ((π / 2) * (1 / ((n : ℝ) + 1))) := by
        field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left (sin_le hy0) (by positivity)
  simpa [two_mul_sq_one_sub_cos_eq] using ha.pow 2

/-- A bound valid for all `n ≥ 2` passes to the limit. -/
theorem ge_pi_sq_mul_of_forall (r s : ℝ)
    (h : ∀ n : ℕ, 2 ≤ n → 2 * (n : ℝ) ^ 2 * (1 - cos (π / ((n : ℝ) + 1))) * s ≤ r) :
    π ^ 2 * s ≤ r :=
  le_of_tendsto (tendsto_two_mul_sq_one_sub_cos.mul_const s)
    (by filter_upwards [eventually_ge_atTop 2] with n hn using h n hn)

end GMCExplicitDelta.Source
