module

public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Rational enclosures

* `π` from `Real.pi_gt_d20` / `Real.pi_lt_d20`;
* `Real.exp q` by Taylor partial sums plus the `Real.exp_bound` remainder (both directions);
* `Real.log 2`, `Real.log 3` to 15 digits, via the exp enclosures;
* `Real.sqrt` via rational squares.
-/

@[expose] public section

namespace GMCNumerics

open Real

/-! ### π -/

theorem pi_enclosure : (3.14159265358979323846 : ℝ) < π ∧ π < 3.14159265358979323847 :=
  ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩

/-! ### exp -/

/-- Taylor partial sum of `exp q` with `n` terms. -/
noncomputable def expPoly (q : ℝ) (n : ℕ) : ℝ := ∑ m ∈ Finset.range n, q ^ m / m.factorial

/-- Remainder bound from `Real.exp_bound`. -/
noncomputable def expErr (q : ℝ) (n : ℕ) : ℝ :=
  |q| ^ n * ((n.succ : ℝ) / (n.factorial * n))

theorem exp_enclosure {q : ℝ} (hq : |q| ≤ 1) {n : ℕ} (hn : 0 < n) :
    expPoly q n - expErr q n ≤ Real.exp q ∧ Real.exp q ≤ expPoly q n + expErr q n := by
  have h := Real.exp_bound hq hn
  rw [abs_le] at h
  unfold expPoly expErr
  constructor <;> linarith [h.1, h.2]

theorem exp_le_of_poly {q y : ℝ} (hq : |q| ≤ 1) {n : ℕ} (hn : 0 < n)
    (h : expPoly q n + expErr q n ≤ y) : Real.exp q ≤ y :=
  (exp_enclosure hq hn).2.trans h

theorem le_exp_of_poly {q y : ℝ} (hq : |q| ≤ 1) {n : ℕ} (hn : 0 < n)
    (h : y ≤ expPoly q n - expErr q n) : y ≤ Real.exp q :=
  h.trans (exp_enclosure hq hn).1

/-- Reduction of large arguments: `exp q = (exp (q / m)) ^ m`. -/
theorem exp_eq_pow_div (q : ℝ) {m : ℕ} (hm : 0 < m) : Real.exp q = Real.exp (q / m) ^ m := by
  rw [← Real.exp_nat_mul]
  congr 1
  field_simp

theorem exp_bounds_of_div {q lo hi : ℝ} {m : ℕ} (hm : 0 < m) (hlo0 : 0 ≤ lo)
    (hlo : lo ≤ Real.exp (q / m)) (hhi : Real.exp (q / m) ≤ hi) :
    lo ^ m ≤ Real.exp q ∧ Real.exp q ≤ hi ^ m := by
  rw [exp_eq_pow_div q hm]
  exact ⟨pow_le_pow_left₀ hlo0 hlo m, pow_le_pow_left₀ (Real.exp_pos _).le hhi m⟩

/-- Example: `exp (1/2)`. -/
theorem exp_half_enclosure :
    (1.6487212707001281 : ℝ) < Real.exp (1 / 2) ∧ Real.exp (1 / 2) < 1.6487212707001283 := by
  have hq : |(1 / 2 : ℝ)| ≤ 1 := by rw [abs_of_pos (by norm_num)]; norm_num
  constructor
  · refine lt_of_lt_of_le ?_ (le_exp_of_poly (n := 20) hq (by norm_num) le_rfl)
    norm_num [expPoly, expErr, Finset.sum_range_succ, Nat.factorial, abs_of_pos]
  · refine lt_of_le_of_lt (exp_le_of_poly (n := 20) hq (by norm_num) le_rfl) ?_
    norm_num [expPoly, expErr, Finset.sum_range_succ, Nat.factorial, abs_of_pos]

/-- Example: `exp (-1)` is below `0.36787944117145`. -/
theorem exp_neg_one_enclosure :
    (0.36787944117143 : ℝ) < Real.exp (-1) ∧ Real.exp (-1) < 0.36787944117145 := by
  have hq : |(-1 : ℝ)| ≤ 1 := by norm_num
  constructor
  · refine lt_of_lt_of_le ?_ (le_exp_of_poly (n := 20) hq (by norm_num) le_rfl)
    norm_num [expPoly, expErr, Finset.sum_range_succ, Nat.factorial]
  · refine lt_of_le_of_lt (exp_le_of_poly (n := 20) hq (by norm_num) le_rfl) ?_
    norm_num [expPoly, expErr, Finset.sum_range_succ, Nat.factorial]

/-! ### log -/

theorem le_log_of_exp_le {a y : ℝ} (hy : 0 < y) (h : Real.exp a ≤ y) : a ≤ Real.log y :=
  (Real.le_log_iff_exp_le hy).2 h

theorem log_le_of_le_exp {b y : ℝ} (hy : 0 < y) (h : y ≤ Real.exp b) : Real.log y ≤ b :=
  (Real.log_le_iff_le_exp hy).2 h

/-- `log 2` to 15 digits. -/
theorem log_two_enclosure :
    (0.693147180559945 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 0.693147180559946 := by
  have h1 : |(0.693147180559945 : ℝ)| ≤ 1 := by rw [abs_of_pos (by norm_num)]; norm_num
  have h2 : |(0.693147180559946 : ℝ)| ≤ 1 := by rw [abs_of_pos (by norm_num)]; norm_num
  constructor
  · refine le_log_of_exp_le (by norm_num) (exp_le_of_poly (n := 24) h1 (by norm_num) ?_)
    norm_num [expPoly, expErr, Finset.sum_range_succ, Nat.factorial, abs_of_pos]
  · refine log_le_of_le_exp (by norm_num) (le_exp_of_poly (n := 24) h2 (by norm_num) ?_)
    norm_num [expPoly, expErr, Finset.sum_range_succ, Nat.factorial, abs_of_pos]

/-- `log (3/2)` to 15 digits. -/
theorem log_three_halves_enclosure :
    (0.405465108108164 : ℝ) ≤ Real.log (3 / 2) ∧ Real.log (3 / 2) ≤ 0.405465108108165 := by
  have h1 : |(0.405465108108164 : ℝ)| ≤ 1 := by rw [abs_of_pos (by norm_num)]; norm_num
  have h2 : |(0.405465108108165 : ℝ)| ≤ 1 := by rw [abs_of_pos (by norm_num)]; norm_num
  constructor
  · refine le_log_of_exp_le (by norm_num) (exp_le_of_poly (n := 24) h1 (by norm_num) ?_)
    norm_num [expPoly, expErr, Finset.sum_range_succ, Nat.factorial, abs_of_pos]
  · refine log_le_of_le_exp (by norm_num) (le_exp_of_poly (n := 24) h2 (by norm_num) ?_)
    norm_num [expPoly, expErr, Finset.sum_range_succ, Nat.factorial, abs_of_pos]

/-- `log 3` to 15 digits (via `log 3 = log 2 + log (3/2)`). -/
theorem log_three_enclosure :
    (1.098612288668109 : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ 1.098612288668111 := by
  have e : Real.log 3 = Real.log 2 + Real.log (3 / 2) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  obtain ⟨a1, a2⟩ := log_two_enclosure
  obtain ⟨b1, b2⟩ := log_three_halves_enclosure
  rw [e]
  constructor <;> linarith

/-! ### sqrt -/

theorem sqrt_enclosure {x a b : ℝ} (hb : 0 ≤ b) (h1 : a ^ 2 ≤ x) (h2 : x ≤ b ^ 2) :
    a ≤ Real.sqrt x ∧ Real.sqrt x ≤ b :=
  ⟨Real.le_sqrt_of_sq_le h1, Real.sqrt_le_iff.2 ⟨hb, h2⟩⟩

/-- Example: `√2`. -/
theorem sqrt_two_enclosure :
    (1.41421356237309 : ℝ) ≤ Real.sqrt 2 ∧ Real.sqrt 2 ≤ 1.4142135623731 :=
  sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)

end GMCNumerics
