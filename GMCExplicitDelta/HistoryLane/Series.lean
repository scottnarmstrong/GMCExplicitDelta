module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# History lane: geometric moment series (G5)

`∑ r z^r = z/(1-z)²` and `∑ r² z^r = z(1+z)/(1-z)³`, and the finite partial sums of the series of G5.
-/

@[expose] public section

namespace GMCExplicitDelta.HistoryLane

theorem hasSum_sq_mul_geometric {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    HasSum (fun n : ℕ => (n : ℝ) ^ 2 * z ^ n) (z * (1 + z) / (1 - z) ^ 3) := by
  have hn : ‖z‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hz0]; exact hz1
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one hn
  have h0 := hasSum_geometric_of_lt_one hz0 hz1
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ 2 * z ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 2 hn
  set S2 := ∑' n : ℕ, (n : ℝ) ^ 2 * z ^ n with hS2
  have hf : HasSum (fun n : ℕ => (n : ℝ) ^ 2 * z ^ n) S2 := hs.hasSum
  have h2 : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 2 * z ^ (n + 1)) S2 := by
    simpa using (hasSum_nat_add_iff' 1).mpr hf
  have h3 := ((hf.add (h1.mul_left 2)).add h0).mul_left z
  have heq : (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 2 * z ^ (n + 1)) =
      fun n : ℕ => z * ((n : ℝ) ^ 2 * z ^ n + 2 * ((n : ℝ) * z ^ n) + z ^ n) := by
    funext n; push_cast; ring
  rw [heq] at h2
  have hval := h2.unique h3
  have h1z : (1 - z) ≠ 0 := (sub_pos.mpr hz1).ne'
  have : S2 = z * (1 + z) / (1 - z) ^ 3 := by
    field_simp at hval ⊢
    nlinarith [hval]
  rw [this] at hf
  exact hf

theorem sum_mul_geometric_le {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) (L : ℕ) :
    ∑ r ∈ Finset.range L, ((r + 1 : ℕ) : ℝ) * z ^ (r + 1) ≤ z / (1 - z) ^ 2 := by
  have hn : ‖z‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hz0]; exact hz1
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one hn
  have := sum_le_hasSum (Finset.range (L + 1)) (fun i _ => by positivity) h1
  rw [Finset.sum_range_succ' (fun n : ℕ => (n : ℝ) * z ^ n)] at this
  simpa using this

theorem sum_sq_mul_geometric_le {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) (L : ℕ) :
    ∑ r ∈ Finset.range L, ((r + 1 : ℕ) : ℝ) ^ 2 * z ^ (r + 1) ≤ z * (1 + z) / (1 - z) ^ 3 := by
  have h1 := hasSum_sq_mul_geometric hz0 hz1
  have := sum_le_hasSum (Finset.range (L + 1)) (fun i _ => by positivity) h1
  rw [Finset.sum_range_succ' (fun n : ℕ => (n : ℝ) ^ 2 * z ^ n)] at this
  simpa using this

/-- The partial sums of the series of G5. -/
theorem fine_series_le {z C A : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) (hC : 0 ≤ C) (hA : 0 ≤ A) (L : ℕ) :
    ∑ r ∈ Finset.range L,
        z ^ (r + 1) * (C * ((r + 1 : ℕ) : ℝ) + A * ((r + 1 : ℕ) : ℝ) ^ 2) ≤
      C * (z / (1 - z) ^ 2) + A * (z * (1 + z) / (1 - z) ^ 3) := by
  have e : ∀ r : ℕ, z ^ (r + 1) * (C * ((r + 1 : ℕ) : ℝ) + A * ((r + 1 : ℕ) : ℝ) ^ 2) =
      C * (((r + 1 : ℕ) : ℝ) * z ^ (r + 1)) + A * (((r + 1 : ℕ) : ℝ) ^ 2 * z ^ (r + 1)) := by
    intro r; ring
  simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum]
  exact add_le_add (mul_le_mul_of_nonneg_left (sum_mul_geometric_le hz0 hz1 L) hC)
    (mul_le_mul_of_nonneg_left (sum_sq_mul_geometric_le hz0 hz1 L) hA)

end GMCExplicitDelta.HistoryLane
