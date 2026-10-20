module

public import GMCExplicitDelta.Contract.DerivedGeometry
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Algebra.Field.GeomSum

/-! H14: the exact geometric minimum series used by the contract layer. -/
@[expose] public section

namespace GMCExplicitDelta.Haar

open Contract
open scoped BigOperators

theorem minSeries_summable {q Λ H : ℝ} (hq0 : 0 ≤ q) (hq9 : q < 9)
    (hΛ : 0 ≤ Λ) (hH : 0 ≤ H) :
    Summable (fun j : ℕ => q ^ j * min Λ (H / 9 ^ j)) := by
  have hr0 : 0 ≤ q / 9 := div_nonneg hq0 (by norm_num)
  have hr1 : q / 9 < 1 := (div_lt_one (by norm_num : (0 : ℝ) < 9)).2 hq9
  apply ((summable_geometric_of_lt_one hr0 hr1).mul_left H).of_norm_bounded
  intro j
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (pow_nonneg hq0 j) (le_min hΛ (div_nonneg hH (by positivity))))]
  calc
    q ^ j * min Λ (H / 9 ^ j) ≤ q ^ j * (H / 9 ^ j) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) (pow_nonneg hq0 j)
    _ = H * (q / 9) ^ j := by rw [div_pow]; ring

/-- Closed form with the crossing index characterized explicitly. -/
theorem minSeries_eq_of_crossing {q Λ H : ℝ} (hq1 : 1 < q) (hq9 : q < 9)
    (hΛ : 0 ≤ Λ) (hH : 0 ≤ H) (J : ℕ)
    (hbefore : ∀ j < J, Λ ≤ H / 9 ^ j) (hcross : H / 9 ^ J ≤ Λ) :
    minSeries q Λ H = Λ * (q ^ J - 1) / (q - 1) +
      H * (q / 9) ^ J / (1 - q / 9) := by
  have hq0 : 0 ≤ q := le_trans zero_le_one hq1.le
  have hs := minSeries_summable hq0 hq9 hΛ hH
  have hsplit := hs.sum_add_tsum_nat_add J
  unfold minSeries
  rw [← hsplit]
  have hfinite : (∑ j ∈ Finset.range J, q ^ j * min Λ (H / 9 ^ j)) =
      Λ * (q ^ J - 1) / (q - 1) := by
    calc
      (∑ j ∈ Finset.range J, q ^ j * min Λ (H / 9 ^ j)) =
          ∑ j ∈ Finset.range J, Λ * q ^ j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [min_eq_left (hbefore j (Finset.mem_range.mp hj)), mul_comm]
      _ = Λ * (q ^ J - 1) / (q - 1) := by
        rw [← Finset.mul_sum, geom_sum_eq (ne_of_gt hq1)]
        ring
  rw [hfinite]
  congr 1
  have htail : ∀ j : ℕ, q ^ (j + J) * min Λ (H / 9 ^ (j + J)) =
      (H * (q / 9) ^ J) * (q / 9) ^ j := by
    intro j
    have hle : H / 9 ^ (j + J) ≤ Λ := by
      apply le_trans _ hcross
      apply div_le_div_of_nonneg_left hH (by positivity)
      exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 9) (Nat.le_add_left J j)
    rw [min_eq_right hle, div_pow, div_pow, pow_add, pow_add]
    ring
  simp_rw [htail]
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity : 0 ≤ q / 9)
    ((div_lt_one (by norm_num : (0 : ℝ) < 9)).2 hq9)]
  ring

/-- The geometric profile eventually crosses every positive level. -/
theorem exists_minSeries_crossing (Λ H : ℝ) (hΛ : 0 < Λ) :
    ∃ j : ℕ, H / 9 ^ j ≤ Λ := by
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (H / Λ) (by norm_num : (1 : ℝ) < 9)
  refine ⟨j, (div_le_iff₀ (by positivity : (0 : ℝ) < 9 ^ j)).2 ?_⟩
  have h := (div_lt_iff₀ hΛ).1 hj
  exact (by simpa only [mul_comm] using h.le)

/-- The least crossing index J in H14. -/
noncomputable def minSeriesIndex (Λ H : ℝ) (hΛ : 0 < Λ) : ℕ :=
  Nat.find (exists_minSeries_crossing Λ H hΛ)

theorem minSeries_eq_closed {q Λ H : ℝ} (hq1 : 1 < q) (hq9 : q < 9)
    (hΛ : 0 < Λ) (hH : 0 < H) :
    minSeries q Λ H = Λ * (q ^ minSeriesIndex Λ H hΛ - 1) / (q - 1) +
      H * (q / 9) ^ minSeriesIndex Λ H hΛ / (1 - q / 9) := by
  apply minSeries_eq_of_crossing hq1 hq9 hΛ.le hH.le
  · intro j hj
    exact le_of_lt (lt_of_not_ge (Nat.find_min (exists_minSeries_crossing Λ H hΛ) hj))
  · exact Nat.find_spec (exists_minSeries_crossing Λ H hΛ)

/-- Split upper bound at any depth; no crossing hypothesis is needed. -/
theorem minSeries_le_split {q Λ H : ℝ} (hq1 : 1 < q) (hq9 : q < 9)
    (hΛ : 0 ≤ Λ) (hH : 0 ≤ H) (J : ℕ) :
    minSeries q Λ H ≤ Λ * (q ^ J - 1) / (q - 1) +
      H * (q / 9) ^ J / (1 - q / 9) := by
  have hq0 : 0 ≤ q := le_trans zero_le_one hq1.le
  have hr0 : 0 ≤ q / 9 := by positivity
  have hr1 : q / 9 < 1 := (div_lt_one (by norm_num : (0 : ℝ) < 9)).2 hq9
  have hs := minSeries_summable hq0 hq9 hΛ hH
  have ht : Summable (fun j : ℕ => H * (q / 9) ^ J * (q / 9) ^ j) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  unfold minSeries
  rw [← hs.sum_add_tsum_nat_add J]
  apply add_le_add
  · calc
      (∑ j ∈ Finset.range J, q ^ j * min Λ (H / 9 ^ j)) ≤
          ∑ j ∈ Finset.range J, Λ * q ^ j := by
        apply Finset.sum_le_sum
        intro j _
        simpa only [mul_comm Λ] using
          mul_le_mul_of_nonneg_left (min_le_left Λ (H / 9 ^ j)) (pow_nonneg hq0 j)
      _ = Λ * (q ^ J - 1) / (q - 1) := by
        rw [← Finset.mul_sum, geom_sum_eq (ne_of_gt hq1)]
        ring
  · calc
      (∑' j : ℕ, q ^ (j + J) * min Λ (H / 9 ^ (j + J))) ≤
          ∑' j : ℕ, H * (q / 9) ^ J * (q / 9) ^ j := by
        apply ((summable_nat_add_iff J).2 hs).tsum_le_tsum _ ht
        intro j
        calc
          q ^ (j + J) * min Λ (H / 9 ^ (j + J)) ≤
              q ^ (j + J) * (H / 9 ^ (j + J)) :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) (pow_nonneg hq0 _)
          _ = H * (q / 9) ^ J * (q / 9) ^ j := by
            rw [div_pow, div_pow, pow_add, pow_add]
            ring
      _ = H * (q / 9) ^ J / (1 - q / 9) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
        ring

end GMCExplicitDelta.Haar
