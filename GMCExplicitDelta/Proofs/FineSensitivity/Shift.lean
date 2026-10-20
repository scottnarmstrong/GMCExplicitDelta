module

public import GMCExplicitDelta.Proofs.FineSensitivity.Band
public import GMCExplicitDelta.HistoryLane.Norm

/-! # Pointwise exponential estimates for the shifted fresh ratio -/

@[expose] public section

namespace GMCExplicitDelta.Assembly

/-- The exponential increment bound used before Hölder in G4. -/
theorem fine_abs_exp_sub_one_le (z : ℝ) :
    |Real.exp z - 1| ≤ |z| * Real.exp |z| := by
  by_cases hz : 0 ≤ z
  · rw [abs_of_nonneg hz, abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp_iff.mpr hz))]
    have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-z)) (Real.exp_pos z).le
    have he : Real.exp (-z) * Real.exp z = 1 := by rw [← Real.exp_add]; simp
    rw [he] at h
    linarith only [h]
  · have hzn : z ≤ 0 := le_of_not_ge hz
    rw [abs_of_nonpos hzn, abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_one_iff.mpr hzn))]
    have h := Real.add_one_le_exp z
    have he := mul_le_mul_of_nonneg_left (Real.one_le_exp_iff.mpr (neg_nonneg.mpr hzn))
      (neg_nonneg.mpr hzn)
    linarith only [h, he]

/-- The squared exponential increment is bounded by a polynomial times an absolute exponential. -/
theorem fine_exp_increment_sq_le (z : ℝ) :
    (Real.exp z - 1) ^ 2 ≤ z ^ 2 * Real.exp (2 * |z|) := by
  have h := pow_le_pow_left₀ (abs_nonneg _) (fine_abs_exp_sub_one_le z) 2
  simpa only [sq_abs, mul_pow, ← Real.exp_nat_mul, Nat.cast_ofNat] using h

/-- The symmetric exponential increment uses half the exponential rate. -/
theorem fine_exp_symmetric_le (z : ℝ) :
    Real.exp z + Real.exp (-z) - 2 ≤ z ^ 2 * Real.exp |z| := by
  have hpos : 0 ≤ |z| := abs_nonneg z
  have h := mul_le_mul_of_nonneg_right (fine_exp_increment_sq_le |z|)
    (Real.exp_pos (-|z|)).le
  have hprod : Real.exp |z| * Real.exp (-|z|) = 1 := by rw [← Real.exp_add]; simp
  have h2prod : Real.exp (2 * |z|) * Real.exp (-|z|) = Real.exp |z| := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [abs_of_nonneg hpos, mul_assoc, h2prod, sq_abs] at h
  have he : (Real.exp |z| - 1) ^ 2 * Real.exp (-|z|) =
      Real.exp |z| + Real.exp (-|z|) - 2 := by
    calc
      _ = Real.exp |z| * (Real.exp |z| * Real.exp (-|z|)) -
          2 * (Real.exp |z| * Real.exp (-|z|)) + Real.exp (-|z|) := by ring
      _ = _ := by rw [hprod]; ring
  rw [he] at h
  rcases le_total 0 z with hz | hz
  · simpa only [abs_of_nonneg hz] using h
  · simpa only [abs_of_nonpos hz, neg_neg, add_comm] using h

/-- Decomposing a deterministic shift of an exponential increment. -/
theorem fine_shift_increment_le (z c : ℝ) :
    |Real.exp (z - c) - 1| ≤
      Real.exp |c| * (|Real.exp z - 1| + |c|) := by
  have he : Real.exp (z - c) - 1 =
      Real.exp (-c) * (Real.exp z - 1) + (Real.exp (-c) - 1) := by
    rw [Real.exp_sub, Real.exp_neg]
    ring
  rw [he]
  calc
    _ ≤ |Real.exp (-c) * (Real.exp z - 1)| + |Real.exp (-c) - 1| := abs_add_le _ _
    _ ≤ Real.exp |c| * |Real.exp z - 1| + |c| * Real.exp |c| := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact add_le_add (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_abs c))
        (abs_nonneg _)) (by simpa only [abs_neg] using fine_abs_exp_sub_one_le (-c))
    _ = _ := by ring

/-- The symmetric increment is the square of a difference of half exponentials. -/
theorem fine_exp_half_diff_sq (z : ℝ) :
    (Real.exp (z / 2) - Real.exp (-z / 2)) ^ 2 =
      Real.exp z + Real.exp (-z) - 2 := by
  have h1 : Real.exp (z / 2) ^ 2 = Real.exp z := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have h2 : Real.exp (-z / 2) ^ 2 = Real.exp (-z) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have h3 : Real.exp (z / 2) * Real.exp (-z / 2) = 1 := by
    rw [← Real.exp_add]; convert Real.exp_zero using 1; congr 1; ring
  nlinarith only [h1, h2, h3]

/-- Square-root form of the symmetric increment estimate. -/
theorem fine_abs_exp_half_diff_le (z : ℝ) :
    |Real.exp (z / 2) - Real.exp (-z / 2)| ≤ |z| * Real.exp (|z| / 2) := by
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)).mp
  rw [sq_abs, fine_exp_half_diff_sq, mul_pow, ← Real.exp_nat_mul, sq_abs]
  convert fine_exp_symmetric_le z using 1
  congr 2
  ring

/-- Deterministic shift of the square-root symmetric increment. -/
theorem fine_shift_symmetric_le (z c : ℝ) :
    |Real.exp ((z - c) / 2) - Real.exp (-(z - c) / 2)| ≤
      Real.exp (|c| / 2) * (|Real.exp (z / 2) - Real.exp (-z / 2)| +
        |c| * Real.exp (-z / 2)) := by
  have he : Real.exp ((z - c) / 2) - Real.exp (-(z - c) / 2) =
      Real.exp (-c / 2) * (Real.exp (z / 2) - Real.exp (-z / 2)) +
        (Real.exp (-c / 2) - Real.exp (c / 2)) * Real.exp (-z / 2) := by
    have h1 : (z - c) / 2 = -c / 2 + z / 2 := by ring
    have h2 : -(z - c) / 2 = c / 2 + -z / 2 := by ring
    rw [h1, h2, Real.exp_add, Real.exp_add]
    ring
  rw [he]
  calc
    _ ≤ |Real.exp (-c / 2) * (Real.exp (z / 2) - Real.exp (-z / 2))| +
        |(Real.exp (-c / 2) - Real.exp (c / 2)) * Real.exp (-z / 2)| := abs_add_le _ _
    _ ≤ Real.exp (|c| / 2) * |Real.exp (z / 2) - Real.exp (-z / 2)| +
        (|c| * Real.exp (|c| / 2)) * Real.exp (-z / 2) := by
      simp only [abs_mul, abs_of_pos (Real.exp_pos _)]
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
          (div_le_div_of_nonneg_right (neg_le_abs c) (by norm_num))) (abs_nonneg _)
      · exact mul_le_mul_of_nonneg_right (by
          rw [abs_sub_comm]
          exact fine_abs_exp_half_diff_le c) (Real.exp_pos _).le
    _ = _ := by ring

end GMCExplicitDelta.Assembly
