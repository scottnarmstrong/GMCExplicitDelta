module

public import GMCExplicitDelta.Certificates.Group2History
public import GMCExplicitDelta.Certificates.Group2Bad
public import GMCExplicitDelta.Certificates.Group2Averaging
public import GMCExplicitDelta.HistoryLane.Consts
public import GMCExplicitDelta.HistoryLane.Series

/-!
# History lane: the deterministic sums of G5 and G7

* `summable_sinf`, `sum_frakU_le_sinf`, `coarse_sum_le`: the coarse part of G7,
  `(1-w) D ∑_{j≤t} x^j 𝔲_{t-j} ≤ (1-w) D x^t S_∞`.
* `fine_sum_le`: the fine part, `∑_{r=1}^L (1-w) x^r fineCap(r) ≤ (1+η)C₁D + β_d(1+D)(F̄/(2η) + Ḡ)`.
-/

@[expose] public section

open Real

namespace GMCExplicitDelta.Assembly

open GMCExplicitDelta.Contract GMCExplicitDelta.Certificates

variable {d : ℕ}

/-- The ratio bound of `𝔲_ℓ` gives summability of `S_∞`. -/
theorem summable_sinf (row : Row d) {D F : ℝ} (hD : 0 < D) (hF : 0 ≤ F) (hx : 0 < row.xHist)
    (h4 : (3 : ℝ) ^ (-((d : ℝ) / 2)) < row.xHist) :
    Summable (fun ℓ : ℕ => frakU d ℓ D F * row.xHist⁻¹ ^ ℓ) := by
  set y := row.xHist⁻¹ with hy
  have hy0 : 0 < y := inv_pos.2 hx
  set r : ℝ := (3 : ℝ) ^ (-((d : ℝ) / 2)) with hr
  have hr0 : 0 < r := by positivity
  have hr2 : 1 ≤ r ^ 2 * ((3 ^ d : ℕ) : ℝ) := by
    have : r ^ 2 = ((3 : ℝ) ^ d)⁻¹ := by
      rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      rw [show (-((d : ℝ) / 2)) * ((2 : ℕ) : ℝ) = -(d : ℝ) by push_cast; ring, Real.rpow_neg
        (by norm_num), Real.rpow_natCast]
    rw [this]; push_cast
    have : (0 : ℝ) < (3 : ℝ) ^ d := by positivity
    rw [inv_mul_cancel₀ this.ne']
  have hry : r * y < 1 := by
    have : r < row.xHist := h4
    rw [hy, ← div_eq_mul_inv, div_lt_one hx]; exact this
  have hU : (sigmaNorm d : ℝ) * Bbar32 (3 ^ (d * 0)) D F ≤ (sigmaNorm d : ℝ) * Bbar32 (3 ^ (d * 0)) D F :=
    le_rfl
  have hterm : ∀ j : ℕ, frakU d (0 + 1 + j) D F * y ^ (0 + 1 + j) ≤
      ((sigmaNorm d : ℝ) * Bbar32 (3 ^ (d * 0)) D F * y ^ (0 + 1)) * (r * y) ^ j := fun j => by
    have h1 := frakU_tail (d := d) hD hF 0 hr0.le hr2 hU j
    calc frakU d (0 + 1 + j) D F * y ^ (0 + 1 + j)
        ≤ (r ^ j * ((sigmaNorm d : ℝ) * Bbar32 (3 ^ (d * 0)) D F)) * y ^ (0 + 1 + j) := by gcongr
      _ = _ := by ring
  have hg : Summable (fun j : ℕ =>
      ((sigmaNorm d : ℝ) * Bbar32 (3 ^ (d * 0)) D F * y ^ (0 + 1)) * (r * y) ^ j) :=
    (summable_geometric_of_lt_one (by positivity) hry).mul_left _
  have hs : Summable (fun j : ℕ => frakU d (0 + 1 + j) D F * y ^ (0 + 1 + j)) :=
    Summable.of_nonneg_of_le (fun j => mul_nonneg (frakU_nonneg d _ hD hF) (by positivity)) hterm hg
  have hs' : Summable (fun j : ℕ => (fun ℓ : ℕ => frakU d ℓ D F * y ^ ℓ) (j + 1)) := by
    simpa [add_comm] using hs
  exact (summable_nat_add_iff 1).mp hs'

theorem sum_frakU_le_sinf (row : Row d) {D F : ℝ} (hD : 0 < D) (hF : 0 ≤ F) (hx : 0 < row.xHist)
    (h4 : (3 : ℝ) ^ (-((d : ℝ) / 2)) < row.xHist) (n : ℕ) :
    ∑ ℓ ∈ Finset.range n, frakU d ℓ D F * row.xHist⁻¹ ^ ℓ ≤ row.Sinf D F := by
  unfold Row.Sinf
  exact (summable_sinf row hD hF hx h4).sum_le_tsum _
    (fun ℓ _ => mul_nonneg (frakU_nonneg d ℓ hD hF) (pow_nonneg (inv_pos.2 hx).le _))

/-- Coarse part of G7: `∑_{j≤t} x^j 𝔲_{t-j} ≤ x^t S_∞`. -/
theorem coarse_sum_le (row : Row d) {D F : ℝ} (hD : 0 < D) (hF : 0 ≤ F) (hx : 0 < row.xHist)
    (h4 : (3 : ℝ) ^ (-((d : ℝ) / 2)) < row.xHist) (t : ℕ) :
    ∑ j ∈ Finset.range (t + 1), row.xHist ^ j * frakU d (t - j) D F ≤
      row.xHist ^ t * row.Sinf D F := by
  have h := sum_frakU_le_sinf row hD hF hx h4 (t + 1)
  have e : ∀ j ∈ Finset.range (t + 1), row.xHist ^ j * frakU d (t - j) D F =
      row.xHist ^ t * (frakU d (t - j) D F * row.xHist⁻¹ ^ (t - j)) := by
    intro j hj
    have hj' : j ≤ t := by simpa [Nat.lt_succ_iff] using hj
    have : row.xHist ^ t = row.xHist ^ j * row.xHist ^ (t - j) := by
      rw [← pow_add]; congr 1; omega
    rw [this, inv_pow]
    field_simp
  rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hx.le _)
  rw [← Finset.sum_range_reflect] at h
  convert h using 2 with j hj
  have hj' : j < t + 1 := Finset.mem_range.1 hj
  congr 2 <;> omega

end GMCExplicitDelta.Assembly
