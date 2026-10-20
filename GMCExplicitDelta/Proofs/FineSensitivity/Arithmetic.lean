module

public import GMCExplicitDelta.Proofs.FineSensitivity.ShiftedBounds

/-! # Contract arithmetic for the G4 shifted moments -/

@[expose] public section

open scoped NNReal

namespace GMCExplicitDelta.Assembly

/-- Squaring the Hölder amplitude yields exactly the `varsigma` factor. -/
theorem fineAmplitude_sq (a : ℝ≥0) :
    fineAmplitude a ^ 2 = 2 * (a : ℝ) * Contract.P32 * Contract.varsigma := by
  have hP : 0 ≤ Contract.P32 := by unfold Contract.P32; positivity
  unfold fineAmplitude
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hP]
  have he : ((2 : ℝ) ^ (128 : ℝ)⁻¹) ^ 2 = Contract.varsigma := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    norm_num [Contract.varsigma]
  rw [he]

/-- Fresh-band polynomial bound: `r^(3/2) ≤ r²` is used through squaring. -/
theorem fine_shift_polynomial_le {d : ℕ} {δ r S c : ℝ}
    (hδ : 0 ≤ δ) (hr : 1 ≤ r) (hS : 0 ≤ S)
    (hS2 : S ^ 2 = Contract.Ch * r * δ ^ 2)
    (hc : |c| ≤ Contract.kappaH d * r * δ ^ 2) :
    (S + |c|) ^ 2 ≤ Contract.Ch * r * δ ^ 2 + Contract.AF d δ * r ^ 2 := by
  have hCh : 0 ≤ Contract.Ch := by
    unfold Contract.Ch Contract.proxyA Contract.P32 Contract.varsigma
    positivity
  have hκ : 0 ≤ Contract.kappaH d := by
    unfold Contract.kappaH Contract.kappaQ1
    split_ifs <;> norm_num
  have hB : 0 ≤ Contract.kappaH d * r * δ ^ 2 := by positivity
  have hsqrt := Real.sq_sqrt hCh
  have hSr : S ≤ Real.sqrt Contract.Ch * r * δ := by
    apply (sq_le_sq₀ hS (by positivity)).mp
    rw [mul_pow, mul_pow, hsqrt, hS2]
    have hrr : r ≤ r ^ 2 := by nlinarith only [hr]
    have hm := mul_le_mul_of_nonneg_left hrr (mul_nonneg hCh (sq_nonneg δ))
    nlinarith only [hm]
  have hcross := mul_le_mul_of_nonneg_right hSr hB
  have hsq := (sq_le_sq₀ (add_nonneg hS (abs_nonneg c)) (add_nonneg hS hB)).mpr
    (add_le_add le_rfl hc)
  unfold Contract.AF
  nlinarith only [hsq, hS2, hcross]

/-- The symmetric-increment polynomial supplied by the contract is no smaller. -/
theorem fine_AF_le_AG (d : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    Contract.AF d δ ≤ Contract.AG d δ := by
  have hCh : 0 ≤ Contract.Ch := by
    unfold Contract.Ch Contract.proxyA Contract.P32 Contract.varsigma
    positivity
  have hκ : 0 ≤ Contract.kappaH d := by
    unfold Contract.kappaH Contract.kappaQ1
    split_ifs <;> norm_num
  have hv : 1 ≤ Contract.varsigma := by
    unfold Contract.varsigma
    exact Real.one_le_rpow (by norm_num) (by norm_num)
  have hv2 : 1 ≤ Contract.varsigma ^ 2 := by nlinarith only [hv]
  have h1 := mul_le_mul_of_nonneg_left hv
    (show 0 ≤ 2 * Contract.kappaH d * Real.sqrt Contract.Ch * δ ^ 3 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hv2
    (show 0 ≤ Contract.kappaH d ^ 2 * δ ^ 4 by positivity)
  unfold Contract.AF Contract.AG
  nlinarith only [h1, h2]

end GMCExplicitDelta.Assembly
