module

public import GMCExplicitDelta.Insertion.FreshBandOperator
public import GMCExplicitDelta.Insertion.CoshGenerator

/-! # Scalar hyperbolic moment transfer with the band majorant (I2–I4, K2) -/

@[expose] public section

open MeasureTheory Polynomial

namespace GMCExplicitDelta.Insertion

/-- The scalar moment transfer needed for the affine seed, with the exact contract series. -/
theorem integral_coshPow_le_band {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {Y : Ω → ℝ} (hY : Measurable Y)
    (hsym : μ.map Y = μ.map (fun ω => -Y ω)) (δ : ℝ) (h : ℕ)
    (hexp : Integrable (fun ω => Real.exp (32 * |Y ω|)) μ)
    (hm : ∀ n : ℕ, ∫ ω, Y ω ^ (2 * n) ∂μ ≤
      ((2 * n).factorial : ℝ) * (δ ^ 2) ^ n *
        PowerSeries.coeff n (Contract.bandSeries ^ h) / 2 ^ n)
    {θ : ℝ} (hθ : 0 ≤ θ) :
    ∫ ω, (Real.cosh (θ + Y ω) - 1) ^ 32 ∂μ ≤
      Contract.bandSeriesEval δ h (Real.cosh θ - 1) := by
  let m : ℕ → ℝ := fun n => ((2 * n).factorial : ℝ) * (δ ^ 2) ^ n *
    PowerSeries.coeff n (Contract.bandSeries ^ h) / 2 ^ n
  have hc (n : ℕ) : m n * 2 ^ n / ((2 * n).factorial : ℝ) =
      (δ ^ 2) ^ n * PowerSeries.coeff n (Contract.bandSeries ^ h) := by
    dsimp only [m]
    have hn : ((2 * n).factorial : ℝ) ≠ 0 := by positivity
    have htwo : (2 : ℝ) ^ n ≠ 0 := by positivity
    field_simp
  have hs : Summable fun n : ℕ =>
      (m n * 2 ^ n / ((2 * n).factorial : ℝ)) *
        ((coshL ^ n) (X ^ 32 : ℝ[X])).eval (Real.cosh θ - 1) := by
    simp_rw [hc]
    exact Contract.bandSeriesEval_summable δ h _
  have hb := integral_coshPow_le hY hsym 32 hexp m hm hθ hs
  simp_rw [hc] at hb
  exact hb

/-- Adding a fresh band increases every coefficient. -/
theorem bandSeries_pow_coeff_mono (n : ℕ) :
    Monotone fun h : ℕ => PowerSeries.coeff n (Contract.bandSeries ^ h) := by
  apply monotone_nat_of_le_succ
  intro h
  rw [pow_succ, PowerSeries.coeff_mul]
  have hz : PowerSeries.coeff 0 Contract.bandSeries = 1 := by
    simp only [Contract.bandSeries, PowerSeries.coeff_mk, ↓reduceIte]
  have hb := Finset.single_le_sum (f := fun ij : ℕ × ℕ =>
      PowerSeries.coeff ij.1 (Contract.bandSeries ^ h) *
        PowerSeries.coeff ij.2 Contract.bandSeries)
    (fun ij _ => mul_nonneg (Contract.bandSeries_pow_coeff_bounds h ij.1).1
      (by simpa only [pow_one] using (Contract.bandSeries_pow_coeff_bounds 1 ij.2).1))
    (show (n, 0) ∈ Finset.antidiagonal n by simp)
  simpa only [hz, mul_one] using hb

/-- Evaluations of generator iterates increase on the nonnegative real axis. -/
theorem coshL_pow_eval_mono (n : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    ((coshL ^ n) (X ^ 32 : ℝ[X])).eval x ≤
      ((coshL ^ n) (X ^ 32 : ℝ[X])).eval y := by
  rw [Contract.coshL_pow_eval_fin_sum, Contract.coshL_pow_eval_fin_sum]
  exact Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hx hxy r) (coshL_pow_nonneg n 32 r)

/-- The scalar band return increases in both the number of bands and the seed point. -/
theorem bandSeriesEval_mono (δ : ℝ) {h h' : ℕ} (hh : h ≤ h')
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    Contract.bandSeriesEval δ h x ≤ Contract.bandSeriesEval δ h' y := by
  apply Summable.tsum_le_tsum _ (Contract.bandSeriesEval_summable δ h x)
    (Contract.bandSeriesEval_summable δ h' y)
  intro n
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (bandSeries_pow_coeff_mono n hh)
      (pow_nonneg (sq_nonneg δ) n)
  · exact coshL_pow_eval_mono n hx hxy
  · exact coshL_pow_eval_nonneg n 32 hx
  · exact mul_nonneg (pow_nonneg (sq_nonneg δ) n)
      (Contract.bandSeries_pow_coeff_bounds h' n).1

end GMCExplicitDelta.Insertion
