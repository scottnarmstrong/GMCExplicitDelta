module

public import GMCExplicitDelta.Insertion.FreshMixedBand

/-! # The even Taylor-moment functional in I3 -/

@[expose] public section

open MeasureTheory Homogenization SubdiffusiveProcess.Model
open scoped ENNReal

namespace GMCExplicitDelta.Insertion

/-- The I3 functional on monomials: factorial times the coefficient of the S9
majorant in the original Taylor variable. Odd monomials are killed. -/
noncomputable def bandMomentFunctional (δ : ℝ) (h N : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((N.factorial : ℝ) * PowerSeries.coeff N
    (Source.bandMajorant Contract.proxyA Contract.varU (δ ^ 2)
      Contract.ratioC2 Contract.ratioC3 ^ h))

@[simp] theorem bandMomentFunctional_zero (δ : ℝ) (h : ℕ) :
    bandMomentFunctional δ h 0 = 1 := by
  have hc := Source.bandMajorant_pow_even_coeff
    (Contract.proxyA : ℝ) Contract.varU (δ ^ 2) Contract.ratioC2 Contract.ratioC3 h 0
  simp only [Nat.mul_zero] at hc
  unfold bandMomentFunctional
  rw [hc, PowerSeries.coeff_zero_eq_constantCoeff, map_pow]
  have h0 : PowerSeries.constantCoeff
      (Source.bandEvenMajorant (Contract.proxyA : ℝ) Contract.varU (δ ^ 2)
        Contract.ratioC2 Contract.ratioC3) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    simp only [Source.bandEvenMajorant, PowerSeries.coeff_mk, ↓reduceIte]
  simp only [h0, one_pow, Nat.factorial_zero, Nat.cast_one, one_mul, ENNReal.ofReal_one]

@[simp] theorem bandMomentFunctional_odd (δ : ℝ) (h n : ℕ) :
    bandMomentFunctional δ h (2 * n + 1) = 0 := by
  unfold bandMomentFunctional
  rw [Source.bandMajorant_pow_odd_coeff, mul_zero, ENNReal.ofReal_zero]

/-- The even values are precisely the rescaled band-series moments. -/
theorem bandMomentFunctional_even (δ : ℝ) (h n : ℕ) :
    bandMomentFunctional δ h (2 * n) = ENNReal.ofReal
      (((2 * n).factorial : ℝ) * (δ ^ 2) ^ n *
        PowerSeries.coeff n (Contract.bandSeries ^ h) / 2 ^ n) := by
  unfold bandMomentFunctional
  rw [Source.bandMajorant_pow_even_coeff, bandEvenMajorant_eq_rescale,
    ← map_pow, PowerSeries.coeff_rescale, div_pow]
  congr 1
  ring

/-- Every even absolute marginal moment is controlled by the I3 functional. -/
theorem layer_sum_abs_even_moment_functional {d : ℕ} (M : GMCModel d)
    (I : Finset ℕ) (x : Vec d) {N : ℕ} (hN : Even N) :
    (∫⁻ ω : PotentialSample d, ENNReal.ofReal |∑ k ∈ I, ω k x| ^ N ∂M.P.toMeasure) ≤
      bandMomentFunctional M.delta I.card N := by
  obtain ⟨n, rfl⟩ := even_iff_two_dvd.mp hN
  have hb := layer_sum_band_moments M I x
  have heq : (fun ω : PotentialSample d => ENNReal.ofReal |∑ k ∈ I, ω k x| ^ (2 * n)) =
      (fun ω : PotentialSample d => ENNReal.ofReal ((∑ k ∈ I, ω k x) ^ (2 * n))) := by
    funext ω
    rw [← ENNReal.ofReal_pow (abs_nonneg _), pow_abs_two_mul]
  rw [heq, bandMomentFunctional_even,
    ← ofReal_integral_eq_lintegral_ofReal (hb.1 (2 * n))
      (Filter.Eventually.of_forall fun ω => Even.pow_nonneg (even_two_mul n) _)]
  exact ENNReal.ofReal_le_ofReal (hb.2 n)

end GMCExplicitDelta.Insertion
