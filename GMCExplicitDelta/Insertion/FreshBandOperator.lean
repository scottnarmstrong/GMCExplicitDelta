module

public import GMCExplicitDelta.Contract.DerivedFresh
public import GMCExplicitDelta.Source.BandMajorant
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

open Polynomial
open scoped Matrix.Norms.Operator

namespace GMCExplicitDelta.Contract

theorem bandSeries_eq_majorant :
    bandSeries = Source.bandEvenMajorant proxyA varU 2 ratioC2 ratioC3 := by
  ext n
  simp only [bandSeries, Source.bandEvenMajorant, PowerSeries.coeff_mk]
  split_ifs <;> ring

theorem bandSeries_pow_coeff_bounds (h n : ℕ) :
    0 ≤ PowerSeries.coeff n (bandSeries ^ h) ∧
      PowerSeries.coeff n (bandSeries ^ h) ≤ ((h : ℝ) * proxyA) ^ n / n.factorial := by
  rw [bandSeries_eq_majorant]
  have hb := Source.bandEvenMajorant_pow_coeff_le
    (a := (proxyA : ℝ)) (u := (varU : ℝ)) (s := 2)
    (c₂ := (ratioC2 : ℝ)) (c₃ := (ratioC3 : ℝ))
    (by norm_num [proxyA]) (by norm_num [varU]) (by norm_num)
    (by norm_num [proxyA, varU]) (by norm_num [ratioC2]) (by norm_num [ratioC2])
    (by norm_num [ratioC3]) (by norm_num [ratioC3]) h n
  simpa only [mul_div_cancel_right₀ _ (show (2 : ℝ) ≠ 0 by norm_num)] using hb

/-- Absolute convergence of the operator series in any real Banach algebra. -/
theorem bandSeries_summable_norm {A : Type*} [NormedRing A] [NormOneClass A] [NormedAlgebra ℝ A]
    [CompleteSpace A] (a : A) (h : ℕ) :
    Summable fun n : ℕ => ‖PowerSeries.coeff n (bandSeries ^ h) • a ^ n‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    (Real.summable_pow_div_factorial (((h : ℝ) * proxyA) * ‖a‖))
  have ha : (0 : ℝ) ≤ (proxyA : ℝ) := by norm_num [proxyA]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (bandSeries_pow_coeff_bounds h n).1]
  calc
    _ ≤ (((h : ℝ) * proxyA) ^ n / n.factorial) * ‖a‖ ^ n :=
      mul_le_mul (bandSeries_pow_coeff_bounds h n).2 (norm_pow_le a n)
        (norm_nonneg _) (by positivity)
    _ = _ := by rw [mul_pow]; ring

/-- Cauchy multiplication of the absolutely convergent band operator series. -/
theorem bandSeries_tsum_pow {A : Type*} [NormedRing A] [NormOneClass A] [NormedAlgebra ℝ A]
    [CompleteSpace A] (a : A) (h : ℕ) :
    (∑' n : ℕ, PowerSeries.coeff n bandSeries • a ^ n) ^ h =
      ∑' n : ℕ, PowerSeries.coeff n (bandSeries ^ h) • a ^ n := by
  induction h with
  | zero =>
    simp only [pow_zero, PowerSeries.coeff_one]
    simp
  | succ h ih =>
    rw [pow_succ, ih,
      tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
        (bandSeries_summable_norm a h) (by simpa using bandSeries_summable_norm a 1)]
    apply tsum_congr
    intro n
    rw [pow_succ, PowerSeries.coeff_mul, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro ij hij
    rw [smul_mul_smul_comm, ← pow_add, Finset.mem_antidiagonal.mp hij]

/-- Iteration of the generator preserves the degree cutoff. -/
theorem coshL_pow_coeff_above (n : ℕ) (i : Fin 33) (k : ℕ) (hk : 33 ≤ k) :
    ((Insertion.coshL ^ n) (X ^ (i : ℕ) : ℝ[X])).coeff k = 0 := by
  induction n generalizing k with
  | zero => simp [coeff_X_pow, show k ≠ (i : ℕ) by omega]
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, Insertion.coeff_coshL,
      ih k hk, ih (k + 1) (by omega)]
    ring

/-- Reconstruct a polynomial in the finite monomial basis used by the contract matrix. -/
theorem polynomial_eq_fin_sum (q : ℝ[X]) (hq : ∀ k, 33 ≤ k → q.coeff k = 0) :
    q = ∑ i : Fin 33, q.coeff i • (X ^ (i : ℕ) : ℝ[X]) := by
  classical
  ext k
  rw [finsetSum_coeff]
  by_cases hk : k < 33
  · rw [Finset.sum_eq_single (⟨k, hk⟩ : Fin 33)]
    · simp
    · intro b _ hb
      have hkb : k ≠ (b : ℕ) := by
        intro heq
        apply hb
        exact Fin.ext heq.symm
      simp [coeff_smul, coeff_X_pow, hkb]
    · simp
  · rw [hq k (by omega)]
    symm
    apply Finset.sum_eq_zero
    intro i _
    simp [coeff_smul, coeff_X_pow, show k ≠ (i : ℕ) by omega]

/-- Powers of the matrix are coefficients of the iterated polynomial generator. -/
theorem generatorMatrix_pow_apply (n : ℕ) (i j : Fin 33) :
    (generatorMatrix ^ n) i j =
      ((Insertion.coshL ^ n) (X ^ (i : ℕ) : ℝ[X])).coeff j := by
  classical
  induction n generalizing i j with
  | zero => simp [Matrix.one_apply, coeff_X_pow, Fin.ext_iff, eq_comm]
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply, pow_succ', Module.End.mul_apply]
    conv_rhs =>
      arg 1
      arg 1
      rw [polynomial_eq_fin_sum _ (coshL_pow_coeff_above n i)]
    simp only [map_sum, map_smul, finsetSum_coeff, coeff_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [ih, generatorMatrix_apply]

/-- Entrywise evaluation of a convergent matrix series. -/
theorem matrix_tsum_apply (f : ℕ → Matrix (Fin 33) (Fin 33) ℝ)
    (hf : Summable f) (i j : Fin 33) :
    (∑' n, f n) i j = ∑' n, f n i j := by
  exact (Pi.hasSum.mp (Pi.hasSum.mp hf.hasSum i) j).tsum_eq.symm

/-- The contract's matrix is the convergent one-band power series. -/
theorem bandMatrix_eq_tsum (δ : ℝ) :
    bandMatrix δ = ∑' n : ℕ, PowerSeries.coeff n bandSeries •
      ((δ ^ 2) • generatorMatrix) ^ n := by
  have hs : Summable fun n : ℕ => PowerSeries.coeff n bandSeries •
      ((δ ^ 2) • generatorMatrix) ^ n := by
    convert! (bandSeries_summable_norm ((δ ^ 2) • generatorMatrix) 1).of_norm using 1
    simp only [pow_one]
  rw [← hs.sum_add_tsum_nat_add 3]
  ext i j
  rw [Matrix.add_apply, matrix_tsum_apply _ ((summable_nat_add_iff 3).mpr hs)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    bandSeries, PowerSeries.coeff_mk, Matrix.add_apply]
  norm_num only [↓reduceIte, pow_zero, pow_one, Nat.factorial_zero,
    Nat.factorial_one, Nat.factorial_two]
  unfold bandMatrix
  simp only [Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  congr 1
  · simp only [smul_pow, Matrix.smul_apply, smul_eq_mul, mul_smul]
    ring
  · rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    simp only [show n + 3 ≠ 0 by omega, show n + 3 ≠ 1 by omega,
      show n + 3 ≠ 2 by omega, ↓reduceIte,
      smul_pow, Matrix.smul_apply, smul_eq_mul, mul_pow]
    ring

/-- Each coefficient series converges absolutely, hence also converges in `ℝ`. -/
theorem bandSeriesCoeff_summable (δ : ℝ) (h : ℕ) (r : Fin 33) :
    Summable fun n : ℕ => (δ ^ 2) ^ n * PowerSeries.coeff n (bandSeries ^ h) *
      ((Insertion.coshL ^ n) (X ^ 32 : ℝ[X])).coeff r := by
  have hs := (bandSeries_summable_norm ((δ ^ 2) • generatorMatrix) h).of_norm
  have he := Pi.summable.mp (Pi.summable.mp hs (32 : Fin 33)) r
  convert he using 1
  ext n
  simp only [smul_pow, Matrix.smul_apply, smul_eq_mul, generatorMatrix_pow_apply]
  simp only [show ((32 : Fin 33) : ℕ) = 32 by decide]
  ring

theorem coshL_pow_eval_fin_sum (n : ℕ) (y : ℝ) :
    ((Insertion.coshL ^ n) (X ^ 32 : ℝ[X])).eval y =
      ∑ r : Fin 33, ((Insertion.coshL ^ n) (X ^ 32 : ℝ[X])).coeff r * y ^ (r : ℕ) := by
  have hs := polynomial_eq_fin_sum _ (coshL_pow_coeff_above n (32 : Fin 33))
  change (Insertion.coshL ^ n) (X ^ 32 : ℝ[X]) = _ at hs
  simp only [show ((32 : Fin 33) : ℕ) = 32 by decide] at hs
  conv_lhs => rw [hs]
  simp only [eval_finsetSum, eval_smul, eval_pow, eval_X, smul_eq_mul]

theorem bandSeriesEval_summable (δ : ℝ) (h : ℕ) (y : ℝ) :
    Summable fun n : ℕ => (δ ^ 2) ^ n * PowerSeries.coeff n (bandSeries ^ h) *
      ((Insertion.coshL ^ n) (X ^ 32 : ℝ[X])).eval y := by
  have hs := summable_sum (s := Finset.univ) (fun (r : Fin 33) _ =>
    (bandSeriesCoeff_summable δ h r).mul_right (y ^ (r : ℕ)))
  convert hs using 1
  ext n
  rw [coshL_pow_eval_fin_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

end GMCExplicitDelta.Contract
