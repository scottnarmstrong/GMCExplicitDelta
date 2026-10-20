module

public import GMCExplicitDelta.Contract.Obligations
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import GMCExplicitDelta.Numerics.Enclosures
public import GMCExplicitDelta.Source.ExpMomentNumerics
public import GMCExplicitDelta.Source.MomentRatios

/-!
# Numeric obligations, group 1: the row-independent facts

O.src.1–7 (value parts), O.avg.2, and the half-integer Gamma formula used by O.sph.
-/

@[expose] public section

open Real

namespace GMCExplicitDelta.Certificates

open GMCExplicitDelta.Contract

/-- **O.src.1**. -/
theorem src1_proof : (3 - 2 * √2) / 16 < (proxyA : ℝ) := by
  have hs : (1.41421356 : ℝ) ≤ √2 := Real.le_sqrt_of_sq_le (by norm_num)
  norm_num [proxyA]
  linarith only [hs]

/-- **O.src.2**. -/
theorem src2_proof : Real.log 2 / (35 + (13 + 2 * √2) * π ^ 2) < (varU : ℝ) := by
  have h := GMCExplicitDelta.Source.sourceVarianceTrue_le
  have h' : Real.log 2 / (35 + (13 + 2 * √2) * π ^ 2) ≤ 0.003624861638 := h
  refine lt_of_le_of_lt h' ?_
  norm_num [varU]

/-- **O.src.3**. -/
theorem src3_proof : (varU : ℝ) < proxyA ∧ (kappaQ1 : ℝ) < (proxyA : ℝ) / 2 ∧
    (varU : ℝ) / 2 + 4 * (Real.exp ((proxyA : ℝ) / 8) - 1 - (proxyA : ℝ) / 8) < kappaQ1 := by
  refine ⟨by norm_num [varU, proxyA], by norm_num [kappaQ1, proxyA], ?_⟩
  have hq : (proxyA : ℝ) / 8 = 1072331 / 800000000 := by norm_num [proxyA]
  have he : Real.exp ((1072331 / 800000000 : ℝ)) ≤
      1 + (1072331 / 800000000 : ℝ) + (1072331 / 800000000 : ℝ) ^ 2 / 2 +
        (1072331 / 800000000 : ℝ) ^ 3 / 5 := by
    apply GMCNumerics.exp_le_of_poly (n := 8) (by norm_num [abs_of_pos]) (by norm_num)
    norm_num [GMCNumerics.expPoly, GMCNumerics.expErr, Finset.sum_range_succ, Nat.factorial,
      abs_of_pos]
  rw [hq]
  norm_num [varU, kappaQ1] at he ⊢
  linarith only [he]

/-- **O.src.4**. -/
theorem src4_proof : 4 / 3 * (√3 - 1) ≤ (ratioC2 : ℝ) :=
  GMCExplicitDelta.Source.sqrt_three_ratio_le_ratioC2

/-- **O.src.5**. -/
theorem src5_proof : 72 * (√3 - 1) / (5 * (Real.exp 3 - Real.exp 1)) ≤ (ratioC3 : ℝ) := by
  have h := GMCExplicitDelta.Source.sqrt_three_ratio_le_ratioC3
  have e3 : Real.exp 3 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [e3]; exact h

/-- **O.src.6**. -/
theorem src6_proof : 0 < ratioC3 ∧ ratioC3 < ratioC2 ∧ ratioC2 < 1 ∧ 0 ≤ varU ∧ varU ≤ proxyA := by
  norm_num [ratioC3, ratioC2, varU, proxyA]

/-- **O.avg.2**. -/
theorem avg2_proof : ∀ k < 16, assocStirling 32 (k + 1) = assocStirling32Table.getD k 0 := by
  decide +kernel

/-! ### Half-integer Gamma values -/

theorem gamma_nat_add_half (n : ℕ) :
    Real.Gamma ((n : ℝ) + 1 / 2) = √π * ∏ j ∈ Finset.range n, ((j : ℝ) + 1 / 2) := by
  induction n with
  | zero => simpa using Real.Gamma_one_half_eq
  | succ n ih =>
    have : ((n + 1 : ℕ) : ℝ) + 1 / 2 = ((n : ℝ) + 1 / 2) + 1 := by push_cast; ring
    rw [this, Real.Gamma_add_one (by positivity), ih, Finset.prod_range_succ]
    ring

/-- **O.sph**, `d = 2`. -/
theorem sph_two : (sphereFactorPow 2 : ℝ) =
    √π * Real.Gamma (32 + ((2 : ℕ) : ℝ) / 2) /
      (Real.Gamma (((2 : ℕ) : ℝ) / 2) * Real.Gamma (32 + 1 / 2)) := by
  have h1 : (32 + ((2 : ℕ) : ℝ) / 2) = ((32 : ℕ) : ℝ) + 1 := by norm_num
  have h2 : (32 + 1 / 2 : ℝ) = ((32 : ℕ) : ℝ) + 1 / 2 := by norm_num
  have h3 : (((2 : ℕ) : ℝ) / 2) = 1 := by norm_num
  rw [h1, h2, h3, Real.Gamma_nat_eq_factorial, Real.Gamma_one, gamma_nat_add_half]
  have hs : √π ≠ 0 := by positivity
  simp only [Finset.prod_range_succ, Finset.prod_range_zero]
  field_simp
  norm_num [sphereFactorPow, Nat.choose_eq_factorial_div_factorial, Nat.factorial]

/-- **O.sph**, `d = 3`. -/
theorem sph_three : (sphereFactorPow 3 : ℝ) =
    √π * Real.Gamma (32 + ((3 : ℕ) : ℝ) / 2) /
      (Real.Gamma (((3 : ℕ) : ℝ) / 2) * Real.Gamma (32 + 1 / 2)) := by
  have h1 : (32 + ((3 : ℕ) : ℝ) / 2) = ((33 : ℕ) : ℝ) + 1 / 2 := by norm_num
  have h2 : (32 + 1 / 2 : ℝ) = ((32 : ℕ) : ℝ) + 1 / 2 := by norm_num
  have h3 : (((3 : ℕ) : ℝ) / 2) = ((1 : ℕ) : ℝ) + 1 / 2 := by norm_num
  rw [h1, h2, h3, gamma_nat_add_half, gamma_nat_add_half, gamma_nat_add_half]
  have hs : √π ≠ 0 := by positivity
  simp only [Finset.prod_range_succ, Finset.prod_range_zero]
  field_simp
  norm_num [sphereFactorPow]

/-- **O.sph**, `d = 4`. -/
theorem sph_four : (sphereFactorPow 4 : ℝ) =
    √π * Real.Gamma (32 + ((4 : ℕ) : ℝ) / 2) /
      (Real.Gamma (((4 : ℕ) : ℝ) / 2) * Real.Gamma (32 + 1 / 2)) := by
  have h1 : (32 + ((4 : ℕ) : ℝ) / 2) = ((33 : ℕ) : ℝ) + 1 := by norm_num
  have h2 : (32 + 1 / 2 : ℝ) = ((32 : ℕ) : ℝ) + 1 / 2 := by norm_num
  have h3 : (((4 : ℕ) : ℝ) / 2) = ((1 : ℕ) : ℝ) + 1 := by norm_num
  rw [h1, h2, h3, Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial, gamma_nat_add_half]
  have hs : √π ≠ 0 := by positivity
  simp only [Finset.prod_range_succ, Finset.prod_range_zero]
  field_simp
  norm_num [sphereFactorPow, Nat.choose_eq_factorial_div_factorial, Nat.factorial]

end GMCExplicitDelta.Certificates
