module

public import GMCExplicitDelta.Proofs.GridMax.Maximum
public import GMCExplicitDelta.Proofs.GridMax.Remainder

/-! # Identification of the grid-moment constants with the contract -/

@[expose] public section

open Homogenization MeasureTheory Real SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

namespace GMCExplicitDelta.Assembly.GridMax

variable {d : ℕ}

/-- The real value of the nonnegative variance proxy, without unfolding its carrier. -/
theorem prefixProxy_coe (M : GMCModel d) (L : ℕ) :
    (prefixProxy M L : ℝ) = ((L : ℝ) + 1) * (Contract.proxyA : ℝ) * M.delta ^ 2 := rfl

/-- The Gaussian layerPrefix standard deviation in separated variables. -/
theorem prefix_sigma (M : GMCModel d) (L : ℕ) :
    sqrt (2 * (prefixProxy M L : ℝ)) =
      M.delta * sqrt (2 * (Contract.proxyA : ℝ)) * sqrt ((L : ℝ) + 1) := by
  have hδ := M.shellPrefix.delta_pos
  have ha : 0 ≤ 2 * (Contract.proxyA : ℝ) := by norm_num [Contract.proxyA]
  have heq : 2 * (prefixProxy M L : ℝ) = M.delta ^ 2 *
      (2 * (Contract.proxyA : ℝ) * ((L : ℝ) + 1)) := by
    rw [prefixProxy_coe]
    ring
  rw [heq, sqrt_mul (sq_nonneg _), sqrt_sq_eq_abs, abs_of_pos hδ, sqrt_mul ha]
  ring

/-- The L128 grid maximum is bounded by the first term inside B_L's bracket. -/
theorem maximum_lnorm_row (row : Contract.Row d) [NeZero row.gridN] (M : GMCModel d) (L : ℕ)
    (c : Homogenization.Vec d) :
    paperENNRealLpNorm M.P.toMeasure 128 (fun ω => ENNReal.ofReal (maximum row.gridN L c ω)) ≤
      ENNReal.ofReal (M.delta * sqrt Contract.P32 * (row.cg * sqrt ((L : ℝ) + 1))) := by
  refine (maximum_lnorm128 M row.gridN L c).trans_eq ?_
  congr 1
  rw [prefix_sigma]
  change row.hbar * (M.delta * sqrt (2 * (Contract.proxyA : ℝ)) * sqrt ((L : ℝ) + 1) *
    sqrt Contract.P32) = _
  unfold Contract.Row.cg
  ring

/-- The product of the two exponential bounds has exactly the contract's prefactor and rate. -/
theorem exponential_factor (row : Contract.Row d) (M : GMCModel d) (L : ℕ) :
    exp (Contract.kappaH d * ((L : ℝ) + 1) * M.delta ^ 2) *
      (((2 * ((row.gridN ^ d : ℕ) : ℝ)) ^ (1 / 128 : ℝ) * exp (64 * (prefixProxy M L : ℝ))) *
        ((2 : ℝ) ^ (1 / 128 : ℝ) * exp (32 * row.Ag ^ 2 * M.delta ^ 2))) =
      Contract.varsigma * row.hbar *
        exp ((64 * (Contract.proxyA : ℝ) * ((L : ℝ) + 1) + 32 * row.Ag ^ 2 +
          Contract.kappaH d * ((L : ℝ) + 1)) * M.delta ^ 2) := by
  have htwo : (2 : ℝ) ^ (1 / 128 : ℝ) * (2 : ℝ) ^ (1 / 128 : ℝ) = Contract.varsigma := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num [Contract.varsigma]
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg _)]
  have heq : (Contract.kappaH d * ((L : ℝ) + 1) * M.delta ^ 2) +
      64 * (prefixProxy M L : ℝ) + 32 * row.Ag ^ 2 * M.delta ^ 2 =
      (64 * (Contract.proxyA : ℝ) * ((L : ℝ) + 1) + 32 * row.Ag ^ 2 +
        Contract.kappaH d * ((L : ℝ) + 1)) * M.delta ^ 2 := by
    rw [prefixProxy_coe]
    ring
  calc
    _ = ((2 : ℝ) ^ (1 / 128 : ℝ) * (2 : ℝ) ^ (1 / 128 : ℝ)) * row.hbar *
        exp ((Contract.kappaH d * ((L : ℝ) + 1) * M.delta ^ 2) +
          64 * (prefixProxy M L : ℝ) + 32 * row.Ag ^ 2 * M.delta ^ 2) := by
      rw [exp_add, exp_add]
      unfold Contract.Row.hbar Contract.Row.gridCount
      ring
    _ = _ := by rw [htwo, heq]

end GMCExplicitDelta.Assembly.GridMax
