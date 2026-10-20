module

public import GMCExplicitDelta.Proofs.GridMax.Grid
public import GMCExplicitDelta.Proofs.GridMax.Norms

/-! # The spatial remainder and its sharp Orlicz scale -/

@[expose] public section

open Homogenization MeasureTheory Real SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

namespace GMCExplicitDelta.Assembly.GridMax

variable {d : ℕ}

/-- Total mass of the truncated geometric derivative weights. -/
theorem geometric_mass (n : ℕ) :
    (∑ i ∈ Finset.range n, ((3 : ℝ) ^ i)⁻¹) = 3 / 2 * (1 - ((3 : ℝ)⁻¹) ^ n) := by
  simp only [← inv_pow]
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

/-- Coefficients of the spatial remainder have mass at most A_g. -/
theorem remainder_mass {N : ℕ} (hN : 0 < N) (L : ℕ) :
    (∑ i ∈ Finset.range (L + 1), 1 / (2 * (N : ℝ)) * ((3 : ℝ) ^ i)⁻¹) ≤ 3 / (4 * (N : ℝ)) := by
  rw [← Finset.mul_sum, geometric_mass]
  have hn : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hp : 0 ≤ ((3 : ℝ)⁻¹) ^ (L + 1) := by positivity
  have hh : 3 / 2 * (1 - ((3 : ℝ)⁻¹) ^ (L + 1)) ≤ 3 / 2 := by linarith
  exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by field_simp; ring)

/-- The remainder is measurable. -/
theorem remainder_measurable (N L : ℕ) (z : Homogenization.Vec d) : Measurable (remainder N L z) :=
  Finset.measurable_sum _ fun i _ => (W_measurable i z).const_mul _

/-- All remainder coefficients and controls are nonnegative. -/
theorem remainder_nonneg (N L : ℕ) (z : Homogenization.Vec d) (ω : PotentialSample d) :
    0 ≤ remainder N L z ω :=
  Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (W_nonneg i z ω)

/-- S10 at exactly the geometric scale A_g δ. -/
theorem remainder_orlicz (M : GMCModel d) {N : ℕ} (hN : 0 < N) (L : ℕ) (z : Homogenization.Vec d) :
    Integrable (fun ω => exp (remainder N L z ω ^ 2 / (3 / (4 * (N : ℝ)) * M.delta) ^ 2)) M.P.toMeasure ∧
      ∫ ω, exp (remainder N L z ω ^ 2 / (3 / (4 * (N : ℝ)) * M.delta) ^ 2) ∂M.P.toMeasure ≤ 2 := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.2 hN
  exact integrable_integral_exp_sq_weighted_sum_le_two
    (A := 3 / (4 * (N : ℝ))) (δ := M.delta) (Finset.range (L + 1))
    (fun i => 1 / (2 * (N : ℝ)) * ((3 : ℝ) ^ i)⁻¹) (fun i => W i z)
    (by positivity) (fun i _ => by positivity) (remainder_mass hN L)
    (fun i _ => (W_measurable i z).aestronglyMeasurable)
    (fun i _ => (W_orlicz M i z).1) (fun i _ => (W_orlicz M i z).2)

/-- The sharp L128 remainder norm. -/
theorem remainder_lnorm128 (M : GMCModel d) {N : ℕ} (hN : 0 < N) (L : ℕ) (z : Homogenization.Vec d) :
    paperENNRealLpNorm M.P.toMeasure 128 (fun ω => ENNReal.ofReal (remainder N L z ω)) ≤
      ENNReal.ofReal (3 / (4 * (N : ℝ)) * M.delta * sqrt Contract.P32) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hδ := M.shellPrefix.delta_pos
  obtain ⟨hi, hb⟩ := remainder_orlicz M hN L z
  simpa only [abs_of_nonneg (remainder_nonneg N L z _)] using
    lnorm128_of_orlicz (by positivity : 0 < 3 / (4 * (N : ℝ)) * M.delta)
      (remainder_measurable N L z).aestronglyMeasurable hi hb

/-- The matching exponential L128 norm. -/
theorem remainder_exp128_norm (M : GMCModel d) {N : ℕ} (hN : 0 < N) (L : ℕ) (z : Homogenization.Vec d) :
    paperENNRealLpNorm M.P.toMeasure 128 (fun ω => ENNReal.ofReal (exp (remainder N L z ω))) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (1 / 128 : ℝ) *
        exp (32 * (3 / (4 * (N : ℝ))) ^ 2 * M.delta ^ 2)) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hδ := M.shellPrefix.delta_pos
  have hB : 0 < 3 / (4 * (N : ℝ)) * M.delta := by positivity
  obtain ⟨hi, hb⟩ := remainder_orlicz M hN L z
  have he := integral_exp_mul_le_of_orlicz hB.ne'
    (remainder_measurable N L z).aestronglyMeasurable hi hb 128
  refine (lnorm_exp_of_moment (by norm_num : (0 : ℝ) < 128)
    (integrable_exp_of_orlicz hB.ne' (remainder_measurable N L z).aestronglyMeasurable hi 128) he).trans_eq ?_
  congr 1
  simp only [one_div]
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (exp_pos _).le, ← exp_mul]
  congr 1
  congr 1
  ring

end GMCExplicitDelta.Assembly.GridMax
