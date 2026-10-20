module

public import GMCExplicitDelta.Insertion.SphereGaussianVector
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Distributions.Gaussian.Fernique

/-! # Radial Gaussian moments by finite-product convolution -/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped Nat NNReal ENNReal BigOperators

namespace GMCExplicitDelta.Insertion

/-- The unnormalized radial moment polynomial. -/
noncomputable def radialMoment (a : ℝ) (p : ℕ) : ℝ :=
  ∏ j ∈ range p, (a + 2 * j)

@[simp] theorem radialMoment_zero (a : ℝ) : radialMoment a 0 = 1 := by
  simp only [radialMoment, range_zero, prod_empty]

theorem radialMoment_succ (a : ℝ) (p : ℕ) :
    radialMoment a (p + 1) = radialMoment a p * (a + 2 * p) := by
  exact prod_range_succ _ _

/-- Chu–Vandermonde in the normalization needed for Gaussian squares. -/
theorem radialMoment_add (a b : ℝ) (p : ℕ) :
    radialMoment (a + b) p = ∑ ij ∈ antidiagonal p,
      (p.choose ij.1 : ℝ) * (radialMoment a ij.1 * radialMoment b ij.2) := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [sum_antidiagonal_choose_succ_mul (fun i j => radialMoment a i * radialMoment b j) p, ← sum_add_distrib, radialMoment_succ, ih,
      sum_mul]
    apply sum_congr rfl
    intro ij hij
    have hij' : ij.1 + ij.2 = p := mem_antidiagonal.mp hij
    have hc : p.choose ij.2 = p.choose ij.1 :=
      Nat.choose_symm_of_eq_add (by omega)
    rw [hc, radialMoment_succ, radialMoment_succ]
    have hr : (ij.1 : ℝ) + ij.2 = p := by exact_mod_cast hij'
    rw [← hr]
    ring

/-- The scalar even-moment sequence is the radial polynomial at dimension one. -/
theorem radialMoment_one (p : ℕ) : radialMoment 1 p = ((2 * p - 1)‼ : ℝ) := by
  induction p with
  | zero => norm_num [Nat.doubleFactorial]
  | succ p ih =>
    rw [radialMoment_succ, ih]
    cases p with
    | zero => norm_num [Nat.doubleFactorial]
    | succ p =>
      have h : 2 * (p + 1 + 1) - 1 = (2 * (p + 1) - 1) + 2 := by omega
      rw [h, Nat.doubleFactorial_add_two]
      push_cast
      have he : 2 * (p + 1) - 1 = 2 * p + 1 := by omega
      rw [he]
      push_cast
      ring

/-- Coordinate product measure for a standard Gaussian vector. -/
noncomputable def gaussianPi (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1

instance (d : ℕ) : IsProbabilityMeasure (gaussianPi d) := by
  unfold gaussianPi
  infer_instance

/-- Squared Euclidean length, explicitly not the function-space sup norm. -/
noncomputable def sqSum {d : ℕ} (x : Fin d → ℝ) : ℝ := ∑ i, x i ^ 2

theorem sqSum_eq_norm_sq {d : ℕ} (x : Fin d → ℝ) :
    sqSum x = ‖WithLp.toLp 2 x‖ ^ 2 := by
  exact (EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 x)).symm

theorem integrable_sqSum_pow (d p : ℕ) :
    Integrable (fun x : Fin d → ℝ => sqSum x ^ p) (gaussianPi d) := by
  have hi := (IsGaussian.memLp_id (stdGaussian (EuclideanSpace ℝ (Fin d)))
    ((2 * p : ℕ) : ℝ≥0∞) (ENNReal.natCast_ne_top (2 * p))).integrable_norm_pow' (p := 2 * p)
  have hm : MeasurePreserving (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d))
      (gaussianPi d) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    ⟨by fun_prop, map_pi_eq_stdGaussian⟩
  have h := hm.integrable_comp_of_integrable hi
  simpa only [Function.comp_def, id_eq, sqSum_eq_norm_sq, ← pow_mul] using h

theorem integrable_gaussianReal_even (p : ℕ) :
    Integrable (fun x : ℝ => x ^ (2 * p)) (gaussianReal 0 1) := by
  simpa only [id_eq, Real.norm_eq_abs, pow_abs_two_mul] using
    (memLp_id_gaussianReal' (μ := 0) (v := 1) ((2 * p : ℕ) : ℝ≥0∞) (ENNReal.natCast_ne_top (2 * p))).integrable_norm_pow'
      (p := 2 * p)

/-- The radial moment under the independent-coordinate Gaussian measure. -/
theorem integral_sqSum_pow (d p : ℕ) :
    (∫ x : Fin d → ℝ, sqSum x ^ p ∂gaussianPi d) = radialMoment d p := by
  induction d generalizing p with
  | zero =>
    cases p with
    | zero => simp
    | succ p => simp [sqSum, radialMoment, prod_range_succ', gaussianPi]
  | succ d ih =>
    calc
      _ = ∫ z : ℝ × (Fin d → ℝ), (z.1 ^ 2 + sqSum z.2) ^ p
          ∂((gaussianReal 0 1).prod (gaussianPi d)) := by
        unfold gaussianPi
        rw [← ((measurePreserving_piFinSuccAbove
          (fun _ : Fin (d + 1) => gaussianReal 0 1) 0).symm).integral_comp']
        simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          sqSum, Fin.sum_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk,
          Fin.cons_succ, Fin.zero_succAbove, cast_eq, Fin.cons_zero]
      _ = ∑ ij ∈ antidiagonal p, (p.choose ij.1 : ℝ) *
          (radialMoment 1 ij.1 * radialMoment d ij.2) := by
        simp_rw [show ∀ a b : ℝ, (a + b) ^ p = ∑ ij ∈ antidiagonal p,
          (p.choose ij.1 : ℝ) * (a ^ ij.1 * b ^ ij.2) from
          fun a b => by simpa only [nsmul_eq_mul] using (Commute.all a b).add_pow' p]
        rw [integral_finsetSum]
        · apply sum_congr rfl
          intro ij hij
          simp_rw [← pow_mul]
          rw [integral_const_mul, integral_prod_mul (fun x : ℝ => x ^ (2 * ij.1))
              (fun x : Fin d → ℝ => sqSum x ^ ij.2), integral_pow_gaussianReal_even,
            ih, radialMoment_one]
        · intro ij hij
          apply Integrable.const_mul
          simpa only [← pow_mul] using
            (integrable_gaussianReal_even ij.1).mul_prod (integrable_sqSum_pow d ij.2)
      _ = radialMoment ((d + 1 : ℕ) : ℝ) p := by
        rw [← radialMoment_add]
        congr 1
        push_cast
        ring

/-- The exact Euclidean radial Gaussian moment. -/
theorem integral_norm_pow_stdGaussian_even (d p : ℕ) :
    (∫ g : EuclideanSpace ℝ (Fin d), ‖g‖ ^ (2 * p)
      ∂stdGaussian (EuclideanSpace ℝ (Fin d))) =
      ∏ j ∈ range p, ((d : ℝ) + 2 * j) := by
  rw [← map_pi_eq_stdGaussian, integral_map (by fun_prop) (by fun_prop)]
  simpa only [← sqSum_eq_norm_sq, pow_mul, radialMoment] using (show (∫ x : Fin d → ℝ, sqSum x ^ p ∂Measure.pi (fun _ => gaussianReal 0 1)) = radialMoment d p from integral_sqSum_pow d p)

end GMCExplicitDelta.Insertion
