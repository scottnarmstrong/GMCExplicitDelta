module

public import GMCExplicitDelta.Proofs.HaarMode.Tensor

/-! # Tensor moments of affine functions -/

@[expose] public section

open MeasureTheory Homogenization Set
open scoped ENNReal

namespace GMCExplicitDelta.Localization

variable {d : ℕ}

/-- Integrability is preserved by dilation from the unit interval. -/
theorem haarMode_interval_scaled {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume (-(1 / 2 : ℝ)) (1 / 2)) (n : ℕ) :
    IntervalIntegrable (fun t => f (t / (3 : ℝ) ^ n)) volume
      (-(1 / 2 : ℝ) * (3 : ℝ) ^ n) ((1 / 2 : ℝ) * (3 : ℝ) ^ n) := by
  have hn : (3 : ℝ) ^ n ≠ 0 := by positivity
  convert! hf.comp_mul_right (c := ((3 : ℝ) ^ n)⁻¹) using 1
  <;> field_simp

/-- Coordinate products with integrable one-dimensional factors are integrable on a scaled cube. -/
theorem haarMode_integrable_scaled_prod (n : ℕ) (f : Fin d → ℝ → ℝ)
    (hf : ∀ i, IntervalIntegrable (f i) volume (-(1 / 2 : ℝ)) (1 / 2)) :
    Integrable (fun x : Homogenization.Vec d => ∏ i, f i (x i / (3 : ℝ) ^ n))
      (normalizedCubeMeasure (originCube d (n : ℤ))) := by
  let Q := originCube d (n : ℤ)
  let (i : Fin d) : IsFiniteMeasure (ENNReal.ofReal (cubeScaleFactor Q)⁻¹ •
      volume.restrict (Ico (((Q.index i : ℝ) - 1 / 2) * cubeScaleFactor Q)
        (((Q.index i : ℝ) + 1 / 2) * cubeScaleFactor Q))) :=
    (volume.restrict _).smul_finite ENNReal.ofReal_ne_top
  rw [← haarMode_normalizedCubeMeasure_pi]
  apply Integrable.fintype_prod (f := fun i t => f i (t / (3 : ℝ) ^ n))
  intro i
  apply Integrable.smul_measure (hc := ENNReal.ofReal_ne_top)
  have h := (intervalIntegrable_iff_integrableOn_Ico_of_le
    (mul_le_mul_of_nonneg_right (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2) (by positivity))).1
      (haarMode_interval_scaled (hf i) n)
  simpa only [cubeScaleFactor, originCube, zpow_natCast, Pi.zero_apply,
    Int.cast_zero, zero_sub, zero_add, IntegrableOn] using h

/-- One inserted coordinate moment is integrable whenever its one-dimensional factors are. -/
theorem haarMode_integrable_scaled_moment (n : ℕ) (f : Fin d → ℝ → ℝ) (g : ℝ → ℝ) (i : Fin d)
    (hf : ∀ j, IntervalIntegrable (f j) volume (-(1 / 2 : ℝ)) (1 / 2))
    (hg : IntervalIntegrable (fun t => g t * f i t) volume (-(1 / 2 : ℝ)) (1 / 2)) :
    Integrable (fun x : Homogenization.Vec d => g (x i / (3 : ℝ) ^ n) *
      ∏ j, f j (x j / (3 : ℝ) ^ n)) (normalizedCubeMeasure (originCube d (n : ℤ))) := by
  classical
  have h := haarMode_integrable_scaled_prod n
    (fun j => if j = i then fun t => g t * f j t else f j) (fun j => by
      by_cases hji : j = i
      · subst j; simpa only [ite_true] using hg
      · simpa only [ite_eq_right hji] using hf j)
  convert! h using 1
  funext x
  exact (haarMode_prod_insert f g i (fun j => x j / (3 : ℝ) ^ n)).symm

/-- Distinct coordinate moments vanish when the first marginal moments vanish. -/
theorem haarMode_scaled_cross_zero (n : ℕ) (f : Fin d → ℝ → ℝ)
    (hf : ∀ i, (∫ t in -(1 / 2 : ℝ)..1 / 2, t * f i t) = 0)
    (i j : Fin d) (hij : i ≠ j) :
    cubeAverage (originCube d (n : ℤ)) (fun x =>
      (x i / (3 : ℝ) ^ n) * (x j / (3 : ℝ) ^ n) * ∏ k, f k (x k / (3 : ℝ) ^ n)) = 0 := by
  classical
  let f' := fun k => if k = j then fun t => t * f k t else f k
  have heq : (fun x : Homogenization.Vec d =>
      (x i / (3 : ℝ) ^ n) * (x j / (3 : ℝ) ^ n) * ∏ k, f k (x k / (3 : ℝ) ^ n)) =
      fun x => (x i / (3 : ℝ) ^ n) * ∏ k, f' k (x k / (3 : ℝ) ^ n) := by
    funext x
    rw [show (∏ k, f' k (x k / (3 : ℝ) ^ n)) =
      (x j / (3 : ℝ) ^ n) * ∏ k, f k (x k / (3 : ℝ) ^ n) from
        haarMode_prod_insert f id j (fun k => x k / (3 : ℝ) ^ n)]
    ring
  have hm := haarMode_cubeAverage_scaled_moment n f' id i
  simp only [id_eq] at hm
  rw [heq, hm]
  simp only [f', ite_eq_right hij, hf, zero_mul]

/-- Normalized cube expectation is linear over integrable finite sums. -/
theorem haarMode_average_sum {ι : Type*} (Q : Homogenization.TriadicCube d) (s : Finset ι)
    (f : ι → Homogenization.Vec d → ℝ)
    (hf : ∀ i ∈ s, Integrable (f i) (normalizedCubeMeasure Q)) :
    cubeAverage Q (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, cubeAverage Q (f i) := by
  simp only [cubeAverage_eq_integral_normalizedCubeMeasure]
  exact integral_finsetSum s hf

/-- Deterministic scalar factors commute with normalized cube expectation. -/
theorem haarMode_average_const_mul (Q : Homogenization.TriadicCube d) (c : ℝ)
    (f : Homogenization.Vec d → ℝ) :
    cubeAverage Q (fun x => c * f x) = c * cubeAverage Q f := by
  simp only [cubeAverage_eq_integral_normalizedCubeMeasure, integral_const_mul]

end GMCExplicitDelta.Localization
