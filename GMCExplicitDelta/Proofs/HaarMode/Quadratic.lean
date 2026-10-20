module

public import GMCExplicitDelta.Proofs.HaarMode.Moments

/-! # Quadratic affine moments under product weights -/

@[expose] public section

open MeasureTheory Homogenization Set
open scoped ENNReal

namespace GMCExplicitDelta.Localization

variable {d : ℕ}

/-- Integrability of degree-two coordinate moments under integrable product weights. -/
theorem haarMode_integrable_scaled_cross (n : ℕ) (f : Fin d → ℝ → ℝ)
    (hf : ∀ i r, r ≤ 2 → IntervalIntegrable (fun t => t ^ r * f i t) volume (-(1 / 2 : ℝ)) (1 / 2))
    (i j : Fin d) :
    Integrable (fun x : Homogenization.Vec d =>
      (x i / (3 : ℝ) ^ n) * (x j / (3 : ℝ) ^ n) * ∏ k, f k (x k / (3 : ℝ) ^ n))
      (normalizedCubeMeasure (originCube d (n : ℤ))) := by
  classical
  let f' := fun k => if k = j then fun t => t * f k t else f k
  have hf0 (k : Fin d) : IntervalIntegrable (f k) volume (-(1 / 2 : ℝ)) (1 / 2) := by
    simpa only [pow_zero, one_mul] using hf k 0 (by norm_num)
  have hf1 (k : Fin d) : IntervalIntegrable (fun t => t * f k t) volume (-(1 / 2 : ℝ)) (1 / 2) := by
    simpa only [pow_one] using hf k 1 (by norm_num)
  have hbase (k : Fin d) : IntervalIntegrable (f' k) volume (-(1 / 2 : ℝ)) (1 / 2) := by
    by_cases hk : k = j
    · subst k; simpa only [f', ite_true] using hf1 j
    · simpa only [f', ite_eq_right hk] using hf0 k
  have hi : IntervalIntegrable (fun t => t * f' i t) volume (-(1 / 2 : ℝ)) (1 / 2) := by
    by_cases hij : i = j
    · subst j
      simpa only [f', ite_true, ← mul_assoc, ← sq] using hf i 2 (by norm_num)
    · simpa only [f', ite_eq_right hij] using hf1 i
  have h := haarMode_integrable_scaled_moment n f' id i hbase hi
  convert! h using 1
  funext x
  rw [show (∏ k, f' k (x k / (3 : ℝ) ^ n)) =
      (x j / (3 : ℝ) ^ n) * ∏ k, f k (x k / (3 : ℝ) ^ n) from
        haarMode_prod_insert f id j (fun k => x k / (3 : ℝ) ^ n)]
  simp only [id_eq]
  ring

/-- Parity reduces a tensor-weighted affine quadratic form to its diagonal moments. -/
theorem haarMode_affine_quadratic (n : ℕ) (a : Homogenization.Vec d) (f : Fin d → ℝ → ℝ)
    (hf : ∀ i r, r ≤ 2 → IntervalIntegrable (fun t => t ^ r * f i t) volume (-(1 / 2 : ℝ)) (1 / 2))
    (hm : ∀ i, (∫ t in -(1 / 2 : ℝ)..1 / 2, t * f i t) = 0) :
    cubeAverage (originCube d (n : ℤ)) (fun x =>
      vecDot a (fun i => x i / (3 : ℝ) ^ n) ^ 2 * ∏ i, f i (x i / (3 : ℝ) ^ n)) =
      ∑ i, a i ^ 2 * (∫ t in -(1 / 2 : ℝ)..1 / 2, t ^ 2 * f i t) *
        ∏ j ∈ Finset.univ.erase i, ∫ t in -(1 / 2 : ℝ)..1 / 2, f j t := by
  classical
  have heq : (fun x : Homogenization.Vec d =>
      vecDot a (fun i => x i / (3 : ℝ) ^ n) ^ 2 * ∏ i, f i (x i / (3 : ℝ) ^ n)) =
      fun x => ∑ i, ∑ j, (a i * a j) *
        ((x i / (3 : ℝ) ^ n) * (x j / (3 : ℝ) ^ n) * ∏ k, f k (x k / (3 : ℝ) ^ n)) := by
    funext x
    simp only [vecDot, pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq, haarMode_average_sum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [haarMode_average_sum]
    · simp_rw [haarMode_average_const_mul]
      rw [Finset.sum_eq_single i]
      · simp only [← sq]
        rw [haarMode_cubeAverage_scaled_moment n f (fun t => t ^ 2) i]
        ring
      · intro j _ hji
        rw [haarMode_scaled_cross_zero n f hm i j hji.symm, mul_zero]
      · intro hi
        exact (hi (Finset.mem_univ i)).elim
    · intro j _
      exact (haarMode_integrable_scaled_cross n f hf i j).const_mul (a i * a j)
  · intro i _
    exact integrable_finsetSum Finset.univ fun j _ =>
      (haarMode_integrable_scaled_cross n f hf i j).const_mul (a i * a j)

/-- Fubini for the tensor-weighted first moment of an affine function. -/
theorem haarMode_affine_linear (n : ℕ) (a : Homogenization.Vec d) (f : Fin d → ℝ → ℝ)
    (hf0 : ∀ i, IntervalIntegrable (f i) volume (-(1 / 2 : ℝ)) (1 / 2))
    (hf1 : ∀ i, IntervalIntegrable (fun t => t * f i t) volume (-(1 / 2 : ℝ)) (1 / 2)) :
    cubeAverage (originCube d (n : ℤ)) (fun x =>
      vecDot a (fun i => x i / (3 : ℝ) ^ n) * ∏ i, f i (x i / (3 : ℝ) ^ n)) =
      ∑ i, a i * (∫ t in -(1 / 2 : ℝ)..1 / 2, t * f i t) *
        ∏ j ∈ Finset.univ.erase i, ∫ t in -(1 / 2 : ℝ)..1 / 2, f j t := by
  have heq : (fun x : Homogenization.Vec d =>
      vecDot a (fun i => x i / (3 : ℝ) ^ n) * ∏ i, f i (x i / (3 : ℝ) ^ n)) =
      fun x => ∑ i, a i * ((x i / (3 : ℝ) ^ n) * ∏ k, f k (x k / (3 : ℝ) ^ n)) := by
    funext x
    simp only [vecDot, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq, haarMode_average_sum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [haarMode_average_const_mul]
    have hi := haarMode_cubeAverage_scaled_moment n f id i
    simp only [id_eq] at hi
    rw [hi]
    ring
  · intro i _
    exact (haarMode_integrable_scaled_moment n f id i hf0 (hf1 i)).const_mul (a i)

/-- Integrability of an affine function against a tensor weight. -/
theorem haarMode_integrable_affine (n : ℕ) (a : Homogenization.Vec d) (f : Fin d → ℝ → ℝ)
    (hf : ∀ i r, r ≤ 2 → IntervalIntegrable (fun t => t ^ r * f i t) volume (-(1 / 2 : ℝ)) (1 / 2)) :
    Integrable (fun x : Homogenization.Vec d =>
      vecDot a (fun i => x i / (3 : ℝ) ^ n) * ∏ i, f i (x i / (3 : ℝ) ^ n))
      (normalizedCubeMeasure (originCube d (n : ℤ))) := by
  have hh := integrable_finsetSum Finset.univ fun i _ =>
    (haarMode_integrable_scaled_moment n f id i
      (fun k => by simpa using hf k 0 (by norm_num))
      (by simpa using hf i 1 (by norm_num))).const_mul (a i)
  convert! hh using 1
  funext x
  simp only [vecDot, Finset.sum_mul, id_eq]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Integrability of an affine square against a tensor weight. -/
theorem haarMode_integrable_affine_sq (n : ℕ) (a : Homogenization.Vec d) (f : Fin d → ℝ → ℝ)
    (hf : ∀ i r, r ≤ 2 → IntervalIntegrable (fun t => t ^ r * f i t) volume (-(1 / 2 : ℝ)) (1 / 2)) :
    Integrable (fun x : Homogenization.Vec d =>
      vecDot a (fun i => x i / (3 : ℝ) ^ n) ^ 2 * ∏ i, f i (x i / (3 : ℝ) ^ n))
      (normalizedCubeMeasure (originCube d (n : ℤ))) := by
  have hh := integrable_finsetSum Finset.univ fun i _ =>
    integrable_finsetSum Finset.univ fun j _ =>
      (haarMode_integrable_scaled_cross n f hf i j).const_mul (a i * a j)
  convert! hh using 1
  funext x
  simp only [vecDot, pow_two, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end GMCExplicitDelta.Localization
