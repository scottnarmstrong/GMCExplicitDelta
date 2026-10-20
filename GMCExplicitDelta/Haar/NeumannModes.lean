module

public import GMCExplicitDelta.Haar.NeumannSpectral
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Box modes with natural frequencies: orthogonality, norms, line derivatives

For `q : Fin d → ℕ` the box modes `boxMode a ℓ O q` (sine in the coordinates of `O`, cosine
elsewhere) are orthogonal for the normalized box measure, with
`⨍ boxMode O q ^ 2 = boxNormSq O q = ∏ᵢ (1/2, or 1 resp. 0 when qᵢ = 0)`. Hence
`⨍ (∑_{q ∈ S} b_q boxMode O q)² = ∑_{q ∈ S} b_q² boxNormSq O q`. Along a coordinate line a box mode
differentiates into `±(π nᵢ/ℓ)` times the box mode with the `i`-th factor switched.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open Homogenization

namespace GMCExplicitDelta.Haar.Torus

variable {d : ℕ}

/-- Normalized Lebesgue measure on `[a, a + ℓ)`. -/
def segMeasure (a ℓ : ℝ) : Measure ℝ := ENNReal.ofReal ℓ⁻¹ • volume.restrict (Ico a (a + ℓ))

instance (a ℓ : ℝ) : IsFiniteMeasure (segMeasure a ℓ) := isFiniteMeasure_smul_restrict_Ico a ℓ

theorem boxMeasure_eq_pi (a : Fin d → ℝ) (ℓ : ℝ) :
    boxMeasure a ℓ = Measure.pi fun i => segMeasure (a i) ℓ := rfl

instance (a : Fin d → ℝ) (ℓ : ℝ) : IsFiniteMeasure (boxMeasure a ℓ) := by
  rw [boxMeasure_eq_pi]
  infer_instance

theorem integrable_of_continuous_bound {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ] {f : X → ℝ}
    (hf : Continuous f) (C : ℝ) (hC : ∀ x, |f x| ≤ C) : Integrable f μ :=
  Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)

theorem memLp_of_continuous_bound {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ] {f : X → ℝ}
    (hf : Continuous f) (C : ℝ) (hC : ∀ x, |f x| ≤ C) (p : ENNReal) : MemLp f p μ :=
  MemLp.of_bound hf.aestronglyMeasurable C
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)

theorem integral_segMeasure (a : ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) (f : ℝ → ℝ) :
    ∫ t, f t ∂segMeasure a ℓ = ℓ⁻¹ * ∫ t in a..a + ℓ, f t := by
  rw [segMeasure, integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.2 hℓ.le), smul_eq_mul,
    intervalIntegral.integral_of_le (by linarith), integral_Ico_eq_integral_Ioo,
    integral_Ioc_eq_integral_Ioo]

theorem integrable_segMeasure {a ℓ : ℝ} {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable f (segMeasure a ℓ) :=
  ((hf.integrableOn_Icc (a := a) (b := a + ℓ)).mono_set Ico_subset_Icc_self).smul_measure
    ENNReal.ofReal_ne_top

/-- `⨍ cos(π m (t - a)/ℓ) = 𝟙[m = 0]` on `[a, a + ℓ)`. -/
theorem integral_cos_seg (a : ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) (m : ℤ) :
    ∫ t, Real.cos (Real.pi * m * (t - a) / ℓ) ∂segMeasure a ℓ = if m = 0 then 1 else 0 := by
  have hℓ' : ℓ ≠ 0 := hℓ.ne'
  rw [integral_segMeasure a hℓ]
  split_ifs with hm
  · subst hm
    simp [hℓ.ne']
  · have hπm : Real.pi * (m : ℝ) ≠ 0 := mul_ne_zero Real.pi_ne_zero (Int.cast_ne_zero.2 hm)
    have hderiv : ∀ t, HasDerivAt
        (fun t => ℓ / (Real.pi * m) * Real.sin (Real.pi * m * (t - a) / ℓ))
        (Real.cos (Real.pi * m * (t - a) / ℓ)) t := by
      intro t
      have h1 : HasDerivAt (fun t => Real.pi * m * (t - a) / ℓ) (Real.pi * m / ℓ) t := by
        simpa using (((hasDerivAt_id t).sub_const a).const_mul (Real.pi * m)).div_const ℓ
      have h2 := ((Real.hasDerivAt_sin _).comp t h1).const_mul (ℓ / (Real.pi * m))
      exact h2.congr_deriv (by field_simp)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
      ((by fun_prop : Continuous fun t => Real.cos (Real.pi * m * (t - a) / ℓ)).intervalIntegrable
        _ _)]
    have e : Real.pi * m * (a + ℓ - a) / ℓ = (m : ℝ) * Real.pi := by
      field_simp
      ring
    rw [e, Real.sin_int_mul_pi]
    simp

theorem cos_mul_cos_nat (a ℓ t : ℝ) (q q' : ℕ) :
    Real.cos (Real.pi * ((q : ℤ) : ℝ) * (t - a) / ℓ) *
        Real.cos (Real.pi * ((q' : ℤ) : ℝ) * (t - a) / ℓ) =
      (Real.cos (Real.pi * (((q : ℤ) - q' : ℤ) : ℝ) * (t - a) / ℓ) +
        Real.cos (Real.pi * (((q : ℤ) + q' : ℤ) : ℝ) * (t - a) / ℓ)) / 2 := by
  push_cast
  have e1 : Real.pi * ((q : ℝ) - q') * (t - a) / ℓ =
      Real.pi * q * (t - a) / ℓ - Real.pi * q' * (t - a) / ℓ := by ring
  have e2 : Real.pi * ((q : ℝ) + q') * (t - a) / ℓ =
      Real.pi * q * (t - a) / ℓ + Real.pi * q' * (t - a) / ℓ := by ring
  rw [e1, e2, Real.cos_sub, Real.cos_add]
  ring

theorem sin_mul_sin_nat (a ℓ t : ℝ) (q q' : ℕ) :
    Real.sin (Real.pi * ((q : ℤ) : ℝ) * (t - a) / ℓ) *
        Real.sin (Real.pi * ((q' : ℤ) : ℝ) * (t - a) / ℓ) =
      (Real.cos (Real.pi * (((q : ℤ) - q' : ℤ) : ℝ) * (t - a) / ℓ) -
        Real.cos (Real.pi * (((q : ℤ) + q' : ℤ) : ℝ) * (t - a) / ℓ)) / 2 := by
  push_cast
  have e1 : Real.pi * ((q : ℝ) - q') * (t - a) / ℓ =
      Real.pi * q * (t - a) / ℓ - Real.pi * q' * (t - a) / ℓ := by ring
  have e2 : Real.pi * ((q : ℝ) + q') * (t - a) / ℓ =
      Real.pi * q * (t - a) / ℓ + Real.pi * q' * (t - a) / ℓ := by ring
  rw [e1, e2, Real.cos_sub, Real.cos_add]
  ring

theorem integral_cos_mul_cos_seg (a : ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) (q q' : ℕ) :
    ∫ t, Real.cos (Real.pi * ((q : ℤ) : ℝ) * (t - a) / ℓ) *
        Real.cos (Real.pi * ((q' : ℤ) : ℝ) * (t - a) / ℓ) ∂segMeasure a ℓ =
      if q = q' then (if q = 0 then 1 else 1 / 2) else 0 := by
  have i1 : Integrable (fun t => Real.cos (Real.pi * (((q : ℤ) - q' : ℤ) : ℝ) * (t - a) / ℓ))
      (segMeasure a ℓ) := integrable_segMeasure (by fun_prop)
  have i2 : Integrable (fun t => Real.cos (Real.pi * (((q : ℤ) + q' : ℤ) : ℝ) * (t - a) / ℓ))
      (segMeasure a ℓ) := integrable_segMeasure (by fun_prop)
  simp_rw [cos_mul_cos_nat a ℓ]
  rw [integral_div, integral_add i1 i2, integral_cos_seg a hℓ, integral_cos_seg a hℓ]
  by_cases hqq : q = q'
  · subst hqq
    rw [if_pos (sub_self _), if_pos rfl]
    by_cases hq0 : q = 0
    · rw [if_pos (by simp [hq0]), if_pos hq0]
      norm_num
    · rw [if_neg (by omega), if_neg hq0]
      norm_num
  · rw [if_neg (by omega), if_neg (by omega), if_neg hqq]
    norm_num

theorem integral_sin_mul_sin_seg (a : ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) (q q' : ℕ) :
    ∫ t, Real.sin (Real.pi * ((q : ℤ) : ℝ) * (t - a) / ℓ) *
        Real.sin (Real.pi * ((q' : ℤ) : ℝ) * (t - a) / ℓ) ∂segMeasure a ℓ =
      if q = q' then (if q = 0 then 0 else 1 / 2) else 0 := by
  have i1 : Integrable (fun t => Real.cos (Real.pi * (((q : ℤ) - q' : ℤ) : ℝ) * (t - a) / ℓ))
      (segMeasure a ℓ) := integrable_segMeasure (by fun_prop)
  have i2 : Integrable (fun t => Real.cos (Real.pi * (((q : ℤ) + q' : ℤ) : ℝ) * (t - a) / ℓ))
      (segMeasure a ℓ) := integrable_segMeasure (by fun_prop)
  simp_rw [sin_mul_sin_nat a ℓ]
  rw [integral_div, integral_sub i1 i2, integral_cos_seg a hℓ, integral_cos_seg a hℓ]
  by_cases hqq : q = q'
  · subst hqq
    rw [if_pos (sub_self _), if_pos rfl]
    by_cases hq0 : q = 0
    · rw [if_pos (by simp [hq0]), if_pos hq0]
      norm_num
    · rw [if_neg (by omega), if_neg hq0]
      norm_num
  · rw [if_neg (by omega), if_neg (by omega), if_neg hqq]
    norm_num

/-! ### Box modes with natural frequencies -/

/-- The natural frequency vector as an integer vector. -/
def natVec (q : Fin d → ℕ) : Fin d → ℤ := fun i => (q i : ℤ)

/-- The one-dimensional squared norms: `⨍ sin² = 1/2` (`0` if `q = 0`), `⨍ cos² = 1/2` (`1` if
`q = 0`). -/
def factorNormSq (O : Finset (Fin d)) (q : Fin d → ℕ) (i : Fin d) : ℝ :=
  if i ∈ O then (if q i = 0 then 0 else 1 / 2) else (if q i = 0 then 1 else 1 / 2)

/-- `⨍ boxMode O q ^ 2`. -/
def boxNormSq (O : Finset (Fin d)) (q : Fin d → ℕ) : ℝ :=
  ∏ i, factorNormSq O q i

theorem integral_modeFactor_mul (a : Fin d → ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) (O : Finset (Fin d))
    (q q' : Fin d → ℕ) (i : Fin d) :
    ∫ t, modeFactor a ℓ O (natVec q) i t * modeFactor a ℓ O (natVec q') i t
        ∂segMeasure (a i) ℓ =
      if q i = q' i then factorNormSq O q i else 0 := by
  by_cases hi : i ∈ O
  · simp only [modeFactor, hi, ite_true, natVec, factorNormSq]
    exact integral_sin_mul_sin_seg (a i) hℓ (q i) (q' i)
  · simp only [modeFactor, hi, ite_false, natVec, factorNormSq]
    exact integral_cos_mul_cos_seg (a i) hℓ (q i) (q' i)

/-- **Orthogonality of box modes.** -/
theorem integral_boxMode_mul_boxMode (a : Fin d → ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) (O : Finset (Fin d))
    (q q' : Fin d → ℕ) :
    ∫ x, boxMode a ℓ O (natVec q) x * boxMode a ℓ O (natVec q') x ∂boxMeasure a ℓ =
      if q = q' then boxNormSq O q else 0 := by
  have hfun : (fun x => boxMode a ℓ O (natVec q) x * boxMode a ℓ O (natVec q') x) =
      fun x => ∏ i, (fun i t => modeFactor a ℓ O (natVec q) i t *
        modeFactor a ℓ O (natVec q') i t) i (x i) := by
    funext x
    rw [boxMode_eq_prod_modeFactor, boxMode_eq_prod_modeFactor, ← Finset.prod_mul_distrib]
  rw [hfun, boxMeasure_eq_pi]
  refine (integral_fintype_prod_eq_prod (𝕜 := ℝ) (fun i t => modeFactor a ℓ O (natVec q) i t *
    modeFactor a ℓ O (natVec q') i t) (μ := fun i => segMeasure (a i) ℓ)).trans ?_
  simp only [integral_modeFactor_mul a hℓ O q q']
  by_cases hqq : q = q'
  · subst hqq
    simp [boxNormSq]
  · rw [if_neg hqq]
    obtain ⟨i, hi⟩ : ∃ i, q i ≠ q' i := by
      by_contra h
      push_neg at h
      exact hqq (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem continuous_sum_boxMode (a : Fin d → ℝ) (ℓ : ℝ) (O : Finset (Fin d))
    (S : Finset (Fin d → ℕ)) (b : (Fin d → ℕ) → ℝ) :
    Continuous fun x => ∑ q ∈ S, b q * boxMode a ℓ O (natVec q) x :=
  continuous_finsetSum _ fun q _ => continuous_const.mul (continuous_boxMode a ℓ O _)

theorem abs_sum_boxMode_le (a : Fin d → ℝ) (ℓ : ℝ) (O : Finset (Fin d))
    (S : Finset (Fin d → ℕ)) (b : (Fin d → ℕ) → ℝ) (x : Fin d → ℝ) :
    |∑ q ∈ S, b q * boxMode a ℓ O (natVec q) x| ≤ ∑ q ∈ S, |b q| := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun q _ => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (abs_boxMode_le a ℓ O _ x)

/-- **Norm of a box-mode polynomial.** -/
theorem integral_sq_sum_boxMode (a : Fin d → ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) (O : Finset (Fin d))
    (S : Finset (Fin d → ℕ)) (b : (Fin d → ℕ) → ℝ) :
    ∫ x, (∑ q ∈ S, b q * boxMode a ℓ O (natVec q) x) ^ 2 ∂boxMeasure a ℓ =
      ∑ q ∈ S, b q ^ 2 * boxNormSq O q := by
  have hsq : ∀ x, (∑ q ∈ S, b q * boxMode a ℓ O (natVec q) x) ^ 2 =
      ∑ q ∈ S, ∑ q' ∈ S, b q * b q' *
        (boxMode a ℓ O (natVec q) x * boxMode a ℓ O (natVec q') x) := by
    intro x
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun q' _ => ?_
    ring
  have hint : ∀ q q', Integrable (fun x => b q * b q' *
      (boxMode a ℓ O (natVec q) x * boxMode a ℓ O (natVec q') x)) (boxMeasure a ℓ) := by
    intro q q'
    refine (integrable_of_continuous_bound ((continuous_boxMode a ℓ O _).mul
      (continuous_boxMode a ℓ O _)) 1 fun x => ?_).const_mul _
    rw [Pi.mul_apply, abs_mul]
    exact (mul_le_mul (abs_boxMode_le a ℓ O _ x) (abs_boxMode_le a ℓ O _ x) (abs_nonneg _)
      zero_le_one).trans (le_of_eq (one_mul 1))
  simp_rw [hsq]
  rw [integral_finsetSum _ fun q _ => integrable_finsetSum _ fun q' _ => hint q q']
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [integral_finsetSum _ fun q' _ => hint q q']
  simp only [integral_const_mul, integral_boxMode_mul_boxMode a hℓ O q, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq S q (fun q' => b q * b q' * boxNormSq O q), if_pos hq]
  ring

/-! ### Derivatives along coordinate lines -/

theorem boxMode_update (a : Fin d → ℝ) (ℓ : ℝ) (O : Finset (Fin d)) (n : Fin d → ℤ) (i : Fin d)
    (x : Fin d → ℝ) (t : ℝ) :
    boxMode a ℓ O n (Function.update x i t) =
      modeFactor a ℓ O n i t * ∏ k ∈ Finset.univ.erase i, modeFactor a ℓ O n k (x k) := by
  classical
  rw [boxMode_eq_prod_modeFactor, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun k hk => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]

theorem prod_erase_modeFactor_congr (a : Fin d → ℝ) (ℓ : ℝ) {O O' : Finset (Fin d)}
    (n : Fin d → ℤ) (i : Fin d) (x : Fin d → ℝ) (h : ∀ k, k ≠ i → (k ∈ O ↔ k ∈ O')) :
    ∏ k ∈ Finset.univ.erase i, modeFactor a ℓ O n k (x k) =
      ∏ k ∈ Finset.univ.erase i, modeFactor a ℓ O' n k (x k) := by
  refine Finset.prod_congr rfl fun k hk => ?_
  have hki := h k (Finset.ne_of_mem_erase hk)
  by_cases hkO : k ∈ O
  · simp [modeFactor, hkO, hki.1 hkO]
  · have : k ∉ O' := fun h' => hkO (hki.2 h')
    simp [modeFactor, hkO, this]

/-- **Line derivative of a box mode.** -/
theorem hasDerivAt_boxMode_update (a : Fin d → ℝ) (ℓ : ℝ) (O : Finset (Fin d)) (n : Fin d → ℤ)
    (i : Fin d) (x : Fin d → ℝ) :
    HasDerivAt (fun t => boxMode a ℓ O n (Function.update x i t))
      (if i ∈ O then Real.pi * n i / ℓ * boxMode a ℓ (O.erase i) n x
        else -(Real.pi * n i / ℓ) * boxMode a ℓ (insert i O) n x) (x i) := by
  classical
  simp_rw [boxMode_update a ℓ O n i x]
  by_cases hi : i ∈ O
  · rw [if_pos hi]
    have hmf : modeFactor a ℓ O n i = modeFactor a ℓ {i} n i := by
      rw [modeFactor_of_mem a ℓ n hi, modeFactor_of_mem a ℓ n (Finset.mem_singleton_self i)]
    have hmf' : modeFactor a ℓ (O.erase i) n i = modeFactor a ℓ ∅ n i := by
      rw [modeFactor_of_notMem a ℓ n (Finset.notMem_erase i O),
        modeFactor_of_notMem a ℓ n (Finset.notMem_empty i)]
    have hD := (hasDerivAt_modeFactor_sin a ℓ n i (x i)).mul_const
      (∏ k ∈ Finset.univ.erase i, modeFactor a ℓ O n k (x k))
    rw [← hmf, ← hmf'] at hD
    convert hD using 1
    rw [boxMode_eq_prod_modeFactor, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      prod_erase_modeFactor_congr a ℓ n i x (O := O.erase i) (O' := O)
        (fun k hk => by simp [hk])]
    ring
  · rw [if_neg hi]
    have hmf : modeFactor a ℓ O n i = modeFactor a ℓ ∅ n i := by
      rw [modeFactor_of_notMem a ℓ n hi, modeFactor_of_notMem a ℓ n (Finset.notMem_empty i)]
    have hmf' : modeFactor a ℓ (insert i O) n i = modeFactor a ℓ {i} n i := by
      rw [modeFactor_of_mem a ℓ n (Finset.mem_insert_self i O),
        modeFactor_of_mem a ℓ n (Finset.mem_singleton_self i)]
    have hD := (hasDerivAt_modeFactor_cos a ℓ n i (x i)).mul_const
      (∏ k ∈ Finset.univ.erase i, modeFactor a ℓ O n k (x k))
    rw [← hmf, ← hmf'] at hD
    convert hD using 1
    rw [boxMode_eq_prod_modeFactor, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      prod_erase_modeFactor_congr a ℓ n i x (O := insert i O) (O' := O)
        (fun k hk => by simp [hk])]
    ring

end GMCExplicitDelta.Haar.Torus
