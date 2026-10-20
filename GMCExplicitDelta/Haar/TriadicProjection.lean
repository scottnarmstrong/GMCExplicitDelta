module

public import Homogenization.Besov.Poincare.Projection

/-! Scalar triadic projections for H1, with volume-normalized pairings. -/
@[expose] public section

namespace GMCExplicitDelta.Haar

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

variable {d : ℕ}

/-- The volume-normalized scalar L² pairing on a triadic cube. -/
noncomputable def pairing (Q : TriadicCube d) (f g : Vec d → ℝ) : ℝ :=
  cubeAverage Q (fun x => f x * g x)

/-- The squared volume-normalized L² norm. -/
noncomputable def energy (Q : TriadicCube d) (f : Vec d → ℝ) : ℝ := pairing Q f f

theorem pairing_comm (Q : TriadicCube d) (f g : Vec d → ℝ) :
    pairing Q f g = pairing Q g f := by
  unfold pairing
  congr 1
  funext x
  exact mul_comm _ _

theorem pairing_sub_left (Q : TriadicCube d) {f g h : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hg : MemLp g 2 (normalizedCubeMeasure Q))
    (hh : MemLp h 2 (normalizedCubeMeasure Q)) :
    pairing Q (fun x => f x - g x) h = pairing Q f h - pairing Q g h := by
  simp only [pairing, cubeAverage_eq_integral_normalizedCubeMeasure, sub_mul]
  exact integral_sub (hf.integrable_mul hh) (hg.integrable_mul hh)

theorem pairing_sub_right (Q : TriadicCube d) {f g h : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hg : MemLp g 2 (normalizedCubeMeasure Q))
    (hh : MemLp h 2 (normalizedCubeMeasure Q)) :
    pairing Q f (fun x => g x - h x) = pairing Q f g - pairing Q f h := by
  rw [pairing_comm, pairing_sub_left Q hg hh hf, pairing_comm Q g, pairing_comm Q h]

theorem energy_nonneg (Q : TriadicCube d) (f : Vec d → ℝ) : 0 ≤ energy Q f := by
  unfold energy pairing
  rw [cubeAverage_eq_integral_normalizedCubeMeasure]
  exact integral_nonneg (fun x => mul_self_nonneg (f x))

theorem projection_memLp (Q : TriadicCube d) (k : ℕ) (f : Vec d → ℝ)
    (p : ℝ≥0∞) : MemLp (cubeProjection Q k f) p (normalizedCubeMeasure Q) := by
  classical
  unfold cubeProjection
  apply memLp_finsetSum
  intro R _
  exact (memLp_const (cubeAverage R f)).indicator (measurableSet_cubeSet R)

theorem increment_memLp (Q : TriadicCube d) (k : ℕ) (f : Vec d → ℝ) :
    MemLp (cubeIncrement Q k f) 2 (normalizedCubeMeasure Q) := by
  cases k with
  | zero => exact projection_memLp Q 0 f 2
  | succ k => exact (projection_memLp Q (k + 1) f 2).sub (projection_memLp Q k f 2)

/-- Projections retain the average on each cell of their own depth. -/
theorem projection_cell_average (Q R : TriadicCube d) (k : ℕ) (f : Vec d → ℝ)
    (hR : R ∈ descendantsAtDepth Q k) :
    cubeAverage R (cubeProjection Q k f) = cubeAverage R f :=
  cubeAverage_cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth f hR

/-- Coarse projection after fine projection. -/
theorem projection_projection_of_le (Q : TriadicCube d) {j k : ℕ} (hjk : j ≤ k)
    {f : Vec d → ℝ} (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    cubeProjection Q j (cubeProjection Q k f) = cubeProjection Q j f := by
  funext x
  by_cases hx : x ∈ cubeSet Q
  · obtain ⟨R, hR, hxR⟩ := exists_mem_descendantsAtDepth_of_mem_cubeSet j hx
    rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth _ hR hxR,
      cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth _ hR hxR]
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hjk
    exact cubeAverage_cubeProjection_add_eq_cubeAverage_of_mem_descendantsAtDepth_of_memLp f hR hf
  · rw [cubeProjection_eq_zero_of_not_mem_cubeSet Q _ _ hx,
      cubeProjection_eq_zero_of_not_mem_cubeSet Q _ _ hx]

/-- Idempotence holds even when the original function is not integrable. -/
theorem projection_idempotent (Q : TriadicCube d) (k : ℕ) (f : Vec d → ℝ) :
    cubeProjection Q k (cubeProjection Q k f) = cubeProjection Q k f := by
  funext x
  by_cases hx : x ∈ cubeSet Q
  · obtain ⟨R, hR, hxR⟩ := exists_mem_descendantsAtDepth_of_mem_cubeSet k hx
    rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth _ hR hxR,
      projection_cell_average Q R k f hR,
      cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth _ hR hxR]
  · rw [cubeProjection_eq_zero_of_not_mem_cubeSet Q _ _ hx,
      cubeProjection_eq_zero_of_not_mem_cubeSet Q _ _ hx]

/-- Fine projection fixes a coarser step function. -/
theorem projection_projection_of_ge (Q : TriadicCube d) {j k : ℕ} (hkj : k ≤ j)
    (f : Vec d → ℝ) :
    cubeProjection Q j (cubeProjection Q k f) = cubeProjection Q k f := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hkj
  funext x
  by_cases hx : x ∈ cubeSet Q
  · obtain ⟨R, hR, hxR⟩ := exists_mem_descendantsAtDepth_of_mem_cubeSet k hx
    obtain ⟨S, hS, hxS⟩ := exists_mem_descendantsAtDepth_of_mem_cubeSet n hxR
    rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth _
      (mem_descendantsAtDepth_add hR hS) hxS,
      cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth _ hR hxR]
    calc
      cubeAverage S (cubeProjection Q k f) = cubeAverage S (fun _ => cubeAverage R f) := by
        apply cubeAverage_congr_on_cubeSet
        intro y hy
        exact cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth f hR
          (cubeSet_subset_of_mem_descendantsAtDepth hS hy)
      _ = cubeAverage R f := cubeAverage_const _ _
  · rw [cubeProjection_eq_zero_of_not_mem_cubeSet Q _ _ hx,
      cubeProjection_eq_zero_of_not_mem_cubeSet Q _ _ hx]

theorem projection_projection (Q : TriadicCube d) (j k : ℕ) {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    cubeProjection Q j (cubeProjection Q k f) = cubeProjection Q (min j k) f := by
  rcases le_total j k with h | h
  · rw [min_eq_left h]
    exact projection_projection_of_le Q h hf
  · rw [min_eq_right h]
    exact projection_projection_of_ge Q h f

/-- The projected pairing is a finite average of products of cell averages. -/
theorem pairing_projection_right (Q : TriadicCube d) (k : ℕ) {f : Vec d → ℝ}
    (g : Vec d → ℝ) (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    pairing Q f (cubeProjection Q k g) =
      descendantsAverage Q k (fun R => cubeAverage R f * cubeAverage R g) := by
  unfold pairing
  have hint : IntegrableOn (fun x => f x * cubeProjection Q k g x) (cubeSet Q) volume :=
    integrableOn_of_integrable_normalizedCubeMeasure Q
      (hf.integrable_mul (projection_memLp Q k g 2))
  rw [cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q k
    (fun x => f x * cubeProjection Q k g x) hint]
  unfold descendantsAverage
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro R hR
  calc
    cubeAverage R (fun x => f x * cubeProjection Q k g x) =
        cubeAverage R (fun x => f x * cubeAverage R g) := by
      apply cubeAverage_congr_on_cubeSet
      intro x hx
      rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth g hR hx]
    _ = cubeAverage R f * cubeAverage R g := by
      simp only [cubeAverage_eq_integral_normalizedCubeMeasure, integral_mul_const]

/-- Self-adjointness for the normalized L² pairing. -/
theorem projection_selfAdjoint (Q : TriadicCube d) (k : ℕ) {f g : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    pairing Q (cubeProjection Q k f) g = pairing Q f (cubeProjection Q k g) := by
  rw [pairing_comm, pairing_projection_right Q k f hg, pairing_projection_right Q k g hf]
  congr 1
  funext R
  exact mul_comm _ _

theorem pairing_projections (Q : TriadicCube d) (j k : ℕ) {f g : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    pairing Q (cubeProjection Q j f) (cubeProjection Q k g) =
      pairing Q f (cubeProjection Q (min j k) g) := by
  rw [projection_selfAdjoint Q j hf (projection_memLp Q k g 2),
    projection_projection Q j k hg]

theorem energy_sub (Q : TriadicCube d) {f g : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    energy Q (fun x => f x - g x) = energy Q f - 2 * pairing Q f g + energy Q g := by
  unfold energy
  have hfg : MemLp (fun x => f x - g x) 2 (normalizedCubeMeasure Q) := hf.sub hg
  rw [pairing_sub_left Q hf hg hfg,
    pairing_sub_right Q hf hf hg, pairing_sub_right Q hg hf hg, pairing_comm Q g f]
  ring

theorem pairing_projection_energy (Q : TriadicCube d) (k : ℕ) {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    pairing Q f (cubeProjection Q k f) = energy Q (cubeProjection Q k f) := by
  unfold energy
  rw [projection_selfAdjoint Q k hf (projection_memLp Q k f 2), projection_idempotent]

/-- Orthogonal decomposition into the projection and its residual. -/
theorem energy_residual (Q : TriadicCube d) (k : ℕ) {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    energy Q (fun x => f x - cubeProjection Q k f x) =
      energy Q f - energy Q (cubeProjection Q k f) := by
  rw [energy_sub Q hf (projection_memLp Q k f 2), pairing_projection_energy Q k hf]
  ring

theorem energy_projection_le (Q : TriadicCube d) (k : ℕ) {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    energy Q (cubeProjection Q k f) ≤ energy Q f := by
  have h := energy_nonneg Q (fun x => f x - cubeProjection Q k f x)
  rw [energy_residual Q k hf] at h
  exact sub_nonneg.mp h

theorem energy_projection_zero (Q : TriadicCube d) (f : Vec d → ℝ) :
    energy Q (cubeProjection Q 0 f) = (cubeAverage Q f) ^ 2 := by
  unfold energy pairing
  calc
    cubeAverage Q (fun x => cubeProjection Q 0 f x * cubeProjection Q 0 f x) =
        cubeAverage Q (fun _ => cubeAverage Q f * cubeAverage Q f) := by
      apply cubeAverage_congr_on_cubeSet
      intro x hx
      rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth f
        (by simp : Q ∈ descendantsAtDepth Q 0) hx]
    _ = (cubeAverage Q f) ^ 2 := by rw [cubeAverage_const, pow_two]

/-- Successive Haar differences satisfy Pythagoras. -/
theorem energy_increment_succ (Q : TriadicCube d) (k : ℕ) {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    energy Q (cubeIncrement Q (k + 1) f) =
      energy Q (cubeProjection Q (k + 1) f) - energy Q (cubeProjection Q k f) := by
  rw [cubeIncrement_succ,
    energy_sub Q (projection_memLp Q (k + 1) f 2) (projection_memLp Q k f 2),
    pairing_projections Q (k + 1) k hf hf, min_eq_right (Nat.le_succ k),
    pairing_projection_energy Q k hf]
  ring

/-- Finite Haar Parseval identity, including the mean at index zero. -/
theorem energy_projection_sum (Q : TriadicCube d) (N : ℕ) {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    energy Q (cubeProjection Q N f) =
      ∑ k ∈ Finset.range (N + 1), energy Q (cubeIncrement Q k f) := by
  induction N with
  | zero => exact (Finset.sum_range_one (fun k => energy Q (cubeIncrement Q k f))).symm
  | succ N ih =>
    rw [Finset.sum_range_succ, energy_increment_succ Q N hf, ← ih]
    ring

/-- H1(d): every residual is bounded by the mean-zero energy. -/
theorem energy_residual_le_fluctuation (Q : TriadicCube d) (j : ℕ) {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    energy Q (fun x => f x - cubeProjection Q j f x) ≤
      energy Q f - (cubeAverage Q f) ^ 2 := by
  have h := energy_projection_le Q 0 (projection_memLp Q j f 2)
  rw [projection_projection_of_le Q (Nat.zero_le j) hf, energy_projection_zero] at h
  rw [energy_residual Q j hf]
  exact sub_le_sub_left h _

theorem pairing_const_right (Q : TriadicCube d) (f : Vec d → ℝ) (c : ℝ) :
    pairing Q f (fun _ => c) = cubeAverage Q f * c := by
  simp only [pairing, cubeAverage_eq_integral_normalizedCubeMeasure, integral_mul_const]

theorem energy_const (Q : TriadicCube d) (c : ℝ) :
    energy Q (fun _ => c) = c ^ 2 := by
  unfold energy pairing
  rw [cubeAverage_const, pow_two]

/-- H1(e) in squared form; the successor index is essential. -/
theorem energy_increment_succ_le_sub_const (Q : TriadicCube d) (n : ℕ)
    {f : Vec d → ℝ} (hf : MemLp f 2 (normalizedCubeMeasure Q)) (c : ℝ) :
    energy Q (cubeIncrement Q (n + 1) f) ≤
      energy Q (fun x => cubeProjection Q (n + 1) f x - c) := by
  have h := energy_nonneg Q (fun x => cubeProjection Q n f x - c)
  rw [energy_sub Q (projection_memLp Q n f 2) (memLp_const c),
    pairing_const_right, energy_const,
    cubeAverage_cubeProjection_eq_cubeAverage_of_memLp Q n f hf] at h
  rw [energy_sub Q (projection_memLp Q (n + 1) f 2) (memLp_const c),
    pairing_const_right, energy_const,
    cubeAverage_cubeProjection_eq_cubeAverage_of_memLp Q (n + 1) f hf,
    energy_increment_succ Q n hf]
  linarith only [h]

/-- The norm corresponding to `energy`. -/
noncomputable def l2Norm (Q : TriadicCube d) (f : Vec d → ℝ) : ℝ := Real.sqrt (energy Q f)

theorem increment_succ_norm_le_sub_const (Q : TriadicCube d) (n : ℕ)
    {f : Vec d → ℝ} (hf : MemLp f 2 (normalizedCubeMeasure Q)) (c : ℝ) :
    l2Norm Q (cubeIncrement Q (n + 1) f) ≤
      l2Norm Q (fun x => cubeProjection Q (n + 1) f x - c) :=
  Real.sqrt_le_sqrt (energy_increment_succ_le_sub_const Q n hf c)

/-- Distinct Haar levels are orthogonal, including the mean level. -/
theorem increments_orthogonal_of_lt (Q : TriadicCube d) {j k : ℕ} (hjk : j < k)
    {f g : Vec d → ℝ} (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    pairing Q (cubeIncrement Q j f) (cubeIncrement Q k g) = 0 := by
  cases k with
  | zero => omega
  | succ k =>
    cases j with
    | zero =>
      rw [cubeIncrement_zero, cubeIncrement_succ,
        pairing_sub_right Q (projection_memLp Q 0 f 2)
          (projection_memLp Q (k + 1) g 2) (projection_memLp Q k g 2),
        pairing_projections Q 0 (k + 1) hf hg, pairing_projections Q 0 k hf hg]
      simp only [Nat.zero_min, sub_self]
    | succ j =>
      rw [cubeIncrement_succ, cubeIncrement_succ]
      have hgsub : MemLp (fun x => cubeProjection Q (k + 1) g x - cubeProjection Q k g x)
          2 (normalizedCubeMeasure Q) :=
        (projection_memLp Q (k + 1) g 2).sub (projection_memLp Q k g 2)
      rw [pairing_sub_left Q (projection_memLp Q (j + 1) f 2)
        (projection_memLp Q j f 2) hgsub,
        pairing_sub_right Q (projection_memLp Q (j + 1) f 2)
          (projection_memLp Q (k + 1) g 2) (projection_memLp Q k g 2),
        pairing_sub_right Q (projection_memLp Q j f 2)
          (projection_memLp Q (k + 1) g 2) (projection_memLp Q k g 2)]
      rw [pairing_projections Q (j + 1) (k + 1) hf hg,
        pairing_projections Q (j + 1) k hf hg,
        pairing_projections Q j (k + 1) hf hg, pairing_projections Q j k hf hg,
        min_eq_left (by omega : j + 1 ≤ k + 1), min_eq_left (by omega : j + 1 ≤ k),
        min_eq_left (by omega : j ≤ k + 1), min_eq_left (by omega : j ≤ k)]
      ring

theorem increments_orthogonal (Q : TriadicCube d) {j k : ℕ} (hjk : j ≠ k)
    {f g : Vec d → ℝ} (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    pairing Q (cubeIncrement Q j f) (cubeIncrement Q k g) = 0 := by
  rcases lt_or_gt_of_ne hjk with h | h
  · exact increments_orthogonal_of_lt Q h hf hg
  · rw [pairing_comm]
    exact increments_orthogonal_of_lt Q h hg hf

/-- The hand-written energy agrees with the existing normalized L² norm. -/
theorem energy_eq_cubeLpNorm_sq (Q : TriadicCube d) {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    energy Q f = (cubeLpNorm Q 2 f) ^ 2 := by
  have h := cubeLpNorm_rpow_eq_cubeAverage_norm_rpow Q 2 f (by norm_num) (by norm_num) hf
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  unfold energy pairing
  simpa only [Real.norm_eq_abs, ← pow_two, sq_abs] using h.symm

theorem l2Norm_eq_cubeLpNorm (Q : TriadicCube d) {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    l2Norm Q f = cubeLpNorm Q 2 f := by
  rw [l2Norm, energy_eq_cubeLpNorm_sq Q hf, Real.sqrt_sq (cubeLpNorm_nonneg Q 2 f)]

theorem abs_pairing_le (Q : TriadicCube d) {f g : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    |pairing Q f g| ≤ l2Norm Q f * l2Norm Q g := by
  rw [l2Norm_eq_cubeLpNorm Q hf, l2Norm_eq_cubeLpNorm Q hg]
  exact abs_cubeAverage_mul_le_mul_cubeLpNorm_of_holderConjugate Q 2 2 f g hf hg

/-- A cellwise constant function is fixed on the cube by its projection. -/
theorem projection_eq_of_cellwise_constant (Q : TriadicCube d) (k : ℕ)
    (f : Vec d → ℝ)
    (hf : ∀ R ∈ descendantsAtDepth Q k, ∃ c : ℝ, ∀ x ∈ cubeSet R, f x = c)
    {x : Vec d} (hx : x ∈ cubeSet Q) : cubeProjection Q k f x = f x := by
  obtain ⟨R, hR, hxR⟩ := exists_mem_descendantsAtDepth_of_mem_cubeSet k hx
  obtain ⟨c, hc⟩ := hf R hR
  rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth f hR hxR, hc x hxR]
  calc
    cubeAverage R f = cubeAverage R (fun _ => c) := cubeAverage_congr_on_cubeSet hc
    _ = c := cubeAverage_const R c

theorem pairing_increment_succ (Q : TriadicCube d) (k : ℕ) {f g : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    pairing Q (cubeIncrement Q (k + 1) f) (cubeIncrement Q (k + 1) g) =
      pairing Q (cubeProjection Q (k + 1) f) (cubeProjection Q (k + 1) g) -
      pairing Q (cubeProjection Q k f) (cubeProjection Q k g) := by
  rw [cubeIncrement_succ, cubeIncrement_succ]
  have hgsub : MemLp (fun x => cubeProjection Q (k + 1) g x - cubeProjection Q k g x)
      2 (normalizedCubeMeasure Q) :=
    (projection_memLp Q (k + 1) g 2).sub (projection_memLp Q k g 2)
  rw [pairing_sub_left Q (projection_memLp Q (k + 1) f 2)
      (projection_memLp Q k f 2) hgsub,
    pairing_sub_right Q (projection_memLp Q (k + 1) f 2)
      (projection_memLp Q (k + 1) g 2) (projection_memLp Q k g 2),
    pairing_sub_right Q (projection_memLp Q k f 2)
      (projection_memLp Q (k + 1) g 2) (projection_memLp Q k g 2)]
  rw [pairing_projections Q (k + 1) (k + 1) hf hg,
    pairing_projections Q (k + 1) k hf hg, pairing_projections Q k (k + 1) hf hg,
    pairing_projections Q k k hf hg, min_self,
    min_eq_right (Nat.le_succ k), min_eq_left (Nat.le_succ k), min_self]
  ring

/-- Finite diagonal expansion of the pairing. -/
theorem pairing_projection_sum (Q : TriadicCube d) (N : ℕ) {f g : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    pairing Q (cubeProjection Q N f) (cubeProjection Q N g) =
      ∑ k ∈ Finset.range (N + 1), pairing Q (cubeIncrement Q k f) (cubeIncrement Q k g) := by
  induction N with
  | zero => exact (Finset.sum_range_one
      (fun k => pairing Q (cubeIncrement Q k f) (cubeIncrement Q k g))).symm
  | succ N ih =>
    rw [Finset.sum_range_succ, pairing_increment_succ Q N hf hg, ← ih]
    ring

/-- The range is exactly the depth-`k` cellwise constant functions on `Q`. -/
theorem projection_eq_iff_cellwise_constant (Q : TriadicCube d) (k : ℕ)
    (f : Vec d → ℝ) :
    (∀ x ∈ cubeSet Q, cubeProjection Q k f x = f x) ↔
      ∀ R ∈ descendantsAtDepth Q k, ∃ c : ℝ, ∀ x ∈ cubeSet R, f x = c := by
  constructor
  · intro hf R hR
    refine ⟨cubeAverage R f, ?_⟩
    intro x hx
    rw [← hf x (cubeSet_subset_of_mem_descendantsAtDepth hR hx)]
    exact cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth f hR hx
  · intro hf x hx
    exact projection_eq_of_cellwise_constant Q k f hf hx

theorem projection_add (Q : TriadicCube d) (k : ℕ) {f g : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    cubeProjection Q k (fun x => f x + g x) =
      fun x => cubeProjection Q k f x + cubeProjection Q k g x := by
  funext x
  by_cases hx : x ∈ cubeSet Q
  · obtain ⟨R, hR, hxR⟩ := exists_mem_descendantsAtDepth_of_mem_cubeSet k hx
    rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth _ hR hxR,
      cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth f hR hxR,
      cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth g hR hxR]
    simp only [cubeAverage_eq_integral_normalizedCubeMeasure]
    exact integral_add
      ((memLp_on_descendant_of_memLp hR hf).integrable (by norm_num))
      ((memLp_on_descendant_of_memLp hR hg).integrable (by norm_num))
  · rw [cubeProjection_eq_zero_of_not_mem_cubeSet Q _ _ hx,
      cubeProjection_eq_zero_of_not_mem_cubeSet Q _ _ hx,
      cubeProjection_eq_zero_of_not_mem_cubeSet Q _ _ hx, add_zero]

theorem projection_smul (Q : TriadicCube d) (k : ℕ) (f : Vec d → ℝ) (c : ℝ) :
    cubeProjection Q k (fun x => c * f x) = fun x => c * cubeProjection Q k f x := by
  funext x
  by_cases hx : x ∈ cubeSet Q
  · obtain ⟨R, hR, hxR⟩ := exists_mem_descendantsAtDepth_of_mem_cubeSet k hx
    rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth _ hR hxR,
      cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth f hR hxR]
    simp only [cubeAverage_eq_integral_normalizedCubeMeasure, integral_const_mul]
  · rw [cubeProjection_eq_zero_of_not_mem_cubeSet Q _ _ hx,
      cubeProjection_eq_zero_of_not_mem_cubeSet Q _ _ hx, mul_zero]

/-- The residual is orthogonal to every function in the projected range. -/
theorem pairing_residual_cellwise_constant (Q : TriadicCube d) (k : ℕ)
    {f g : Vec d → ℝ} (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hg : MemLp g 2 (normalizedCubeMeasure Q))
    (hgc : ∀ R ∈ descendantsAtDepth Q k, ∃ c : ℝ, ∀ x ∈ cubeSet R, g x = c) :
    pairing Q (fun x => f x - cubeProjection Q k f x) g = 0 := by
  rw [pairing_sub_left Q hf (projection_memLp Q k f 2) hg,
    projection_selfAdjoint Q k hf hg]
  have heq : pairing Q f (cubeProjection Q k g) = pairing Q f g := by
    apply cubeAverage_congr_on_cubeSet
    intro x hx
    rw [projection_eq_of_cellwise_constant Q k g hgc hx]
  rw [heq, sub_self]

/-- The usual mean-plus-positive-level form of finite Parseval. -/
theorem energy_projection_eq_mean_add (Q : TriadicCube d) (N : ℕ) {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    energy Q (cubeProjection Q N f) = (cubeAverage Q f) ^ 2 +
      ∑ k ∈ Finset.range N, energy Q (cubeIncrement Q (k + 1) f) := by
  rw [energy_projection_sum Q N hf, Finset.sum_range_succ', cubeIncrement_zero,
    energy_projection_zero, add_comm]

end GMCExplicitDelta.Haar
