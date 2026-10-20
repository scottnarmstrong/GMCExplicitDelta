module

public import Homogenization.Sobolev.H1.BasicLemmas
public import GMCExplicitDelta.Localization.HaarMinkowski
public import GMCExplicitDelta.Haar.TriadicDualNorms
public import GMCExplicitDelta.Localization.Basic

/-!
Pieces of the localization argument on the good event (steps L2, G1).
Helper declarations live in the namespace `Localization.GradPieces`.

# Localization pieces: Haar projections of vector fields through cell averages

* `sum_energy_projection`: `‖E_k G‖² = avg_R |(G)_R|²`;
* `incNorm_sq_le_proj`: `‖D_k G‖² ≤ ‖E_k G‖²` for `k ≥ 1`;
* `incNorm_le_drop`: `‖D_k G‖ ≤ (avg_R |(G)_R - S_R|²)^{1/2} + (avg_R |S_R - c|²)^{1/2}` for `k ≥ 1`
  (H1(e) with a constant `c`, then Minkowski over the cells).
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open scoped ENNReal

namespace GMCExplicitDelta.Localization.GradPieces

variable {d : ℕ}

theorem incNorm_sq_eq (Q : Homogenization.TriadicCube d) (k : ℕ)
    (G : Homogenization.Vec d → Homogenization.Vec d) :
    incNorm Q k G ^ 2 = ∑ i, Haar.energy Q (cubeIncrement Q k fun x => G x i) := by
  unfold incNorm
  exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => Haar.energy_nonneg _ _)

theorem incNorm_nonneg' (Q : Homogenization.TriadicCube d) (k : ℕ)
    (G : Homogenization.Vec d → Homogenization.Vec d) : 0 ≤ incNorm Q k G :=
  Real.sqrt_nonneg _

theorem energy_projection_eq_avg (Q : Homogenization.TriadicCube d) (k : ℕ) {f : Homogenization.Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    Haar.energy Q (cubeProjection Q k f) =
      descendantsAverage Q k (fun R => cubeAverage R f * cubeAverage R f) := by
  rw [← Haar.pairing_projection_energy Q k hf]
  exact Haar.pairing_projection_right Q k f hf

theorem vecNormSq_cubeAverageVec_eq (R : Homogenization.TriadicCube d)
    (G : Homogenization.Vec d → Homogenization.Vec d) :
    vecNormSq (cubeAverageVec R G) = ∑ i, cubeAverage R (fun x => G x i) *
      cubeAverage R (fun x => G x i) := rfl

theorem descendantsAverage_sum (Q : Homogenization.TriadicCube d) (k : ℕ) {ι : Type*}
    (s : Finset ι) (F : ι → Homogenization.TriadicCube d → ℝ) :
    ∑ i ∈ s, descendantsAverage Q k (F i) = descendantsAverage Q k (fun R => ∑ i ∈ s, F i R) := by
  simp only [descendantsAverage_eq]
  rw [← Finset.mul_sum, Finset.sum_comm]

theorem sum_energy_projection (Q : Homogenization.TriadicCube d) (k : ℕ)
    {G : Homogenization.Vec d → Homogenization.Vec d}
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q)) :
    ∑ i, Haar.energy Q (cubeProjection Q k fun x => G x i) =
      descendantsAverage Q k (fun R => vecNormSq (cubeAverageVec R G)) := by
  simp_rw [energy_projection_eq_avg Q k (hG _), vecNormSq_cubeAverageVec_eq]
  exact descendantsAverage_sum Q k Finset.univ _

/-- `‖D_k G‖² ≤ ‖E_k G‖²` for `k ≥ 1`. -/
theorem incNorm_sq_le_proj (Q : Homogenization.TriadicCube d) {k : ℕ} (hk : 1 ≤ k)
    {G : Homogenization.Vec d → Homogenization.Vec d}
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q)) :
    incNorm Q k G ^ 2 ≤ descendantsAverage Q k (fun R => vecNormSq (cubeAverageVec R G)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [incNorm_sq_eq, ← sum_energy_projection Q _ hG]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Haar.energy_increment_succ Q j (hG i)]
  have := Haar.energy_nonneg Q (cubeProjection Q j fun x => G x i)
  linarith

theorem descAvg_sq_sub (Q : Homogenization.TriadicCube d) (k : ℕ)
    (a : Homogenization.TriadicCube d → ℝ) (c : ℝ) :
    descendantsAverage Q k (fun R => (a R - c) ^ 2) =
      descendantsAverage Q k (fun R => a R * a R) - 2 * c * descendantsAverage Q k a + c ^ 2 := by
  have hpos := card_descendantsAtDepth_pos Q k
  simp only [descendantsAverage_eq]
  have e : ∀ R, (a R - c) ^ 2 = a R * a R - 2 * c * a R + c ^ 2 := fun R => by ring
  simp_rw [e]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    nsmul_eq_mul]
  field_simp

theorem energy_sub_const_eq_avg (Q : Homogenization.TriadicCube d) (k : ℕ)
    {f : Homogenization.Vec d → ℝ} (hf : MemLp f 2 (normalizedCubeMeasure Q)) (c : ℝ) :
    Haar.energy Q (fun x => cubeProjection Q k f x - c) =
      descendantsAverage Q k (fun R => (cubeAverage R f - c) ^ 2) := by
  rw [descAvg_sq_sub, Haar.energy_sub Q (Haar.projection_memLp Q k f 2) (memLp_const c),
    Haar.pairing_const_right, Haar.energy_const,
    cubeAverage_cubeProjection_eq_cubeAverage_of_memLp Q k f hf, energy_projection_eq_avg Q k hf]
  have hint : IntegrableOn f (cubeSet Q) volume :=
    integrableOn_of_integrable_normalizedCubeMeasure Q (hf.integrable one_le_two)
  have h := cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q k f hint
  rw [← h]
  ring

/-- H1(e), summed over components: `‖D_k G‖² ≤ avg_R |(G)_R - c|²` for `k ≥ 1`. -/
theorem incNorm_sq_le_const (Q : Homogenization.TriadicCube d) {k : ℕ} (hk : 1 ≤ k)
    {G : Homogenization.Vec d → Homogenization.Vec d}
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q)) (c : Homogenization.Vec d) :
    incNorm Q k G ^ 2 ≤
      descendantsAverage Q k (fun R => vecNormSq (cubeAverageVec R G - c)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [incNorm_sq_eq]
  calc ∑ i, Haar.energy Q (cubeIncrement Q (j + 1) fun x => G x i) ≤
      ∑ i, Haar.energy Q (fun x => cubeProjection Q (j + 1) (fun y => G y i) x - c i) :=
        Finset.sum_le_sum fun i _ => Haar.energy_increment_succ_le_sub_const Q j (hG i) (c i)
    _ = ∑ i, descendantsAverage Q (j + 1)
          (fun R => (cubeAverage R (fun y => G y i) - c i) ^ 2) :=
        Finset.sum_congr rfl fun i _ => energy_sub_const_eq_avg Q _ (hG i) (c i)
    _ = _ := by
        rw [descendantsAverage_sum]
        refine descendantsAverage_congr' Q _ fun R _ => ?_
        simp only [vecNormSq, vecDot, cubeAverageVec, Pi.sub_apply]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring

theorem vecNormSq_add_le (x y : Homogenization.Vec d) :
    vecNormSq (x + y) ≤ (Real.sqrt (vecNormSq x) + Real.sqrt (vecNormSq y)) ^ 2 := by
  have h1 : vecNormSq (x + y) = vecNormSq x + 2 * vecDot x y + vecNormSq y := by
    simp only [vecNormSq, vecDot_add_left, vecDot_add_right, vecDot_comm y x]
    ring
  have h2 : vecDot x y ≤ Real.sqrt (vecNormSq x) * Real.sqrt (vecNormSq y) := by
    have := (le_abs_self (vecDot x y)).trans
      (Real.abs_le_sqrt (sq_vecDot_le_vecNormSq_mul_vecNormSq x y))
    rwa [Real.sqrt_mul (vecNormSq_nonneg x)] at this
  have h3 := Real.sq_sqrt (vecNormSq_nonneg x)
  have h4 := Real.sq_sqrt (vecNormSq_nonneg y)
  rw [h1]
  nlinarith [h2, h3, h4]

/-- Minkowski for the cell average of squared vector norms. -/
theorem sqrt_avg_add_le (Q : Homogenization.TriadicCube d) (k : ℕ)
    (A B : Homogenization.TriadicCube d → Homogenization.Vec d) :
    Real.sqrt (descendantsAverage Q k (fun R => vecNormSq (A R + B R))) ≤
      Real.sqrt (descendantsAverage Q k (fun R => vecNormSq (A R))) +
        Real.sqrt (descendantsAverage Q k (fun R => vecNormSq (B R))) := by
  have hpos := card_descendantsAtDepth_pos Q k
  set N := ((descendantsAtDepth Q k).card : ℝ)⁻¹ with hN
  have hN0 : 0 < N := inv_pos.mpr hpos
  set s := descendantsAtDepth Q k
  have hu : ∀ R, 0 ≤ N * vecNormSq (A R) := fun R => mul_nonneg hN0.le (vecNormSq_nonneg _)
  have hv : ∀ R, 0 ≤ N * vecNormSq (B R) := fun R => mul_nonneg hN0.le (vecNormSq_nonneg _)
  have hcs := sum_sqrt_add_sq_le s hu hv
  have hlhs : descendantsAverage Q k (fun R => vecNormSq (A R + B R)) ≤
      ∑ R ∈ s, (Real.sqrt (N * vecNormSq (A R)) + Real.sqrt (N * vecNormSq (B R))) ^ 2 := by
    rw [descendantsAverage_eq, ← hN, Finset.mul_sum]
    refine Finset.sum_le_sum fun R _ => ?_
    have h := vecNormSq_add_le (A R) (B R)
    have e : (Real.sqrt (N * vecNormSq (A R)) + Real.sqrt (N * vecNormSq (B R))) ^ 2 =
        N * (Real.sqrt (vecNormSq (A R)) + Real.sqrt (vecNormSq (B R))) ^ 2 := by
      rw [Real.sqrt_mul hN0.le, Real.sqrt_mul hN0.le]
      have := Real.sq_sqrt hN0.le
      calc _ = (Real.sqrt N) ^ 2 * (Real.sqrt (vecNormSq (A R)) + Real.sqrt (vecNormSq (B R))) ^ 2 := by
            ring
        _ = _ := by rw [this]
    rw [e]
    exact mul_le_mul_of_nonneg_left h hN0.le
  have hnn : 0 ≤ descendantsAverage Q k (fun R => vecNormSq (A R + B R)) :=
    descendantsAverage_nonneg Q k _ fun R _ => vecNormSq_nonneg _
  have hrhs : (Real.sqrt (∑ R ∈ s, N * vecNormSq (A R)) + Real.sqrt (∑ R ∈ s, N * vecNormSq (B R))) =
      Real.sqrt (descendantsAverage Q k (fun R => vecNormSq (A R))) +
        Real.sqrt (descendantsAverage Q k (fun R => vecNormSq (B R))) := by
    simp only [descendantsAverage_eq, Finset.mul_sum]; rfl
  rw [hrhs] at hcs
  exact Real.sqrt_le_iff.mpr ⟨add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _),
    hlhs.trans hcs⟩

/-- **H1(e) with a step field and Minkowski over the cells.** -/
theorem incNorm_le_drop (Q : Homogenization.TriadicCube d) {k : ℕ} (hk : 1 ≤ k)
    {G : Homogenization.Vec d → Homogenization.Vec d}
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q))
    (S : Homogenization.TriadicCube d → Homogenization.Vec d) (c : Homogenization.Vec d) :
    incNorm Q k G ≤
      Real.sqrt (descendantsAverage Q k (fun R => vecNormSq (cubeAverageVec R G - S R))) +
        Real.sqrt (descendantsAverage Q k (fun R => vecNormSq (S R - c))) := by
  have h1 := incNorm_sq_le_const Q hk hG c
  have h2 : descendantsAverage Q k (fun R => vecNormSq (cubeAverageVec R G - c)) =
      descendantsAverage Q k (fun R => vecNormSq ((cubeAverageVec R G - S R) + (S R - c))) :=
    descendantsAverage_congr' Q k fun R _ => by rw [sub_add_sub_cancel]
  rw [h2] at h1
  refine le_trans ?_ (sqrt_avg_add_le Q k _ _)
  calc incNorm Q k G = Real.sqrt (incNorm Q k G ^ 2) := (Real.sqrt_sq (incNorm_nonneg' Q k G)).symm
    _ ≤ _ := Real.sqrt_le_sqrt h1

end GMCExplicitDelta.Localization.GradPieces
