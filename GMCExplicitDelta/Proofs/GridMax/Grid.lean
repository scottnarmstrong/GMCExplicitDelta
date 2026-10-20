module

public import GMCExplicitDelta.Proofs.GridMax.Spatial
public import Mathlib.Algebra.Order.Floor.Ring

/-! # The finite grid covering of an open unit cube -/

@[expose] public section

open Homogenization MeasureTheory SubdiffusiveProcess.Model

namespace GMCExplicitDelta.Assembly.GridMax

variable {d : ℕ}

/-- Centers of the equal grid cells in the centered unit cube. -/
noncomputable def gridPoint (N : ℕ) (j : Fin d → Fin N) : Homogenization.Vec d :=
  fun k => -(1 / 2 : ℝ) + ((j k : ℝ) + 1 / 2) / N

/-- Every grid center lies strictly inside the unit cube. -/
theorem gridPoint_mem {N : ℕ} (hN : 0 < N) (j : Fin d → Fin N) :
    gridPoint N j ∈ openCubeSet (originCube d 0) := by
  rw [mem_openCubeSet_originCube_iff]
  intro k
  have hn : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hj0 : (0 : ℝ) ≤ (j k : ℕ) := Nat.cast_nonneg _
  have hj1 : ((j k : ℕ) : ℝ) + 1 ≤ N := by
    have h : (((j k : ℕ) + 1 : ℕ) : ℝ) ≤ N := Nat.cast_le.2 (Nat.succ_le_of_lt (j k).isLt)
    simpa only [Nat.cast_add, Nat.cast_one] using h
  norm_num only [zpow_zero, mul_one, gridPoint]
  constructor
  · have : 0 < ((j k : ℝ) + 1 / 2) / N := div_pos (by linarith) hn
    linarith
  · have : ((j k : ℝ) + 1 / 2) / N < 1 := (div_lt_one hn).2 (by linarith)
    linarith

/-- The grid has covering radius 1/(2N) in the ambient supremum norm. -/
theorem grid_cover {N : ℕ} (hN : 0 < N) {x : Homogenization.Vec d}
    (hx : x ∈ openCubeSet (originCube d 0)) :
    ∃ j : Fin d → Fin N, ‖x - gridPoint N j‖ ≤ 1 / (2 * (N : ℝ)) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hx' := mem_openCubeSet_originCube_iff.1 hx
  have ht0 (k : Fin d) : 0 ≤ (N : ℝ) * (x k + 1 / 2) := by
    have hk := hx' k
    norm_num only [zpow_zero, mul_one] at hk
    exact mul_nonneg hn.le (by linarith)
  have ht1 (k : Fin d) : (N : ℝ) * (x k + 1 / 2) < N := by
    have hk := hx' k
    norm_num only [zpow_zero, mul_one] at hk
    nlinarith
  let j : Fin d → Fin N := fun k => ⟨⌊(N : ℝ) * (x k + 1 / 2)⌋₊,
    (Nat.floor_lt (ht0 k)).2 (ht1 k)⟩
  refine ⟨j, (pi_norm_le_iff_of_nonneg (by positivity)).2 fun k => ?_⟩
  have hlo := Nat.floor_le (ht0 k)
  have hhi := Nat.lt_floor_add_one ((N : ℝ) * (x k + 1 / 2))
  have heq : (x k - gridPoint N j k) * N =
      (N : ℝ) * (x k + 1 / 2) - ((j k : ℝ) + 1 / 2) := by
    unfold gridPoint
    field_simp
    ring
  change |x k - gridPoint N j k| ≤ 1 / (2 * (N : ℝ))
  apply abs_le.2
  constructor
  · rw [← neg_div, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * N)]
    change (N : ℝ) * (x k + 1 / 2) < (j k : ℝ) + 1 at hhi
    nlinarith
  · rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * N)]
    change (j k : ℝ) ≤ (N : ℝ) * (x k + 1 / 2) at hlo
    nlinarith

/-- The whole layerPrefix of layers at a point. -/
noncomputable def layerPrefix (L : ℕ) (ω : PotentialSample d) (x : Homogenization.Vec d) : ℝ :=
  ∑ i ∈ Finset.range (L + 1), ω i x

/-- The random spatial remainder for a unit cube centered at `z`. -/
noncomputable def remainder (N L : ℕ) (z : Homogenization.Vec d) (ω : PotentialSample d) : ℝ :=
  ∑ i ∈ Finset.range (L + 1), (1 / (2 * (N : ℝ)) * ((3 : ℝ) ^ i)⁻¹) * W i z ω

/-- S1(c) and the finite covering control every layerPrefix value by a grid value plus the remainder. -/
theorem prefix_grid_bound {N : ℕ} (hN : 0 < N) (L : ℕ) (z : Homogenization.Vec d)
    (ω : PotentialSample d) {x : Homogenization.Vec d}
    (hx : x ∈ openCubeSet (originCube d 0)) :
    ∃ j : Fin d → Fin N, |layerPrefix L ω (x + z)| ≤
      |layerPrefix L ω (gridPoint N j + z)| + remainder N L z ω := by
  obtain ⟨j, hj⟩ := grid_cover hN hx
  refine ⟨j, ?_⟩
  have hi (i : ℕ) : |ω i (x + z) - ω i (gridPoint N j + z)| ≤
      (1 / (2 * (N : ℝ)) * ((3 : ℝ) ^ i)⁻¹) * W i z ω := by
    exact (layer_increment_le i z ω hx (gridPoint_mem hN j)).trans
      ((mul_le_mul_of_nonneg_left hj (mul_nonneg (by positivity) (W_nonneg _ _ _))).trans_eq (by ring))
  have hsum : |∑ i ∈ Finset.range (L + 1), (ω i (x + z) - ω i (gridPoint N j + z))| ≤
      ∑ i ∈ Finset.range (L + 1),
        (1 / (2 * (N : ℝ)) * ((3 : ℝ) ^ i)⁻¹) * W i z ω :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hi i)
  rw [Finset.sum_sub_distrib] at hsum
  change |layerPrefix L ω (x + z) - layerPrefix L ω (gridPoint N j + z)| ≤ remainder N L z ω at hsum
  calc
    _ = |layerPrefix L ω (gridPoint N j + z) +
        (layerPrefix L ω (x + z) - layerPrefix L ω (gridPoint N j + z))| := by congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add le_rfl hsum)

end GMCExplicitDelta.Assembly.GridMax
