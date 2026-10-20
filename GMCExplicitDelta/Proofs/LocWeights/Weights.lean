module

public import GMCExplicitDelta.Proofs.LocWeights.Grid
public import Mathlib.Analysis.Convex.Jensen

/-! The endpoint-minimum weights on the actual triadic partition (H13). -/
@[expose] public section

open Homogenization Homogenization.Book
open scoped BigOperators

namespace GMCExplicitDelta.Localization.LocWeights

open Assembly Contract Haar
variable {d : ℕ}

theorem omega_bounds (row : Row d) (hO : row.Obligations) :
    0 < row.omegaEff ∧ row.omegaEff ≤ 1 / 2 := by
  unfold Row.omegaEff
  split_ifs with hd
  · norm_num
  · have h := (hO.par2.2.2.2.2.2 hd).2
    constructor
    · exact_mod_cast h.1
    · have h' : (row.width : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr h.2
      simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h'

theorem gridCube_scale (n k : ℕ) (a : Fin d → Fin (3 ^ k)) :
    cubeScaleFactor (gridCube n k a) = (3 : ℝ) ^ n / (3 : ℝ) ^ k := by
  unfold cubeScaleFactor gridCube
  rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
  simp only [zpow_natCast]

theorem gridCube_endpoint (n k : ℕ) (a : Fin d → Fin (3 ^ k)) (i : Fin d) (e : ℕ) :
    (((gridCube n k a).index i : ℝ) - 1 / 2 + (e : ℝ)) *
        cubeScaleFactor (gridCube n k a) / (3 : ℝ) ^ n =
      gridPoint (3 ^ k) ((a i : ℕ) + e) := by
  have h3n : (3 : ℝ) ^ n ≠ 0 := by positivity
  have h3k : (3 : ℝ) ^ k ≠ 0 := by positivity
  have hrad : (3 : ℝ) ^ k = 2 * (gridRadius k : ℝ) + 1 := by exact_mod_cast gridRadius_spec k
  rw [gridCube_scale]
  unfold gridCube gridPoint
  push_cast
  field_simp
  nlinarith only [hrad]

noncomputable def endpointWeight (row : Row d) (n k : ℕ) (R : TriadicCube d) : ℝ :=
  if R ∈ descendantsAtDepth (originCube d (n : ℤ)) k then
    ∏ i, min
      (cutoffProfile row.omegaEff ((((R.index i : ℝ) - 1 / 2) * cubeScaleFactor R) / (3 : ℝ) ^ n))
      (cutoffProfile row.omegaEff ((((R.index i : ℝ) + 1 / 2) * cubeScaleFactor R) / (3 : ℝ) ^ n))
  else 0

noncomputable def gridFactor (row : Row d) (k j : ℕ) : ℝ :=
  min (cutoffProfile row.omegaEff (gridPoint (3 ^ k) j))
    (cutoffProfile row.omegaEff (gridPoint (3 ^ k) (j + 1)))

theorem endpointWeight_grid (row : Row d) (n k : ℕ) (a : Fin d → Fin (3 ^ k)) :
    endpointWeight row n k (gridCube n k a) = ∏ i, gridFactor row k (a i) := by
  classical
  have hmem : gridCube n k a ∈ descendantsAtDepth (originCube d (n : ℤ)) k := by
    rw [descendants_eq_grid]
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  rw [endpointWeight, ite_eq_left hmem]
  apply Finset.prod_congr rfl
  intro i _
  unfold gridFactor
  have he0 := gridCube_endpoint n k a i 0
  have he1 := gridCube_endpoint n k a i 1
  simp only [Nat.cast_zero, Nat.cast_one, add_zero] at he0 he1
  rw [show ((gridCube n k a).index i : ℝ) + 1 / 2 =
      ((gridCube n k a).index i : ℝ) - 1 / 2 + 1 by ring, he0, he1]

theorem gridFactor_bounds (row : Row d) (hO : row.Obligations) {k j : ℕ} (hj : j < 3 ^ k) :
    0 ≤ gridFactor row k j ∧ gridFactor row k j ≤ 1 := by
  obtain ⟨hω0, hω1⟩ := omega_bounds row hO
  have hN : 0 < (3 : ℕ) ^ k := by positivity
  have h0 := cutoffProfile_bounds hω0 hω1 (abs_le.mpr (gridPoint_mem hN (Nat.le_of_lt hj)))
  have h1 := cutoffProfile_bounds hω0 hω1 (abs_le.mpr (gridPoint_mem hN (Nat.succ_le_of_lt hj)))
  exact ⟨le_min h0.1 h1.1, (min_le_left _ _).trans h0.2⟩

theorem endpointWeight_bounds (row : Row d) (hO : row.Obligations) (n k : ℕ) (R : TriadicCube d) :
    0 ≤ endpointWeight row n k R ∧ endpointWeight row n k R ≤ 1 := by
  classical
  by_cases hR : R ∈ descendantsAtDepth (originCube d (n : ℤ)) k
  · rw [descendants_eq_grid] at hR
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hR
    rw [endpointWeight_grid]
    exact ⟨Finset.prod_nonneg (fun i _ => (gridFactor_bounds row hO (a i).isLt).1),
      Finset.prod_le_one₀ (fun i _ => (gridFactor_bounds row hO (a i).isLt).1)
        (fun i _ => (gridFactor_bounds row hO (a i).isLt).2)⟩
  · rw [endpointWeight, ite_eq_right hR]
    exact ⟨le_rfl, zero_le_one⟩

theorem endpointWeight_le_cutoff (row : Row d) (hO : row.Obligations) (n k : ℕ)
    {R : TriadicCube d} (hR : R ∈ descendantsAtDepth (originCube d (n : ℤ)) k)
    {x : Homogenization.Vec d} (hx : x ∈ cubeSet R) :
    endpointWeight row n k R ≤ cubeCutoff row n x := by
  classical
  rw [descendants_eq_grid] at hR
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hR
  rw [endpointWeight_grid]
  unfold cubeCutoff cutoffProduct
  apply Finset.prod_le_prod₀ (fun i _ => (gridFactor_bounds row hO (a i).isLt).1)
  intro i _
  obtain ⟨hω0, hω1⟩ := omega_bounds row hO
  have hN : 0 < (3 : ℕ) ^ k := by positivity
  apply (cutoffProfile_concaveOn hω0 hω1).min_le_of_mem_Icc
    (gridPoint_mem hN (a i).isLt.le) (gridPoint_mem hN (Nat.succ_le_of_lt (a i).isLt))
  have h3n : 0 ≤ (3 : ℝ) ^ n := by positivity
  have hl := div_le_div_of_nonneg_right (hx i).1 h3n
  have hu := div_le_div_of_nonneg_right (hx i).2.le h3n
  have he0 := gridCube_endpoint n k a i 0
  have he1 := gridCube_endpoint n k a i 1
  simp only [Nat.cast_zero, add_zero] at he0
  have he1' : (((gridCube n k a).index i : ℝ) + 1 / 2) *
      cubeScaleFactor (gridCube n k a) / (3 : ℝ) ^ n = gridPoint (3 ^ k) ((a i : ℕ) + 1) := by
    rw [show ((gridCube n k a).index i : ℝ) + 1 / 2 =
      ((gridCube n k a).index i : ℝ) - 1 / 2 + (1 : ℝ) by ring]
    simpa only [Nat.cast_one] using he1
  rw [he0] at hl
  rw [he1'] at hu
  exact ⟨hl, hu⟩

theorem endpointWeight_average (row : Row d) (n k : ℕ) :
    descendantsAverage (originCube d (n : ℤ)) k (endpointWeight row n k) =
      gridMin (3 ^ k) (cutoffProfile row.omegaEff) ^ d := by
  classical
  change ((descendantsAtDepth (originCube d (n : ℤ)) k).card : ℝ)⁻¹ *
    (∑ R ∈ descendantsAtDepth (originCube d (n : ℤ)) k, endpointWeight row n k R) = _
  rw [descendants_eq_grid, Finset.sum_image (gridCube_injective n k).injOn]
  simp_rw [endpointWeight_grid]
  rw [← Fintype.prod_sum (fun (_ : Fin d) (j : Fin (3 ^ k)) => gridFactor row k j)]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [Finset.card_image_of_injective _ (gridCube_injective n k)]
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  rw [Fin.sum_univ_eq_sum_range (fun j => gridFactor row k j)]
  unfold gridMin gridFactor
  push_cast
  rw [mul_pow, inv_pow]

end GMCExplicitDelta.Localization.LocWeights

namespace GMCExplicitDelta.Localization

open Assembly Contract
variable {d : ℕ}

theorem loc_weights_proof (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (n : ℕ) :
    ∃ w : Homogenization.TriadicCube d → ℝ, (∀ R, 0 ≤ w R ∧ w R ≤ 1) ∧
      row.cNu ≤ descendantsAverage (originCube d (n : ℤ)) row.nu w ∧
      ∀ R ∈ descendantsAtDepth (originCube d (n : ℤ)) row.nu, ∀ x ∈ cubeSet R,
        w R ≤ cubeCutoff row n x := by
  have _hd := hd
  obtain ⟨hω0, hω1⟩ := LocWeights.omega_bounds row hO
  refine ⟨LocWeights.endpointWeight row n row.nu, LocWeights.endpointWeight_bounds row hO n row.nu, ?_, ?_⟩
  · rw [LocWeights.endpointWeight_average]
    exact Haar.cNu_le_exactLocalizationWeight row hω0 hω1 hO.geo1.1
  · intro R hR x hx
    exact LocWeights.endpointWeight_le_cutoff row hO n row.nu hR hx

end GMCExplicitDelta.Localization
