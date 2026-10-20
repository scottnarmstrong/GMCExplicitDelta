module

public import GMCExplicitDelta.Localization.HaarDefs
public import GMCExplicitDelta.Haar.LocalizationWeight
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Coordinates for the depth-k partition of an origin cube. -/
@[expose] public section

open Homogenization Homogenization.Book

namespace GMCExplicitDelta.Localization.LocWeights

variable {d : ℕ}

theorem cube_eq_of_fields (P Q : TriadicCube d) (hs : P.scale = Q.scale)
    (hi : P.index = Q.index) : P = Q := by
  cases P
  cases Q
  congr

def gridRadius : ℕ → ℕ
  | 0 => 0
  | k + 1 => 3 * gridRadius k + 1

theorem gridRadius_spec (k : ℕ) : 3 ^ k = 2 * gridRadius k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ, ih, gridRadius]; ring

def gridCube (n k : ℕ) (a : Fin d → Fin (3 ^ k)) : TriadicCube d :=
  ⟨(n : ℤ) - k, fun i => (a i : ℤ) - (gridRadius k : ℤ)⟩

theorem gridCube_injective (n k : ℕ) : Function.Injective (gridCube (d := d) n k) := by
  intro a b hab
  funext i
  apply Fin.ext
  have h := congrArg (fun R : TriadicCube d => R.index i) hab
  dsimp only [gridCube] at h
  omega

theorem descendant_index_bounds (n k : ℕ) {R : TriadicCube d}
    (hR : R ∈ descendantsAtDepth (originCube d (n : ℤ)) k) (i : Fin d) :
    -(gridRadius k : ℤ) ≤ R.index i ∧ R.index i ≤ (gridRadius k : ℤ) := by
  induction k generalizing R with
  | zero =>
    have heq : R = originCube d (n : ℤ) := by simpa only [descendantsAtDepth_zero, Finset.mem_singleton] using hR
    subst R
    simp only [originCube, Pi.zero_apply, gridRadius, Nat.cast_zero, neg_zero, le_refl, and_self]
  | succ k ih =>
    obtain ⟨S, hS, hRS⟩ := mem_descendantsAtDepth_succ_iff.mp hR
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hRS
    have hb := ih hS
    have ha : (a i : ℕ) < 3 := (a i).isLt
    simp only [gridRadius, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    omega

theorem descendants_eq_grid (n k : ℕ) :
    descendantsAtDepth (originCube d (n : ℤ)) k = Finset.univ.image (gridCube (d := d) n k) := by
  classical
  have hsub : descendantsAtDepth (originCube d (n : ℤ)) k ⊆ Finset.univ.image (gridCube (d := d) n k) := by
    intro R hR
    have hrad := gridRadius_spec k
    let a : Fin d → Fin (3 ^ k) := fun i =>
      ⟨(R.index i + (gridRadius k : ℤ)).toNat, by
        have hb := descendant_index_bounds n k hR i
        omega⟩
    have hindex : (gridCube n k a).index = R.index := by
      funext i
      have hb := descendant_index_bounds n k hR i
      dsimp only [gridCube, a]
      omega
    have hscale : (gridCube n k a).scale = R.scale := by
      symm
      exact scale_eq_sub_of_mem_descendantsAtDepth hR
    apply Finset.mem_image.mpr
    refine ⟨a, Finset.mem_univ _, ?_⟩
    exact cube_eq_of_fields _ _ hscale hindex
  apply Finset.eq_of_subset_of_card_le hsub
  rw [Finset.card_image_of_injective _ (gridCube_injective n k), Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, descendantsAtDepth_card]
  rw [← pow_mul, ← pow_mul, Nat.mul_comm k d]

end GMCExplicitDelta.Localization.LocWeights
