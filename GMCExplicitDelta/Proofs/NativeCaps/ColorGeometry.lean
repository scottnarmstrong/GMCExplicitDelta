module

public import Homogenization.Geometry.TriadicPartition
public import Homogenization.Book.Ch02.Theorems.MatrixOperatorNorm

/-! # The sharp ternary coloring of the last generation of cells -/

@[expose] public section

open Homogenization Homogenization.Book MeasureTheory
open scoped BigOperators

namespace GMCExplicitDelta.Assembly

/-- Last-digit parametrization of a child. Its color is its index plus one modulo 3. -/
def nativeChild {d : ℕ} (R : TriadicCube d) (c : Fin d → Fin 3) : TriadicCube d :=
  ⟨R.scale - 1, fun i => 3 * R.index i + (c i : ℤ) - 1⟩

@[simp]
theorem nativeChild_scale {d : ℕ} (R : TriadicCube d) (c : Fin d → Fin 3) :
    (nativeChild R c).scale = R.scale - 1 := rfl

@[simp]
theorem parent_nativeChild {d : ℕ} (R : TriadicCube d) (c : Fin d → Fin 3) :
    parentCube (nativeChild R c) = R := childCube_parent R c

theorem nativeChild_mem {d : ℕ} (R : TriadicCube d) (c : Fin d → Fin 3) :
    nativeChild R c ∈ childCubes R := mem_childCubes_iff.mpr ⟨c, rfl⟩

theorem nativeChild_injective {d : ℕ} :
    Function.Injective (fun p : (TriadicCube d × (Fin d → Fin 3)) => nativeChild p.1 p.2) := by
  rintro ⟨R, c⟩ ⟨S, b⟩ he
  have hp := congrArg parentCube he
  simp only [parent_nativeChild] at hp
  subst S
  have hc : c = b := by
    funext i
    apply Fin.ext
    have h := congrArg (fun Q : TriadicCube d => Q.index i) he
    change 3 * R.index i + (c i : ℤ) - 1 = 3 * R.index i + (b i : ℤ) - 1 at h
    omega
  subst b
  rfl

theorem nativeChild_color {d : ℕ} (R : TriadicCube d) (c : Fin d → Fin 3) (i : Fin d) :
    ((nativeChild R c).index i + 1) % 3 = (c i : ℤ) := by
  change (3 * R.index i + (c i : ℤ) - 1 + 1) % 3 = (c i : ℤ)
  have hc := (c i).isLt
  omega

/-- A fixed color contains exactly one child per parent. -/
theorem nativeColor_card {d : ℕ} (Q : TriadicCube d) (j : ℕ) (c : Fin d → Fin 3) :
    ((descendantsAtDepth Q j).image (fun R => nativeChild R c)).card = 3 ^ (d * j) := by
  rw [Finset.card_image_of_injective]
  · rw [descendantsAtDepth_card, ← pow_mul]
  · intro R S h
    exact congrArg Prod.fst (nativeChild_injective (a₁ := (R, c)) (a₂ := (S, c)) h)

/-- The last-digit parametrization is exactly the index-plus-one residue class modulo three. -/
theorem nativeColor_eq_filter {d : ℕ} (Q : TriadicCube d) (j : ℕ) (c : Fin d → Fin 3) :
    (descendantsAtDepth Q (j + 1)).filter
        (fun R => ∀ i, (R.index i + 1) % 3 = (c i : ℤ)) =
      (descendantsAtDepth Q j).image (fun R => nativeChild R c) := by
  classical
  ext R
  constructor
  · intro h
    obtain ⟨P, hP, hR⟩ := mem_descendantsAtDepth_succ_iff.mp (Finset.mem_filter.mp h).1
    obtain ⟨b, rfl⟩ := mem_childCubes_iff.mp hR
    have hb : b = c := by
      funext i
      apply Fin.ext
      have hh := (Finset.mem_filter.mp h).2 i
      change ((nativeChild P b).index i + 1) % 3 = (c i : ℤ) at hh
      rw [nativeChild_color] at hh
      exact_mod_cast hh
    subst b
    exact Finset.mem_image.mpr ⟨P, hP, rfl⟩
  · rintro h
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_filter.mpr ⟨mem_descendantsAtDepth_succ_iff.mpr
      ⟨P, hP, nativeChild_mem P c⟩, nativeChild_color P c⟩

/-- Every modulo-three class in a depth-(j+1) partition has precisely 3^(d*j) cells. -/
theorem native_modThree_class_card {d : ℕ} (Q : TriadicCube d) (j : ℕ) (c : Fin d → Fin 3) :
    ((descendantsAtDepth Q (j + 1)).filter
      (fun R => ∀ i, (R.index i + 1) % 3 = (c i : ℤ))).card = 3 ^ (d * j) := by
  rw [nativeColor_eq_filter, nativeColor_card]

theorem native_palette_card (d : ℕ) : Fintype.card (Fin d → Fin 3) = 3 ^ d := by
  simp only [Fintype.card_fun, Fintype.card_fin]

/-- Summation on the next generation is summation over parents and colors. -/
theorem sum_nativeChild {d : ℕ} {E : Type*} [AddCommMonoid E]
    (Q : TriadicCube d) (j : ℕ) (f : TriadicCube d → E) :
    ∑ R ∈ descendantsAtDepth Q (j + 1), f R =
      ∑ c : Fin d → Fin 3, ∑ R ∈ descendantsAtDepth Q j, f (nativeChild R c) := by
  classical
  rw [descendantsAtDepth_succ, Finset.sum_biUnion]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro R _
    change ∑ S ∈ Finset.univ.image (nativeChild R), f S = _
    rw [Finset.sum_image]
    intro a _ b _ h
    exact congrArg Prod.snd (nativeChild_injective (a₁ := (R, a)) (a₂ := (R, b)) h)
  · intro R _ S _ hRS
    exact disjoint_childCubes_of_ne hRS

/-- Different children with the same last digit are separated by two cell widths. -/
theorem nativeChild_separation {d L : ℕ} {R S : TriadicCube d}
    (hR : R.scale = (L : ℤ) + 1) (hS : S.scale = (L : ℤ) + 1) (hne : R ≠ S)
    (c : Fin d → Fin 3) {x y : Homogenization.Vec d}
    (hx : x ∈ openCubeSet (nativeChild R c)) (hy : y ∈ openCubeSet (nativeChild S c)) :
    2 * (3 : ℝ) ^ L ≤ Ch02.vecNorm (x - y) := by
  have hidx : R.index ≠ S.index := by
    intro h
    apply hne
    exact congrArg₂ TriadicCube.mk (hR.trans hS.symm) h
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hidx
  have hr : cubeScaleFactor (nativeChild R c) = (3 : ℝ) ^ L := by
    simp only [cubeScaleFactor, nativeChild_scale, hR, add_sub_cancel_right, zpow_natCast]
  have hs : cubeScaleFactor (nativeChild S c) = (3 : ℝ) ^ L := by
    simp only [cubeScaleFactor, nativeChild_scale, hS, add_sub_cancel_right, zpow_natCast]
  have hxi := hx i
  have hyi := hy i
  rw [hr] at hxi
  rw [hs] at hyi
  change (((3 * R.index i + (c i : ℤ) - 1 : ℤ) : ℝ) - 1 / 2) * 3 ^ L < x i ∧
    x i < (((3 * R.index i + (c i : ℤ) - 1 : ℤ) : ℝ) + 1 / 2) * 3 ^ L at hxi
  change (((3 * S.index i + (c i : ℤ) - 1 : ℤ) : ℝ) - 1 / 2) * 3 ^ L < y i ∧
    y i < (((3 * S.index i + (c i : ℤ) - 1 : ℤ) : ℝ) + 1 / 2) * 3 ^ L at hyi
  push_cast at hxi hyi
  have hcoord : 2 * (3 : ℝ) ^ L ≤ |x i - y i| := by
    rcases lt_or_gt_of_ne hi with hlt | hlt
    · have hz : (R.index i : ℝ) + 1 ≤ (S.index i : ℝ) := by exact_mod_cast (show R.index i + 1 ≤ S.index i by omega)
      have hp := mul_le_mul_of_nonneg_right hz (show 0 ≤ (3 : ℝ) ^ L by positivity)
      have ha := neg_le_abs (x i - y i)
      nlinarith only [hp, hxi.2, hyi.1, ha]
    · have hz : (S.index i : ℝ) + 1 ≤ (R.index i : ℝ) := by exact_mod_cast (show S.index i + 1 ≤ R.index i by omega)
      have hp := mul_le_mul_of_nonneg_right hz (show 0 ≤ (3 : ℝ) ^ L by positivity)
      have ha := le_abs_self (x i - y i)
      nlinarith only [hp, hxi.1, hyi.2, ha]
  apply hcoord.trans
  simpa only [Ch02.vecNorm, PiLp.toLp_apply, Pi.sub_apply, Real.norm_eq_abs] using
    (PiLp.norm_apply_le (WithLp.toLp 2 (x - y)) i)

/-- Dimensions at most four fit exactly within the two-width separation. -/
theorem nativeChild_rangeSeparation {d L : ℕ} (hd : d ≤ 4) {R S : TriadicCube d}
    (hR : R.scale = (L : ℤ) + 1) (hS : S.scale = (L : ℤ) + 1) (hne : R ≠ S)
    (c : Fin d → Fin 3) {x y : Homogenization.Vec d}
    (hx : x ∈ openCubeSet (nativeChild R c)) (hy : y ∈ openCubeSet (nativeChild S c)) :
    Real.sqrt (d : ℝ) * (3 : ℝ) ^ L ≤ Ch02.vecNorm (x - y) := by
  have hs : Real.sqrt (d : ℝ) ≤ 2 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by exact_mod_cast hd⟩
  exact (mul_le_mul_of_nonneg_right hs (by positivity)).trans
    (nativeChild_separation hR hS hne c hx hy)

end GMCExplicitDelta.Assembly
