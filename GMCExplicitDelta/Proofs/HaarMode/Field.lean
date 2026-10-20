module

public import GMCExplicitDelta.Proofs.HaarMode.Atoms
public import GMCExplicitDelta.Proofs.HaarMode.Products
public import Homogenization.Sobolev.H1.OriginCubeBridge

/-! # H¹ witnesses for the scaled cutoff gradient -/

@[expose] public section

open MeasureTheory Homogenization Set Filter
open scoped ENNReal

namespace GMCExplicitDelta.Localization

variable {d : ℕ}

/-- Factor type in one component of the cutoff gradient. -/
def haarMode_gtype (i k : Fin d) : Fin 3 := if k = i then 1 else 0

/-- Factor type after differentiating that component in coordinate `j`. -/
def haarMode_htype (i j k : Fin d) : Fin 3 :=
  if k = j then if j = i then 2 else 1 else haarMode_gtype i k

/-- Product representation of the cutoff gradient. -/
noncomputable def haarMode_rawG (ω : ℝ) (x : Homogenization.Vec d) (i : Fin d) : ℝ :=
  ∏ k, haarMode_atom ω (haarMode_gtype i k) (x k)

/-- Product representation of the cutoff's weak Hessian. -/
noncomputable def haarMode_rawH (ω : ℝ) (x : Homogenization.Vec d) (i j : Fin d) : ℝ :=
  ∏ k, haarMode_atom ω (haarMode_htype i j k) (x k)

/-- The product representation is the original cutoff gradient. -/
theorem haarMode_rawG_eq (ω : ℝ) (x : Homogenization.Vec d) (i : Fin d) :
    haarMode_rawG ω x i = Haar.cutoffGradient ω x i := by
  classical
  unfold haarMode_rawG Haar.cutoffGradient
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [haarMode_gtype, ite_true]
  apply congrArg₂ (· * ·)
  · norm_num [haarMode_atom]
  apply Finset.prod_congr rfl
  intro k hk
  simp only [ite_eq_right (Finset.ne_of_mem_erase hk)]
  norm_num [haarMode_atom]

/-- A Hessian component is a single differentiated factor times the remaining factors. -/
theorem haarMode_rawH_eq (ω : ℝ) (x : Homogenization.Vec d) (i j : Fin d) :
    haarMode_rawH ω x i j = haarMode_atom ω (if j = i then 2 else 1) (x j) *
      ∏ k ∈ Finset.univ.erase j, haarMode_atom ω (haarMode_gtype i k) (x k) := by
  classical
  unfold haarMode_rawH
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
  simp only [haarMode_htype, ite_true]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [ite_eq_right (Finset.ne_of_mem_erase hk)]

/-- The normalized coordinate is H¹ with its constant scaled gradient. -/
theorem haarMode_scaled_coordinate (n : ℕ) (i : Fin d) :
    ∃ u : H1Function (openCubeSet (originCube d (n : ℤ))),
      u.toFun = (fun x => x i / (3 : ℝ) ^ n) ∧
      u.grad = (fun _ => ((3 : ℝ) ^ n)⁻¹ • basisVec i) := by
  refine ⟨((3 : ℝ) ^ n)⁻¹ • H1Function.coordOnOpenCubeSetOriginCube (n := (n : ℤ)) i, ?_, ?_⟩
  · funext x
    simp only [H1Function.smul_toFun, H1Function.coordOnOpenCubeSetOriginCube, div_eq_mul_inv]
    ring
  · rfl

/-- Each scalar factor in a cutoff-gradient component has the expected coordinate weak derivative. -/
theorem haarMode_factor_h1 {ω : ℝ} (hω : ω ≤ 1 / 2) (n : ℕ) (i k : Fin d) :
    ∃ v : H1Function (openCubeSet (originCube d (n : ℤ))),
      v.toFun = (fun x => haarMode_atom ω (haarMode_gtype i k) (x k / (3 : ℝ) ^ n)) ∧
      ∀ᵐ x ∂volume.restrict (openCubeSet (originCube d (n : ℤ))),
        v.grad x = fun j => ((3 : ℝ) ^ n)⁻¹ *
          haarMode_atom ω (if k = i then 2 else 1) (x k / (3 : ℝ) ^ n) * basisVec k j := by
  classical
  obtain ⟨u, huf, hug⟩ := haarMode_scaled_coordinate n k
  have hU := isOpenBoundedConvexDomain_openCubeSet (originCube d (n : ℤ))
  by_cases hki : k = i
  · obtain ⟨v, hvf, hvg⟩ := haarMode_h1_slope hU u hω
    refine ⟨v, ?_, ?_⟩
    · rw [hvf, huf]
      simp only [haarMode_gtype, ite_eq_left hki]
      norm_num [haarMode_atom]
    · filter_upwards [hvg] with x hx
      rw [hx, hug]
      funext j
      simp only [huf, ite_eq_left hki, Pi.smul_apply, smul_eq_mul]
      norm_num [haarMode_atom]
      unfold haarMode_curvature
      split_ifs <;> ring
  · obtain ⟨v, hvf, hvg⟩ := haarMode_h1_profile hU u hω
    refine ⟨v, ?_, ?_⟩
    · rw [hvf, huf]
      simp only [haarMode_gtype, ite_eq_right hki]
      norm_num [haarMode_atom]
    · exact Filter.Eventually.of_forall fun x => by
        rw [hvg, hug]
        funext j
        simp only [huf, ite_eq_right hki, Pi.smul_apply, smul_eq_mul]
        norm_num [haarMode_atom, basisVec_apply]
        split_ifs <;> ring

/-- A component of the scaled cutoff gradient is H¹, with its weak Hessian. -/
theorem haarMode_rawG_h1 {ω : ℝ} (hω : ω ≤ 1 / 2) (n : ℕ) (i : Fin d) :
    ∃ v : H1Function (openCubeSet (originCube d (n : ℤ))),
      v.toFun = (fun x => haarMode_rawG ω (fun k => x k / (3 : ℝ) ^ n) i) ∧
      ∀ᵐ x ∂volume.restrict (openCubeSet (originCube d (n : ℤ))),
        v.grad x = fun j => ((3 : ℝ) ^ n)⁻¹ *
          haarMode_rawH ω (fun k => x k / (3 : ℝ) ^ n) i j := by
  classical
  choose u huf hug using fun k => haarMode_factor_h1 hω n i k
  let C := max 1 (max |Real.pi / (2 * ω)| ((Real.pi / (2 * ω)) ^ 2))
  have hb (k : Fin d) : ∀ᵐ x ∂volume.restrict (openCubeSet (originCube d (n : ℤ))),
      |u k x| ≤ C := Filter.Eventually.of_forall fun x => by
    rw [huf]
    exact haarMode_atom_abs_le _ _ _
  obtain ⟨v, hvf, hvg, _⟩ := haarMode_h1_finset_prod
    (isOpenBoundedConvexDomain_openCubeSet (originCube d (n : ℤ)))
    Finset.univ u (le_max_left 1 _) (fun k _ => hb k)
  refine ⟨v, ?_, ?_⟩
  · rw [hvf]
    funext x
    exact Finset.prod_congr rfl fun k _ => congrFun (huf k) x
  · filter_upwards [ae_all_iff.2 hug] with x hx
    rw [hvg]
    funext j
    simp only [hx, huf, basisVec_apply]
    rw [Finset.sum_eq_single j]
    · rw [ite_eq_left rfl, mul_one, haarMode_rawH_eq]
      ring
    · intro k _ hkj
      rw [ite_eq_right (Ne.symm hkj), mul_zero, zero_mul]
    · simp

end GMCExplicitDelta.Localization
