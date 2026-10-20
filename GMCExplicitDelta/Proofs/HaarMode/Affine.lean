module

public import GMCExplicitDelta.Proofs.HaarMode.Field

/-! # The affine factor and the H¹ cutoff field -/

@[expose] public section

open MeasureTheory Homogenization Set Filter

namespace GMCExplicitDelta.Localization

variable {d : ℕ}

/-- Sums of H¹ representatives commute with evaluation and weak differentiation. -/
theorem haarMode_h1_sum {U : Set (Homogenization.Vec d)} {ι : Type*}
    (s : Finset ι) (u : ι → H1Function U) :
    (∑ i ∈ s, u i).toFun = (fun x => ∑ i ∈ s, u i x) ∧
    (∑ i ∈ s, u i).grad = (fun x j => ∑ i ∈ s, (u i).grad x j) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨rfl, rfl⟩
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi, H1Function.add_toFun, H1Function.add_grad, ih]
    exact ⟨trivial, funext fun _ => funext fun _ => rfl⟩

/-- The normalized affine factor and its constant weak gradient. -/
theorem haarMode_affine_h1 (n : ℕ) (a : Homogenization.Vec d) :
    ∃ u : H1Function (openCubeSet (originCube d (n : ℤ))),
      u.toFun = (fun x => vecDot a (fun i => x i / (3 : ℝ) ^ n)) ∧
      u.grad = (fun _ j => ((3 : ℝ) ^ n)⁻¹ * a j) := by
  classical
  choose v hvf hvg using haarMode_scaled_coordinate (d := d) n
  refine ⟨∑ i, a i • v i, ?_, ?_⟩
  · rw [(haarMode_h1_sum Finset.univ _).1]
    funext x
    simp only [H1Function.smul_toFun, hvf, vecDot]
  · rw [(haarMode_h1_sum Finset.univ _).2]
    funext x j
    simp only [H1Function.smul_grad, Pi.smul_apply, smul_eq_mul, hvg,
      basisVec_apply]
    rw [Finset.sum_eq_single j]
    · simp
      ring
    · intro k _ hkj
      simp [Ne.symm hkj]
    · simp

/-- On the cube each normalized coordinate has absolute value at most one half. -/
theorem haarMode_coordinate_bound (n : ℕ) {x : Homogenization.Vec d}
    (hx : x ∈ openCubeSet (originCube d (n : ℤ))) (i : Fin d) :
    |x i / (3 : ℝ) ^ n| ≤ 1 / 2 := by
  have hi := (mem_openCubeSet_originCube_iff.1 hx) i
  simp only [zpow_natCast] at hi
  have hpos : 0 < (3 : ℝ) ^ n := pow_pos (by norm_num) _
  exact abs_le.2 ⟨(le_div_iff₀ hpos).2 (by linarith [hi.1]),
    (div_le_iff₀ hpos).2 hi.2.le⟩

/-- A uniform bound for the affine factor on the open cube. -/
theorem haarMode_affine_bound (n : ℕ) (a : Homogenization.Vec d)
    {x : Homogenization.Vec d} (hx : x ∈ openCubeSet (originCube d (n : ℤ))) :
    |vecDot a (fun i => x i / (3 : ℝ) ^ n)| ≤ ∑ i, |a i| / 2 := by
  unfold vecDot
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_left (haarMode_coordinate_bound n hx i) (abs_nonneg _)).trans_eq (by ring)

/-- The affine-cutoff field is H¹ with its full product-rule weak derivative. -/
theorem haarMode_affine_cutoff_h1 {ω : ℝ} (hω : ω ≤ 1 / 2) (n : ℕ)
    (a : Homogenization.Vec d) (i : Fin d) :
    ∃ w : H1Function (openCubeSet (originCube d (n : ℤ))),
      w.toFun = (fun x => vecDot a (fun k => x k / (3 : ℝ) ^ n) *
        haarMode_rawG ω (fun k => x k / (3 : ℝ) ^ n) i) ∧
      ∀ᵐ x ∂volume.restrict (openCubeSet (originCube d (n : ℤ))),
        w.grad x = fun j => ((3 : ℝ) ^ n)⁻¹ *
          (a j * haarMode_rawG ω (fun k => x k / (3 : ℝ) ^ n) i +
            vecDot a (fun k => x k / (3 : ℝ) ^ n) *
              haarMode_rawH ω (fun k => x k / (3 : ℝ) ^ n) i j) := by
  classical
  obtain ⟨u, huf, hug⟩ := haarMode_affine_h1 n a
  obtain ⟨v, hvf, hvg⟩ := haarMode_rawG_h1 hω n i
  let C := max 1 (max |Real.pi / (2 * ω)| ((Real.pi / (2 * ω)) ^ 2))
  let B := max (∑ k, |a k| / 2) (C ^ d)
  have hB : 0 ≤ B := (pow_nonneg (zero_le_one.trans (le_max_left _ _)) d).trans (le_max_right _ _)
  have hu : ∀ᵐ x ∂volume.restrict (openCubeSet (originCube d (n : ℤ))), |u x| ≤ B := by
    filter_upwards [ae_restrict_mem (isOpen_openCubeSet _).measurableSet] with x hx
    rw [show u x = vecDot a (fun k => x k / (3 : ℝ) ^ n) from congrFun huf x]
    exact (haarMode_affine_bound n a hx).trans (le_max_left _ _)
  have hv : ∀ᵐ x ∂volume.restrict (openCubeSet (originCube d (n : ℤ))), |v x| ≤ B :=
    Filter.Eventually.of_forall fun x => by
      rw [show v x = haarMode_rawG ω (fun k => x k / (3 : ℝ) ^ n) i from congrFun hvf x,
        haarMode_rawG, Finset.abs_prod]
      exact (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun k _ => haarMode_atom_abs_le _ _ _)).trans
        (by simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using le_max_right (∑ k, |a k| / 2) (C ^ d))
  obtain ⟨w, hwf, hwg⟩ := haarMode_h1_mul
    (isOpenBoundedConvexDomain_openCubeSet _) u v hB hu hv
  refine ⟨w, by rw [hwf, huf, hvf], ?_⟩
  filter_upwards [hvg] with x hx
  rw [hwg, huf, hvf, hug]
  funext j
  simp only [hx]
  ring

end GMCExplicitDelta.Localization
