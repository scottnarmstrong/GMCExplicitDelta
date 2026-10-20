module

public import GMCExplicitDelta.Haar.NeumannTest

/-!
# H5: the Neumann primitive of a Haar block (duality with the projected Poincaré inequality)

For `k = m + 1 ≥ 1` and a Neumann primitive `w = T D_k 𝐅` on a triadic cube `Q` of side `ℓ`:
`‖w‖² ≤ (5/54)(ℓ/3^m)² ‖D_k 𝐅‖²`, given the projected Poincaré inequality H4 on every cube
(`ProjectedPoincare`). Proof (step H5): for a finite set `S` of nonzero natural frequency
vectors put `A_S = ∑_{q ∈ S} m_q c_q²` (`c_q` the cosine coefficients of `w`). The spectral identity
gives `A_S = ∑_j ⟨G_j, v_j⟩` for the test fields `v_j = ∂_j z` of `z = ∑ (m_q c_q/λ_q) C_q`; since
`G_j = D_k F_j`, `⟨G_j, v_j⟩ = ⟨G_j, D_k v_j⟩`; H4 on the depth-`m` cells bounds
`‖D_k v_j‖² ≤ (5/54)(ℓ/3^m)² ∑_i ‖∂_i v_j‖²` and the Hessian identity gives
`∑_{i,j} ‖∂_i v_j‖² = A_S`. Hence `A_S ≤ (5/54)(ℓ/3^m)²‖G‖²`, and the cosine Parseval identity
(grouping `p ∈ ℤ^d` by `|p|`, at most `m_q` vectors per class) gives the bound for `‖w‖²`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open Homogenization

namespace GMCExplicitDelta.Haar

variable {d : ℕ}

open Torus

/-- **H4 on every cube** (the projected triadic Poincaré inequality with constant `5/54`). -/
def ProjectedPoincare (d : ℕ) : Prop :=
  ∀ (U : TriadicCube d) (v : Vec d → ℝ) (g : Fin d → Vec d → ℝ), Continuous v →
    (∀ i, Continuous (g i)) →
    (∀ (i : Fin d) (x : Vec d), HasDerivAt (fun t => v (Function.update x i t)) (g i x) (x i)) →
    energy U (cubeIncrement U 1 v) ≤ 5 / 54 * cubeScaleFactor U ^ 2 * ∑ i, energy U (g i)

theorem increment_succ_eq_on_cell {Q U : TriadicCube d} {m : ℕ}
    (hU : U ∈ descendantsAtDepth Q m) (v : Vec d → ℝ) {x : Vec d} (hx : x ∈ cubeSet U) :
    cubeIncrement Q (m + 1) v x = cubeIncrement U 1 v x := by
  obtain ⟨S, hS, hxS⟩ := exists_mem_descendantsAtDepth_of_mem_cubeSet 1 hx
  have hS' : S ∈ descendantsAtDepth Q (m + 1) := mem_descendantsAtDepth_add hU hS
  show cubeProjection Q (m + 1) v x - cubeProjection Q m v x =
    cubeProjection U (0 + 1) v x - cubeProjection U 0 v x
  rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth v hS' hxS,
    cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth v hU hx,
    cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth v hS hxS,
    cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth v
      (by simp : U ∈ descendantsAtDepth U 0) hx]

/-- **H4 summed over the depth-`m` cells.** -/
theorem energy_increment_le (hH4 : ProjectedPoincare d) (Q : TriadicCube d) (m : ℕ)
    {v : Vec d → ℝ} {g : Fin d → Vec d → ℝ} (hv : Continuous v) (hg : ∀ i, Continuous (g i))
    (hder : ∀ (i : Fin d) (x : Vec d),
      HasDerivAt (fun t => v (Function.update x i t)) (g i x) (x i))
    (hgL : ∀ i, MemLp (g i) 2 (normalizedCubeMeasure Q)) :
    energy Q (cubeIncrement Q (m + 1) v) ≤
      5 / 54 * (cubeScaleFactor Q / 3 ^ m) ^ 2 * ∑ i, energy Q (g i) := by
  rw [energy_eq_descendantsAverage Q m (increment_memLp Q (m + 1) v)]
  have hcell : ∀ U ∈ descendantsAtDepth Q m, energy U (cubeIncrement Q (m + 1) v) ≤
      5 / 54 * (cubeScaleFactor Q / 3 ^ m) ^ 2 * ∑ i, energy U (g i) := by
    intro U hU
    have heq : energy U (cubeIncrement Q (m + 1) v) = energy U (cubeIncrement U 1 v) := by
      unfold energy pairing
      refine cubeAverage_congr_on_cubeSet fun x hx => ?_
      beta_reduce
      rw [increment_succ_eq_on_cell hU v hx]
    rw [heq, ← cubeScaleFactor_descendant_eq_div_pow hU]
    exact hH4 U v g hv hg hder
  refine (descendantsAverage_le hcell).trans (le_of_eq ?_)
  rw [descendantsAverage_mul_left, descendantsAverage_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (energy_eq_descendantsAverage Q m (hgL i)).symm

/-- The increment is a self-adjoint projection. -/
theorem pairing_increment_right (Q : TriadicCube d) (m : ℕ) {f g : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    pairing Q (cubeIncrement Q (m + 1) f) g =
      pairing Q (cubeIncrement Q (m + 1) f) (cubeIncrement Q (m + 1) g) := by
  rw [pairing_increment_succ Q m hf hg, cubeIncrement_succ,
    pairing_sub_left Q (projection_memLp Q (m + 1) f 2) (projection_memLp Q m f 2) hg,
    projection_selfAdjoint Q (m + 1) hf hg, projection_selfAdjoint Q m hf hg,
    pairing_projections Q (m + 1) (m + 1) hf hg, pairing_projections Q m m hf hg, min_self,
    min_self]

/-! ### Grouping integer frequencies by their absolute values -/

/-- `|p|`, componentwise. -/
def natAbsVec (p : Fin d → ℤ) : Fin d → ℕ := fun i => (p i).natAbs

theorem card_filter_natAbsVec_le (T : Finset (Fin d → ℤ)) (q : Fin d → ℕ) :
    (((T.filter fun p => natAbsVec p = q).card : ℕ) : ℝ) ≤ modeMult q := by
  classical
  have hsub : T.filter (fun p => natAbsVec p = q) ⊆
      Fintype.piFinset (fun i => ({(q i : ℤ), -(q i : ℤ)} : Finset ℤ)) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [Fintype.mem_piFinset]
    intro i
    have h := congrFun hp.2 i
    simp only [natAbsVec] at h
    rcases Int.natAbs_eq (p i) with h' | h'
    · rw [h', h]
      simp
    · rw [h', h]
      simp
  calc (((T.filter fun p => natAbsVec p = q).card : ℕ) : ℝ)
      ≤ ((Fintype.piFinset (fun i => ({(q i : ℤ), -(q i : ℤ)} : Finset ℤ))).card : ℝ) :=
        Nat.cast_le.2 (Finset.card_le_card hsub)
    _ = ∏ i, (({(q i : ℤ), -(q i : ℤ)} : Finset ℤ).card : ℝ) := by
        rw [Fintype.card_piFinset, Nat.cast_prod]
    _ = modeMult q := by
        unfold modeMult
        refine Finset.prod_congr rfl fun i _ => ?_
        by_cases h : q i = 0
        · simp [h]
        · rw [if_neg h, Finset.card_pair (by omega)]
          norm_num

theorem sum_le_sum_image_natAbsVec (T : Finset (Fin d → ℤ)) (φ : (Fin d → ℕ) → ℝ)
    (hφ : ∀ q, 0 ≤ φ q) :
    ∑ p ∈ T, φ (natAbsVec p) ≤ ∑ q ∈ T.image natAbsVec, modeMult q * φ q := by
  classical
  rw [Finset.sum_comp]
  refine Finset.sum_le_sum fun q _ => ?_
  rw [nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (card_filter_natAbsVec_le T q) (hφ q)

theorem cubeCos_natAbsVec (Q : TriadicCube d) (p : Fin d → ℤ) :
    cubeCos Q p = cubeCos Q (natVec (natAbsVec p)) := by
  funext x
  unfold cubeCos
  rw [boxMode_eq_prod_modeFactor, boxMode_eq_prod_modeFactor]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [modeFactor, Finset.notMem_empty, if_false, natVec, natAbsVec]
  rcases Int.natAbs_eq (p i) with h | h
  · conv_lhs => rw [h]
  · conv_lhs => rw [h]
    rw [← Real.cos_neg]
    congr 1
    push_cast
    ring

theorem cubeCos_natVec_zero (Q : TriadicCube d) (x : Vec d) :
    cubeCos Q (natVec (0 : Fin d → ℕ)) x = 1 := by
  simp [cubeCos, boxMode, natVec]

/-! ### The H5 bound -/

/-- **Partial sums of the spectral expansion** of `w`. -/
theorem partial_sum_le (hH4 : ProjectedPoincare d) (Q : TriadicCube d) (m : ℕ)
    (F : Vec d → Vec d) (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (w : H1Function (openCubeSet Q))
    (hw : GMCExplicitDelta.Localization.IsNeumannPrimitive Q
      (GMCExplicitDelta.Localization.vecIncrement Q (m + 1) F) w)
    (S : Finset (Fin d → ℕ)) (hS : ∀ q ∈ S, q ≠ 0) :
    ∑ q ∈ S, modeMult q * (∫ x, cubeCos Q (natVec q) x * w.toFun x ∂normalizedCubeMeasure Q) ^ 2
      ≤ 5 / 54 * (cubeScaleFactor Q / 3 ^ m) ^ 2 *
        GMCExplicitDelta.Localization.vecEnergy Q
          (GMCExplicitDelta.Localization.vecIncrement Q (m + 1) F) := by
  classical
  set K : ℝ := 5 / 54 * (cubeScaleFactor Q / 3 ^ m) ^ 2 with hK
  set G := GMCExplicitDelta.Localization.vecIncrement Q (m + 1) F with hGdef
  have hGj : ∀ j, (fun x => G x j) = cubeIncrement Q (m + 1) (fun y => F y j) := fun j => rfl
  have hG : ∀ j, MemLp (fun x => G x j) 2 (normalizedCubeMeasure Q) := fun j => by
    rw [hGj]
    exact increment_memLp Q (m + 1) _
  set c : (Fin d → ℕ) → ℝ := fun q => ∫ x, cubeCos Q (natVec q) x * w.toFun x ∂normalizedCubeMeasure Q with hc
  set β : (Fin d → ℕ) → ℝ := fun q => modeMult q * c q / cubeEig Q (natVec q) with hβ
  set A : ℝ := ∑ q ∈ S, modeMult q * c q ^ 2 with hA
  have hlam : ∀ q ∈ S, cubeEig Q (natVec q) ≠ 0 := fun q hq =>
    (cubeEig_natVec_pos Q (hS q hq)).ne'
  have hA0 : 0 ≤ A :=
    Finset.sum_nonneg fun q _ => mul_nonneg (modeMult_pos q).le (sq_nonneg _)
  -- the duality identity `A = ∑_j ⟨G_j, v_j⟩`
  have hdual : A = ∑ j, pairing Q (fun x => G x j) (testField Q S β j) := by
    rw [hA, Finset.sum_congr rfl fun j _ => pairing_testField Q S β j (hG j), Finset.sum_comm]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hid := neumann_coeff_identity Q hG hw (natVec q)
    have h1 : ∑ j, -(β q) * cubeFreq Q (natVec q) j *
        ∫ x, cubeSin Q j (natVec q) x * G x j ∂normalizedCubeMeasure Q =
        -(β q) * ∑ j, cubeFreq Q (natVec q) j * ∫ x, cubeSin Q j (natVec q) x * G x j ∂normalizedCubeMeasure Q := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [h1, ← neg_neg (∑ j, cubeFreq Q (natVec q) j * ∫ x, cubeSin Q j (natVec q) x * G x j ∂normalizedCubeMeasure Q),
      ← hid]
    simp only [hβ, hc]
    field_simp [hlam q hq]
  -- each pairing through the increment
  have hpair : ∀ j, pairing Q (fun x => G x j) (testField Q S β j) ≤
      l2Norm Q (fun x => G x j) * l2Norm Q (cubeIncrement Q (m + 1) (testField Q S β j)) := by
    intro j
    rw [hGj, pairing_increment_right Q m (hF j) (memLp_testField Q S β j)]
    exact (le_abs_self _).trans (abs_pairing_le Q (increment_memLp Q (m + 1) _)
      (increment_memLp Q (m + 1) _))
  -- H4 for each test field
  have hDv : ∀ j, energy Q (cubeIncrement Q (m + 1) (testField Q S β j)) ≤
      K * ∑ i, energy Q (testHess Q S β j i) := fun j =>
    energy_increment_le hH4 Q m (continuous_testField Q S β j) (continuous_testHess Q S β j)
      (hasDerivAt_testField Q S β j) (memLp_testHess Q S β j)
  -- the Hessian identity
  have hHess : ∑ j, ∑ i, energy Q (testHess Q S β j i) = A := by
    rw [sum_energy_testHess, hA]
    refine Finset.sum_congr rfl fun q hq => ?_
    simp only [hβ]
    have hm := (modeMult_pos q).ne'
    field_simp [hlam q hq]
  -- Cauchy–Schwarz
  have hsq_l2 : ∀ f : Vec d → ℝ, l2Norm Q f ^ 2 = energy Q f := fun f =>
    Real.sq_sqrt (energy_nonneg Q f)
  have hCS : A ^ 2 ≤ GMCExplicitDelta.Localization.vecEnergy Q G * (K * A) := by
    have h1 : A ≤ ∑ j, l2Norm Q (fun x => G x j) *
        l2Norm Q (cubeIncrement Q (m + 1) (testField Q S β j)) := by
      rw [hdual]
      exact Finset.sum_le_sum fun j _ => hpair j
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => l2Norm Q (fun x => G x j))
      (fun j => l2Norm Q (cubeIncrement Q (m + 1) (testField Q S β j)))
    simp only [hsq_l2] at h2
    have h3 : ∑ j, energy Q (cubeIncrement Q (m + 1) (testField Q S β j)) ≤ K * A := by
      rw [← hHess, Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => hDv j
    calc A ^ 2 ≤ (∑ j, l2Norm Q (fun x => G x j) *
          l2Norm Q (cubeIncrement Q (m + 1) (testField Q S β j))) ^ 2 :=
          pow_le_pow_left₀ hA0 h1 2
      _ ≤ _ := h2
      _ ≤ GMCExplicitDelta.Localization.vecEnergy Q G * (K * A) :=
          mul_le_mul_of_nonneg_left h3
            (Finset.sum_nonneg fun j _ => energy_nonneg Q _)
  have hE0 : 0 ≤ GMCExplicitDelta.Localization.vecEnergy Q G :=
    Finset.sum_nonneg fun j _ => energy_nonneg Q _
  rcases hA0.lt_or_eq with hpos | hzero
  · have : A * A ≤ (K * GMCExplicitDelta.Localization.vecEnergy Q G) * A := by
      nlinarith [hCS]
    exact le_of_mul_le_mul_right this hpos
  · rw [← hzero]
    exact mul_nonneg (by rw [hK]; positivity) hE0

/-- **H5 (primitive on Haar blocks), given H4.** -/
theorem neumann_block_bound_of_projectedPoincare (hH4 : ProjectedPoincare d)
    (Q : TriadicCube d) (m : ℕ) (F : Vec d → Vec d)
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (w : H1Function (openCubeSet Q))
    (hw : GMCExplicitDelta.Localization.IsNeumannPrimitive Q
      (GMCExplicitDelta.Localization.vecIncrement Q (m + 1) F) w) :
    energy Q w.toFun ≤ 5 / 54 * (cubeScaleFactor Q / 3 ^ m) ^ 2 *
      GMCExplicitDelta.Localization.vecEnergy Q
        (GMCExplicitDelta.Localization.vecIncrement Q (m + 1) F) := by
  classical
  set c : (Fin d → ℕ) → ℝ := fun q => ∫ x, cubeCos Q (natVec q) x * w.toFun x ∂normalizedCubeMeasure Q with hc
  have hℓ := cubeScaleFactor_pos' Q
  have hwL : MemLp w.toFun 2 (normalizedCubeMeasure Q) := memLp_normalized_of_memL2On w.memL2
  have hP : HasSum (fun p : Fin d → ℤ => (∫ x, cubeCos Q p x * w.toFun x ∂normalizedCubeMeasure Q) ^ 2)
      (∫ x, w.toFun x ^ 2 ∂normalizedCubeMeasure Q) := by
    have huB : MemLp w.toFun 2 (boxMeasure (cubeCorner Q) (cubeScaleFactor Q)) := by
      rw [boxMeasure_eq_normalizedCubeMeasure]
      exact hwL
    have h := hasSum_sq_boxCoeff_cos (cubeCorner Q) hℓ huB
    rw [boxMeasure_eq_normalizedCubeMeasure] at h
    exact h
  have hc0 : c 0 = 0 := by
    simp only [hc, cubeCos_natVec_zero, one_mul]
    rw [← cubeAverage_eq_integral_normalizedCubeMeasure]
    exact hw.1
  rw [energy_eq_integral_sq, ← hP.tsum_eq]
  refine Real.tsum_le_of_sum_le (fun p => sq_nonneg _) fun T => ?_
  calc ∑ p ∈ T, (∫ x, cubeCos Q p x * w.toFun x ∂normalizedCubeMeasure Q) ^ 2
      = ∑ p ∈ T, c (natAbsVec p) ^ 2 := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [cubeCos_natAbsVec Q p]
    _ ≤ ∑ q ∈ T.image natAbsVec, modeMult q * c q ^ 2 :=
        sum_le_sum_image_natAbsVec T (fun q => c q ^ 2) fun q => sq_nonneg _
    _ = ∑ q ∈ (T.image natAbsVec).erase 0, modeMult q * c q ^ 2 :=
        (Finset.sum_erase _ (by simp [hc0])).symm
    _ ≤ _ := partial_sum_le hH4 Q m F hF w hw _ fun q hq => Finset.ne_of_mem_erase hq

end GMCExplicitDelta.Haar
