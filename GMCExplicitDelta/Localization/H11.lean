module

public import GMCExplicitDelta.Localization.H11Decomp

/-!
# H11 assembly, step 3: the Haar summation of the localized test field

`loc_H11_assembled`: for `u ∈ H¹(Q_n)`, `P_s((u - ū)𝐠)² ≤ (∑_k b_k‖D_k∇u‖)²`, from H2 (`neumann_exists`),
H5/H6 (`neumann_block_bound`), H8 (`cell_poincare`), H9 (`haar_multiplier`), H10
(`haar_constant_mode`), Minkowski (`haarPrimal_add_le`) and Haar completeness
(`energy_sub_projection_tendsto`).
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open scoped ENNReal

namespace GMCExplicitDelta.Localization

open Assembly Contract

variable {d : ℕ}

theorem incNorm_zero_sq (Q : Homogenization.TriadicCube d)
    (F : Homogenization.Vec d → Homogenization.Vec d) :
    incNorm Q 0 F ^ 2 = vecNormSq (avgVec Q F) := by
  rw [incNorm_sq]
  unfold vecEnergy vecIncrement
  simp only [cubeIncrement_zero]
  rw [vecNormSq, vecDot]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (fun x => cubeProjection Q 0 (fun y => F y i) x) = cubeProjection Q 0 (fun y => F y i)
    from rfl, Haar.energy_projection_zero, avgVec, pow_two]

section Bounds

variable (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations) (n : ℕ)
  (u : H1Function (openCubeSet (originCube d (n : ℤ))))
include hd hO

/-- The constant mode (H10). -/
theorem h11_bound_zero :
    haarPrimal (originCube d (n : ℤ)) row.qs (fun x =>
        ((affineH1 (originCube d (n : ℤ)) (avgVec (originCube d (n : ℤ)) u.grad)).toFun x -
          cubeAverage (originCube d (n : ℤ))
            (affineH1 (originCube d (n : ℤ)) (avgVec (originCube d (n : ℤ)) u.grad)).toFun) •
        cubeCutoffGrad row n x) ≤
      ENNReal.ofReal ((row.haarB 0 * incNorm (originCube d (n : ℤ)) 0 u.grad) ^ 2) := by
  have h := haar_constant_mode row hd hO n (avgVec (originCube d (n : ℤ)) u.grad)
  have e : (affineH1 (originCube d (n : ℤ)) (avgVec (originCube d (n : ℤ)) u.grad)).toFun =
      fun x => vecDot (avgVec (originCube d (n : ℤ)) u.grad) x :=
    funext (affineH1_toFun _ _)
  rw [mul_pow, incNorm_zero_sq, e]
  exact h

/-- The Haar blocks `k ≥ 1` (H9 with H5/H6). -/
theorem h11_bound_block {k : ℕ} (hk : 1 ≤ k) :
    haarPrimal (originCube d (n : ℤ)) row.qs (fun x =>
        ((blockPrimitive (originCube d (n : ℤ)) u.grad k).toFun x -
          cubeAverage (originCube d (n : ℤ)) (blockPrimitive (originCube d (n : ℤ)) u.grad k).toFun) •
        cubeCutoffGrad row n x) ≤
      ENNReal.ofReal ((row.haarB k * incNorm (originCube d (n : ℤ)) k u.grad) ^ 2) := by
  have hspec := blockPrimitive_spec (originCube d (n : ℤ)) u.grad k
  have hF := memLp_grad (originCube d (n : ℤ)) u
  have hw : Haar.energy (originCube d (n : ℤ))
        (fun x => (blockPrimitive (originCube d (n : ℤ)) u.grad k).toFun x -
          cubeAverage (originCube d (n : ℤ)) (blockPrimitive (originCube d (n : ℤ)) u.grad k).toFun) ≤
      row.haarL k / row.kappaOmega ^ 2 * ((3 : ℝ) ^ n) ^ 2 *
        incNorm (originCube d (n : ℤ)) k u.grad ^ 2 := by
    rw [hspec.1]
    simp only [sub_zero]
    rw [incNorm_sq]
    exact neumann_block_bound row hd hO n k hk u.grad hF _ hspec
  have hgw : vecEnergy (originCube d (n : ℤ)) (blockPrimitive (originCube d (n : ℤ)) u.grad k).grad ≤
      incNorm (originCube d (n : ℤ)) k u.grad ^ 2 := by
    rw [incNorm_sq]
    exact vecEnergy_grad_le_of_weak (originCube d (n : ℤ))
      (fun i => Haar.increment_memLp (originCube d (n : ℤ)) k fun y => u.grad y i) _ hspec.2
  have h := haar_multiplier row hd hO n (blockPrimitive (originCube d (n : ℤ)) u.grad k)
    (Haar.haarL_nonneg row k) (Real.sqrt_nonneg _) hw hgw
  rwa [← haarB_sq_eq_multSq row hO hk, ← mul_pow] at h

/-- The remainder (H9 with H8 at depth `0`). -/
theorem h11_bound_remainder (N : ℕ) :
    haarPrimal (originCube d (n : ℤ)) row.qs (fun x =>
        ((remainderH1 (originCube d (n : ℤ)) u N).toFun x -
          cubeAverage (originCube d (n : ℤ)) (remainderH1 (originCube d (n : ℤ)) u N).toFun) •
        cubeCutoffGrad row n x) ≤
      ENNReal.ofReal ((Real.sqrt (multSq row row.etaOmega) *
        Real.sqrt (vecEnergy (originCube d (n : ℤ)) (tailField (originCube d (n : ℤ)) u.grad N))) ^ 2) := by
  have hρsq : Real.sqrt (vecEnergy (originCube d (n : ℤ))
      (tailField (originCube d (n : ℤ)) u.grad N)) ^ 2 =
      vecEnergy (originCube d (n : ℤ)) (tailField (originCube d (n : ℤ)) u.grad N) :=
    Real.sq_sqrt (vecEnergy_nonneg _ _)
  have hgw : vecEnergy (originCube d (n : ℤ)) (remainderH1 (originCube d (n : ℤ)) u N).grad ≤
      Real.sqrt (vecEnergy (originCube d (n : ℤ)) (tailField (originCube d (n : ℤ)) u.grad N)) ^ 2 := by
    rw [hρsq]
    exact vecEnergy_grad_le_of_weak (originCube d (n : ℤ)) (memLp_tailField _ u N) _
      (remainderH1_weak _ u N)
  have hpoinc := cell_poincare (originCube d (n : ℤ)) 0 (remainderH1 (originCube d (n : ℤ)) u N)
  have hcongr : Haar.energy (originCube d (n : ℤ)) (fun x =>
        (remainderH1 (originCube d (n : ℤ)) u N).toFun x -
          cubeAverage (originCube d (n : ℤ)) (remainderH1 (originCube d (n : ℤ)) u N).toFun) =
      Haar.energy (originCube d (n : ℤ)) (fun x =>
        (remainderH1 (originCube d (n : ℤ)) u N).toFun x -
          cubeProjection (originCube d (n : ℤ)) 0 (remainderH1 (originCube d (n : ℤ)) u N).toFun x) := by
    unfold Haar.energy Haar.pairing
    apply cubeAverage_congr_on_cubeSet
    intro x hx
    dsimp only
    rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth _
      (by simp : originCube d (n : ℤ) ∈ descendantsAtDepth (originCube d (n : ℤ)) 0) hx]
  have hscale : cubeScaleFactor (originCube d (n : ℤ)) = (3 : ℝ) ^ n := by
    rw [cubeScaleFactor_originCube, zpow_natCast]
  have hw : Haar.energy (originCube d (n : ℤ)) (fun x =>
        (remainderH1 (originCube d (n : ℤ)) u N).toFun x -
          cubeAverage (originCube d (n : ℤ)) (remainderH1 (originCube d (n : ℤ)) u N).toFun) ≤
      row.etaOmega / row.kappaOmega ^ 2 * ((3 : ℝ) ^ n) ^ 2 *
        Real.sqrt (vecEnergy (originCube d (n : ℤ)) (tailField (originCube d (n : ℤ)) u.grad N)) ^ 2 := by
    rw [hcongr, etaOmega_div_kappaOmega_sq row hO]
    refine hpoinc.trans ?_
    rw [hscale, pow_zero, one_mul]
    calc ((3 : ℝ) ^ n) ^ 2 / Real.pi ^ 2 *
          vecEnergy (originCube d (n : ℤ)) (remainderH1 (originCube d (n : ℤ)) u N).grad ≤
        ((3 : ℝ) ^ n) ^ 2 / Real.pi ^ 2 * Real.sqrt (vecEnergy (originCube d (n : ℤ))
          (tailField (originCube d (n : ℤ)) u.grad N)) ^ 2 :=
          mul_le_mul_of_nonneg_left hgw (by positivity)
      _ = _ := by ring
  have hη : 0 ≤ row.etaOmega := by unfold Row.etaOmega; positivity
  have h := haar_multiplier row hd hO n (remainderH1 (originCube d (n : ℤ)) u N) hη
    (Real.sqrt_nonneg _) hw hgw
  rwa [← Real.sq_sqrt (multSq_nonneg row hO hη), ← mul_pow] at h

end Bounds

/-- The test field splits into the constant mode, the blocks and the remainder. -/
theorem locTestField_decomp (row : Row d) (n N : ℕ)
    (u : H1Function (openCubeSet (originCube d (n : ℤ)))) :
    locTestField row n u.toFun =
      (fun x =>
        ((affineH1 (originCube d (n : ℤ)) (avgVec (originCube d (n : ℤ)) u.grad)).toFun x -
          cubeAverage (originCube d (n : ℤ))
            (affineH1 (originCube d (n : ℤ)) (avgVec (originCube d (n : ℤ)) u.grad)).toFun) •
          cubeCutoffGrad row n x) +
        (∑ k ∈ Finset.Icc 1 N, fun x =>
          ((blockPrimitive (originCube d (n : ℤ)) u.grad k).toFun x -
            cubeAverage (originCube d (n : ℤ))
              (blockPrimitive (originCube d (n : ℤ)) u.grad k).toFun) • cubeCutoffGrad row n x) +
        (fun x => ((remainderH1 (originCube d (n : ℤ)) u N).toFun x -
          cubeAverage (originCube d (n : ℤ)) (remainderH1 (originCube d (n : ℤ)) u N).toFun) •
          cubeCutoffGrad row n x) := by
  have e : (affineH1 (originCube d (n : ℤ)) (avgVec (originCube d (n : ℤ)) u.grad)).toFun =
      fun x => vecDot (avgVec (originCube d (n : ℤ)) u.grad) x :=
    funext (affineH1_toFun _ _)
  funext x
  simp only [locTestField, Pi.add_apply, Finset.sum_apply]
  rw [remainderH1_toFun, cubeAverage_remainderH1, e, ← Finset.sum_smul, ← add_smul, ← add_smul]
  congr 1
  rw [Finset.sum_sub_distrib]
  ring

/-- **The truncated Haar summation.** For every `N`,
`P_s((u - ū)𝐠)² ≤ (∑_{k≤N} b_k‖D_k∇u‖ + 𝖻(η_ω)‖∇u - E_N∇u‖)²`. -/
theorem loc_H11_truncated (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (n N : ℕ) (u : H1Function (openCubeSet (originCube d (n : ℤ)))) :
    haarPrimal (originCube d (n : ℤ)) row.qs (locTestField row n u.toFun) ≤
      ENNReal.ofReal ((∑ k ∈ Finset.range (N + 1),
          row.haarB k * incNorm (originCube d (n : ℤ)) k u.grad +
        Real.sqrt (multSq row row.etaOmega) *
          Real.sqrt (vecEnergy (originCube d (n : ℤ))
            (tailField (originCube d (n : ℤ)) u.grad N))) ^ 2) := by
  have hq := qs_pos row
  have hr : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [locTestField_decomp row n N u, hr, Finset.sum_insert (by simp)]
  have hc0 : 0 ≤ row.haarB 0 * incNorm (originCube d (n : ℤ)) 0 u.grad :=
    mul_nonneg (haarB_nonneg' row 0) (Real.sqrt_nonneg _)
  have hck : ∀ k ∈ Finset.Icc 1 N, 0 ≤ row.haarB k * incNorm (originCube d (n : ℤ)) k u.grad := fun k _ =>
    mul_nonneg (haarB_nonneg' row k) (Real.sqrt_nonneg _)
  have hcR : 0 ≤ Real.sqrt (multSq row row.etaOmega) *
      Real.sqrt (vecEnergy (originCube d (n : ℤ)) (tailField (originCube d (n : ℤ)) u.grad N)) := by positivity
  have hm0 : ∀ i, MemLp (fun x => ((fun x =>
      ((affineH1 (originCube d (n : ℤ)) (avgVec (originCube d (n : ℤ)) u.grad)).toFun x - cubeAverage (originCube d (n : ℤ)) (affineH1 (originCube d (n : ℤ)) (avgVec (originCube d (n : ℤ)) u.grad)).toFun) •
        cubeCutoffGrad row n x) x) i) 2 (normalizedCubeMeasure (originCube d (n : ℤ))) := fun i =>
    memLp_smul_cutoffGrad row hO n ((memLp_toFun (originCube d (n : ℤ)) _).sub (memLp_const _)) i
  have hmk : ∀ k ∈ Finset.Icc 1 N, ∀ i, MemLp (fun x => ((fun x =>
      ((blockPrimitive (originCube d (n : ℤ)) u.grad k).toFun x - cubeAverage (originCube d (n : ℤ)) (blockPrimitive (originCube d (n : ℤ)) u.grad k).toFun) •
        cubeCutoffGrad row n x) x) i) 2 (normalizedCubeMeasure (originCube d (n : ℤ))) := fun k _ i =>
    memLp_smul_cutoffGrad row hO n ((memLp_toFun (originCube d (n : ℤ)) _).sub (memLp_const _)) i
  have hmR : ∀ i, MemLp (fun x => ((fun x =>
      ((remainderH1 (originCube d (n : ℤ)) u N).toFun x - cubeAverage (originCube d (n : ℤ)) (remainderH1 (originCube d (n : ℤ)) u N).toFun) •
        cubeCutoffGrad row n x) x) i) 2 (normalizedCubeMeasure (originCube d (n : ℤ))) := fun i =>
    memLp_smul_cutoffGrad row hO n ((memLp_toFun (originCube d (n : ℤ)) _).sub (memLp_const _)) i
  have hmsum : ∀ i, MemLp (fun x => (∑ k ∈ Finset.Icc 1 N, fun x =>
      ((blockPrimitive (originCube d (n : ℤ)) u.grad k).toFun x - cubeAverage (originCube d (n : ℤ)) (blockPrimitive (originCube d (n : ℤ)) u.grad k).toFun) •
        cubeCutoffGrad row n x) x i) 2 (normalizedCubeMeasure (originCube d (n : ℤ))) := by
    intro i
    have e : (fun x => (∑ k ∈ Finset.Icc 1 N, fun x =>
        ((blockPrimitive (originCube d (n : ℤ)) u.grad k).toFun x - cubeAverage (originCube d (n : ℤ)) (blockPrimitive (originCube d (n : ℤ)) u.grad k).toFun) •
          cubeCutoffGrad row n x) x i) = fun x => ∑ k ∈ Finset.Icc 1 N,
        (((blockPrimitive (originCube d (n : ℤ)) u.grad k).toFun x - cubeAverage (originCube d (n : ℤ)) (blockPrimitive (originCube d (n : ℤ)) u.grad k).toFun) •
          cubeCutoffGrad row n x) i := by
      funext x
      simp only [Finset.sum_apply]
    rw [e]
    exact memLp_finsetSum _ fun k hk => hmk k hk i
  have hsumle := haarPrimal_sum_le (originCube d (n : ℤ)) hq (Finset.Icc 1 N) _ _ hmk hck
    (fun k hk => h11_bound_block row hd hO n u (Finset.mem_Icc.mp hk).1)
  have h01 := haarPrimal_add_le (originCube d (n : ℤ)) hq hm0 hmsum hc0 (Finset.sum_nonneg hck)
    (h11_bound_zero row hd hO n u) hsumle
  have hm01 : ∀ i, MemLp (fun x => ((fun x =>
      ((affineH1 (originCube d (n : ℤ)) (avgVec (originCube d (n : ℤ)) u.grad)).toFun x - cubeAverage (originCube d (n : ℤ)) (affineH1 (originCube d (n : ℤ)) (avgVec (originCube d (n : ℤ)) u.grad)).toFun) •
        cubeCutoffGrad row n x) + ∑ k ∈ Finset.Icc 1 N, fun x =>
      ((blockPrimitive (originCube d (n : ℤ)) u.grad k).toFun x - cubeAverage (originCube d (n : ℤ)) (blockPrimitive (originCube d (n : ℤ)) u.grad k).toFun) •
        cubeCutoffGrad row n x) x i) 2 (normalizedCubeMeasure (originCube d (n : ℤ))) := fun i =>
    (hm0 i).add (hmsum i)
  have h := haarPrimal_add_le (originCube d (n : ℤ)) hq hm01 hmR (add_nonneg hc0 (Finset.sum_nonneg hck)) hcR h01
    (h11_bound_remainder row hd hO n u N)
  refine h.trans (le_of_eq ?_)
  ring_nf

/-- **H11 (Haar summation of the localized test field)**, assembled. -/
theorem loc_H11_assembled (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (n : ℕ) (u : H1Function (openCubeSet (originCube d (n : ℤ)))) :
    haarPrimal (originCube d (n : ℤ)) row.qs (locTestField row n u.toFun) ≤
      (tsum fun k : ℕ => ENNReal.ofReal (row.haarB k * incNorm (originCube d (n : ℤ)) k u.grad)) ^ 2 := by
  set S := tsum fun k : ℕ => ENNReal.ofReal (row.haarB k * incNorm (originCube d (n : ℤ)) k u.grad) with hS
  set C := Real.sqrt (multSq row row.etaOmega) with hC
  set ρ : ℕ → ℝ := fun N => Real.sqrt (vecEnergy (originCube d (n : ℤ)) (tailField (originCube d (n : ℤ)) u.grad N)) with hρ
  have hρ0 : Filter.Tendsto ρ Filter.atTop (nhds 0) := by
    have h : Filter.Tendsto (fun N => vecEnergy (originCube d (n : ℤ))
        (tailField (originCube d (n : ℤ)) u.grad N)) Filter.atTop (nhds 0) := by
      have := tendsto_finsetSum (Finset.univ : Finset (Fin d)) fun i _ =>
        energy_sub_projection_tendsto (originCube d (n : ℤ)) (memLp_grad (originCube d (n : ℤ)) u i)
      rw [Finset.sum_const_zero] at this
      exact this
    have := (Real.continuous_sqrt.tendsto 0).comp h
    rw [Real.sqrt_zero] at this
    exact this
  have hlim : Filter.Tendsto (fun N => (S + ENNReal.ofReal (C * ρ N)) ^ 2) Filter.atTop
      (nhds (S ^ 2)) := by
    have h1 : Filter.Tendsto (fun N => ENNReal.ofReal (C * ρ N)) Filter.atTop (nhds 0) := by
      have := ENNReal.tendsto_ofReal (hρ0.const_mul C)
      simpa only [mul_zero, ENNReal.ofReal_zero] using this
    have h2 : Filter.Tendsto (fun N => S + ENNReal.ofReal (C * ρ N)) Filter.atTop
        (nhds (S + 0)) := tendsto_const_nhds.add h1
    rw [add_zero] at h2
    exact ((ENNReal.continuous_pow 2).tendsto S).comp h2
  refine ge_of_tendsto' hlim fun N => ?_
  refine (loc_H11_truncated row hd hO n N u).trans ?_
  have hP : 0 ≤ ∑ k ∈ Finset.range (N + 1), row.haarB k * incNorm (originCube d (n : ℤ)) k u.grad :=
    Finset.sum_nonneg fun k _ => mul_nonneg (haarB_nonneg' row k) (Real.sqrt_nonneg _)
  have hCρ : 0 ≤ C * ρ N := by positivity
  rw [ENNReal.ofReal_pow (add_nonneg hP hCρ), ENNReal.ofReal_add hP hCρ]
  gcongr
  rw [ENNReal.ofReal_sum_of_nonneg (f := fun k => row.haarB k * incNorm (originCube d (n : ℤ)) k u.grad)
    fun k _ => mul_nonneg (haarB_nonneg' row k) (Real.sqrt_nonneg _)]
  exact ENNReal.sum_le_tsum _

end GMCExplicitDelta.Localization
