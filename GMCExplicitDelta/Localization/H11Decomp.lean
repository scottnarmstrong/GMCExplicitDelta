module

public import GMCExplicitDelta.Localization.H11Step

/-!
# H11 assembly, step 2: the decomposition `u - ū = (a·x - avg) + ∑_k w_k + (R - R̄)`

On `Q_n`, for `u ∈ H¹`, `𝐅 = ∇u`, `a = E_0𝐅`: `affineH1 a` is `x ↦ a·x`, `blockPrimitive 𝐅 k` is a
Neumann primitive of `D_k𝐅` (H2), and `remainderH1 u N = u - a·x - ∑_{k=1}^N blockPrimitive 𝐅 k`
solves the weak Neumann equation with data `𝐅 - E_N𝐅` (`remainderH1_weak`).
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open scoped ENNReal

namespace GMCExplicitDelta.Localization

open Assembly Contract

variable {d : ℕ}

theorem isFiniteMeasure_volumeMeasureOn_openCubeSet (Q : Homogenization.TriadicCube d) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) := by
  simpa [volumeMeasureOn] using
    (isOpenBoundedConvexDomain_openCubeSet Q).isSobolevRegularDomain.isFiniteMeasure_restrict_volume

/-- The affine `H¹` function `x ↦ a·x` on the open cube. -/
noncomputable def affineH1 (Q : Homogenization.TriadicCube d) (a : Homogenization.Vec d) :
    H1Function (openCubeSet Q) :=
  haveI := isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  H1Function.affineOnIsSobolevRegularDomain
    (isOpenBoundedConvexDomain_openCubeSet Q).isSobolevRegularDomain a

theorem affineH1_toFun (Q : Homogenization.TriadicCube d) (a x : Homogenization.Vec d) :
    (affineH1 Q a).toFun x = vecDot a x := by
  have := isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  exact H1Function.affineOnIsSobolevRegularDomain_apply _ a x

theorem affineH1_grad (Q : Homogenization.TriadicCube d) (a x : Homogenization.Vec d) :
    (affineH1 Q a).grad x = a := by
  have := isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  exact H1Function.affineOnIsSobolevRegularDomain_grad _ a x

/-- A Neumann primitive of the Haar block `D_k𝐅` (H2). -/
noncomputable def blockPrimitive (Q : Homogenization.TriadicCube d)
    (F : Homogenization.Vec d → Homogenization.Vec d) (k : ℕ) : H1Function (openCubeSet Q) :=
  Classical.choose (neumann_exists Q (vecIncrement Q k F) fun i =>
    Haar.increment_memLp Q k fun y => F y i)

theorem blockPrimitive_spec (Q : Homogenization.TriadicCube d)
    (F : Homogenization.Vec d → Homogenization.Vec d) (k : ℕ) :
    IsNeumannPrimitive Q (vecIncrement Q k F) (blockPrimitive Q F k) :=
  Classical.choose_spec (neumann_exists Q (vecIncrement Q k F) fun i =>
    Haar.increment_memLp Q k fun y => F y i)

/-- The mean `E_0𝐅 = ⨍_Q 𝐅` as a vector. -/
noncomputable def avgVec (Q : Homogenization.TriadicCube d)
    (F : Homogenization.Vec d → Homogenization.Vec d) : Homogenization.Vec d :=
  fun i => cubeAverage Q fun x => F x i

/-- The remainder `R_N = u - a·x - ∑_{k=1}^N T D_k∇u`. -/
noncomputable def remainderH1 (Q : Homogenization.TriadicCube d) (u : H1Function (openCubeSet Q))
    (N : ℕ) : H1Function (openCubeSet Q) :=
  u - affineH1 Q (avgVec Q u.grad) - ∑ k ∈ Finset.Icc 1 N, blockPrimitive Q u.grad k

/-- The data `𝐅 - E_N𝐅` of the remainder. -/
noncomputable def tailField (Q : Homogenization.TriadicCube d)
    (F : Homogenization.Vec d → Homogenization.Vec d) (N : ℕ) :
    Homogenization.Vec d → Homogenization.Vec d :=
  fun x i => F x i - cubeProjection Q N (fun y => F y i) x

section

variable (Q : Homogenization.TriadicCube d) (u : H1Function (openCubeSet Q)) (N : ℕ)

theorem remainderH1_toFun (x : Homogenization.Vec d) :
    (remainderH1 Q u N).toFun x = u.toFun x - vecDot (avgVec Q u.grad) x -
      ∑ k ∈ Finset.Icc 1 N, (blockPrimitive Q u.grad k).toFun x := by
  simp only [remainderH1, H1Function.sub_toFun]
  rw [H1Function.sum_toFun', affineH1_toFun]

theorem remainderH1_grad (x : Homogenization.Vec d) :
    (remainderH1 Q u N).grad x = u.grad x - avgVec Q u.grad -
      ∑ k ∈ Finset.Icc 1 N, (blockPrimitive Q u.grad k).grad x := by
  simp only [remainderH1, H1Function.sub_grad]
  rw [H1Function.sum_grad', affineH1_grad]

theorem memLp_grad (w : H1Function (openCubeSet Q)) (i : Fin d) :
    MemLp (fun x => w.grad x i) 2 (normalizedCubeMeasure Q) :=
  H1Function.grad_memL2_normalizedCubeMeasure w i

theorem memLp_toFun (w : H1Function (openCubeSet Q)) :
    MemLp w.toFun 2 (normalizedCubeMeasure Q) :=
  H1Function.memL2_normalizedCubeMeasure w

theorem memLp_tailField (i : Fin d) :
    MemLp (fun x => tailField Q u.grad N x i) 2 (normalizedCubeMeasure Q) :=
  (memLp_grad Q u i).sub (Haar.projection_memLp Q N _ 2)

/-- On the cube, `𝐅 - a - ∑_{k=1}^N D_k𝐅 = 𝐅 - E_N𝐅` (telescoping). -/
theorem sub_sub_sum_increment {x : Homogenization.Vec d} (hx : x ∈ cubeSet Q) :
    u.grad x - avgVec Q u.grad - ∑ k ∈ Finset.Icc 1 N, vecIncrement Q k u.grad x =
      tailField Q u.grad N x := by
  funext i
  have htel := cubeIncrement_telescope Q (fun y => u.grad y i) x N
  have hr : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hr, Finset.sum_insert (by simp), cubeIncrement_zero,
    cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth _
      (by simp : Q ∈ descendantsAtDepth Q 0) hx] at htel
  simp only [Pi.sub_apply, Finset.sum_apply, tailField, avgVec, vecIncrement]
  rw [← htel]
  ring

/-- **The remainder solves the weak Neumann equation with data `𝐅 - E_N𝐅`.** -/
theorem remainderH1_weak (φ : H1Function (openCubeSet Q)) :
    cubeAverage Q (fun x => vecDot ((remainderH1 Q u N).grad x) (φ.grad x)) =
      cubeAverage Q (fun x => vecDot (tailField Q u.grad N x) (φ.grad x)) := by
  have hφ := memLp_grad Q φ
  have h1 : (fun x => vecDot ((remainderH1 Q u N).grad x) (φ.grad x)) =
      fun x => vecDot (u.grad x - avgVec Q u.grad -
        ∑ k ∈ Finset.Icc 1 N, (blockPrimitive Q u.grad k).grad x) (φ.grad x) := by
    funext x
    rw [remainderH1_grad]
  rw [h1, cubeAverage_vecDot_sub_sub_sum Q (Finset.Icc 1 N) (avgVec Q u.grad) (memLp_grad Q u) hφ
    (fun k _ i => memLp_grad Q (blockPrimitive Q u.grad k) i)]
  have h2 : ∑ k ∈ Finset.Icc 1 N, cubeAverage Q (fun x =>
      vecDot ((blockPrimitive Q u.grad k).grad x) (φ.grad x)) =
      ∑ k ∈ Finset.Icc 1 N, cubeAverage Q (fun x => vecDot (vecIncrement Q k u.grad x) (φ.grad x)) :=
    Finset.sum_congr rfl fun k _ => (blockPrimitive_spec Q u.grad k).2 φ
  rw [h2, ← cubeAverage_vecDot_sub_sub_sum Q (Finset.Icc 1 N) (avgVec Q u.grad) (memLp_grad Q u) hφ
    (A := fun k x => vecIncrement Q k u.grad x)
    (fun k _ i => Haar.increment_memLp Q k (fun y => u.grad y i))]
  apply cubeAverage_congr_on_cubeSet
  intro x hx
  rw [sub_sub_sum_increment Q u N hx]

theorem integrable_toFun (w : H1Function (openCubeSet Q)) :
    Integrable w.toFun (normalizedCubeMeasure Q) :=
  (memLp_toFun Q w).integrable (by norm_num)

theorem cubeAverage_remainderH1 :
    cubeAverage Q (remainderH1 Q u N).toFun = cubeAverage Q u.toFun -
      cubeAverage Q (fun x => vecDot (avgVec Q u.grad) x) -
      ∑ k ∈ Finset.Icc 1 N, cubeAverage Q (blockPrimitive Q u.grad k).toFun := by
  have h : (remainderH1 Q u N).toFun = fun x => (u.toFun x - vecDot (avgVec Q u.grad) x) -
      ∑ k ∈ Finset.Icc 1 N, (blockPrimitive Q u.grad k).toFun x := by
    funext x
    rw [remainderH1_toFun]
  have haff : Integrable (fun x => vecDot (avgVec Q u.grad) x) (normalizedCubeMeasure Q) := by
    have := integrable_toFun Q (affineH1 Q (avgVec Q u.grad))
    have e : (affineH1 Q (avgVec Q u.grad)).toFun = fun x => vecDot (avgVec Q u.grad) x :=
      funext (affineH1_toFun Q (avgVec Q u.grad))
    rwa [e] at this
  rw [h, cubeAverage_sub' Q (f := fun x => u.toFun x - vecDot (avgVec Q u.grad) x)
      (g := fun x => ∑ k ∈ Finset.Icc 1 N, (blockPrimitive Q u.grad k).toFun x)
      ((integrable_toFun Q u).sub haff)
      (integrable_finsetSum _ fun k _ => integrable_toFun Q (blockPrimitive Q u.grad k)),
    cubeAverage_sub' Q (f := u.toFun) (g := fun x => vecDot (avgVec Q u.grad) x)
      (integrable_toFun Q u) haff,
    cubeAverage_finsetSum Q _ fun k _ => integrable_toFun Q (blockPrimitive Q u.grad k)]

end

end GMCExplicitDelta.Localization
