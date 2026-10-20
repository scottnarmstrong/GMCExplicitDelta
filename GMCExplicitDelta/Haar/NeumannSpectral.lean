module

public import GMCExplicitDelta.Haar.PoincareCell
public import GMCExplicitDelta.Localization.HaarDefs
public import Homogenization.Geometry.ConvexDomain
public import Homogenization.Sobolev.H1.BasicLemmas

/-!
# Spectral form of the Neumann primitive (H2/H3 on the cosine basis)

For a Neumann primitive `w = T G` on a triadic cube (`IsNeumannPrimitive Q G w`), the cosine
coefficients `c_p = ⨍ C_p w` and the mixed sine coefficients `s_{j,p} = ⨍ M_{j,p} G_j` satisfy
`λ_p c_p = -∑_j (π p_j/ℓ) s_{j,p}` with `λ_p = ∑_j (π p_j/ℓ)²` (test the defining identity with the
cosine mode `C_p`, then apply the mixed coefficient identity to `∂_j w`). With the cosine Parseval
identity this gives `‖w‖² = ∑_{p ≠ 0} c_p²`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open Homogenization

namespace GMCExplicitDelta.Haar

variable {d : ℕ}

/-- The cosine mode `C_p` of a cube. -/
def cubeCos (Q : TriadicCube d) (p : Fin d → ℤ) : Vec d → ℝ :=
  Torus.boxMode (cubeCorner Q) (cubeScaleFactor Q) ∅ p

/-- The mixed mode `M_{j,p}` of a cube (sine in coordinate `j`). -/
def cubeSin (Q : TriadicCube d) (j : Fin d) (p : Fin d → ℤ) : Vec d → ℝ :=
  Torus.boxMode (cubeCorner Q) (cubeScaleFactor Q) {j} p

/-- `π p_j / ℓ`. -/
def cubeFreq (Q : TriadicCube d) (p : Fin d → ℤ) (j : Fin d) : ℝ :=
  Real.pi * p j / cubeScaleFactor Q

/-- The Neumann eigenvalue `λ_p = ∑_j (π p_j/ℓ)²`. -/
def cubeEig (Q : TriadicCube d) (p : Fin d → ℤ) : ℝ := ∑ j, cubeFreq Q p j ^ 2

theorem hasDerivAt_modeFactor_cos (a : Fin d → ℝ) (ℓ : ℝ) (n : Fin d → ℤ) (i : Fin d)
    (t : ℝ) :
    HasDerivAt (Torus.modeFactor a ℓ ∅ n i)
      (-(Real.pi * n i / ℓ) * Torus.modeFactor a ℓ {i} n i t) t := by
  rw [Torus.modeFactor_of_notMem a ℓ n (Finset.notMem_empty i),
    Torus.modeFactor_of_mem a ℓ n (Finset.mem_singleton_self i)]
  beta_reduce
  have h : HasDerivAt (fun s : ℝ => Real.pi * n i * (s - a i) / ℓ) (Real.pi * n i / ℓ) t := by
    have := (((hasDerivAt_id t).sub_const (a i)).const_mul (Real.pi * n i)).div_const ℓ
    simpa using this
  have := (Real.hasDerivAt_cos _).comp t h
  rw [show -(Real.pi * n i / ℓ) * Real.sin (Real.pi * n i * (t - a i) / ℓ) =
      -Real.sin (Real.pi * n i * (t - a i) / ℓ) * (Real.pi * n i / ℓ) by ring]
  exact this

/-- The partial derivatives of the cosine mode. -/
theorem fderiv_cubeCos_apply (Q : TriadicCube d) (p : Fin d → ℤ) (x : Vec d) (j : Fin d) :
    fderiv ℝ (cubeCos Q p) x (basisVec j) = -cubeFreq Q p j * cubeSin Q j p x := by
  classical
  have hd : ∀ i, Differentiable ℝ
      (Torus.modeFactor (cubeCorner Q) (cubeScaleFactor Q) ∅ p i) := fun i =>
    (Torus.contDiff_modeFactor _ _ _ _ i (m := 1)).differentiable (by simp)
  have h := Torus.fderiv_prod_apply_basisVec _ hd x j
  have hcos : cubeCos Q p = fun y : Fin d → ℝ =>
      ∏ i, Torus.modeFactor (cubeCorner Q) (cubeScaleFactor Q) ∅ p i (y i) := rfl
  rw [hcos, h, (hasDerivAt_modeFactor_cos _ _ p j (x j)).deriv]
  unfold cubeSin cubeFreq
  rw [Torus.boxMode_eq_prod_modeFactor, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
  have hrest : ∏ i ∈ Finset.univ.erase j,
      Torus.modeFactor (cubeCorner Q) (cubeScaleFactor Q) ∅ p i (x i) =
      ∏ i ∈ Finset.univ.erase j,
        Torus.modeFactor (cubeCorner Q) (cubeScaleFactor Q) {j} p i (x i) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    simp [Torus.modeFactor, hij]
  rw [hrest]
  ring

theorem contDiff_cubeCos (Q : TriadicCube d) (p : Fin d → ℤ) {m : ℕ∞} :
    ContDiff ℝ m (cubeCos Q p) := by
  show ContDiff ℝ m (fun y : Fin d → ℝ =>
    ∏ i ∈ Finset.univ, Torus.modeFactor (cubeCorner Q) (cubeScaleFactor Q) ∅ p i (y i))
  refine contDiff_prod (t := Finset.univ)
    (f := fun i (y : Fin d → ℝ) => Torus.modeFactor (cubeCorner Q) (cubeScaleFactor Q) ∅ p i (y i))
    fun i _ => ?_
  exact (Torus.contDiff_modeFactor _ _ _ _ i).comp (contDiff_apply ℝ ℝ i)

/-- The cosine mode as an `H¹` function on the open cube. -/
def cubeCosH1 (Q : TriadicCube d) (p : Fin d → ℤ) : H1Function (openCubeSet Q) :=
  H1Function.ofContDiffOnIsOpenBoundedConvexDomain (isOpenBoundedConvexDomain_openCubeSet Q)
    (contDiff_cubeCos Q p (m := 1))

theorem cubeCosH1_toFun (Q : TriadicCube d) (p : Fin d → ℤ) :
    (cubeCosH1 Q p).toFun = cubeCos Q p := rfl

theorem cubeCosH1_grad (Q : TriadicCube d) (p : Fin d → ℤ) (x : Vec d) (j : Fin d) :
    (cubeCosH1 Q p).grad x j = -cubeFreq Q p j * cubeSin Q j p x :=
  fderiv_cubeCos_apply Q p x j

theorem memLp_mode_mul {Q : TriadicCube d} {f m : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) (hm : Continuous m)
    (hb : ∀ x, |m x| ≤ 1) : Integrable (fun x => m x * f x) (normalizedCubeMeasure Q) := by
  refine (hf.integrable one_le_two).bdd_mul (c := 1) hm.aestronglyMeasurable ?_
  exact Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hb x

/-- **Spectral identity of the Neumann primitive.** -/
theorem neumann_coeff_identity (Q : TriadicCube d) {G : Vec d → Vec d}
    (hG : ∀ j, MemLp (fun x => G x j) 2 (normalizedCubeMeasure Q))
    {w : H1Function (openCubeSet Q)}
    (hw : GMCExplicitDelta.Localization.IsNeumannPrimitive Q G w) (p : Fin d → ℤ) :
    cubeEig Q p * ∫ x, cubeCos Q p x * w.toFun x ∂normalizedCubeMeasure Q =
      -∑ j, cubeFreq Q p j * ∫ x, cubeSin Q j p x * G x j ∂normalizedCubeMeasure Q := by
  have hℓ : 0 < cubeScaleFactor Q := cubeScaleFactor_pos' Q
  have hwL : MemLp w.toFun 2 (normalizedCubeMeasure Q) := memLp_normalized_of_memL2On w.memL2
  have hwG : ∀ j, MemLp (fun x => w.grad x j) 2 (normalizedCubeMeasure Q) := fun j =>
    memLp_normalized_of_memL2On (w.gradMemL2 j)
  have hcont_sin : ∀ j, Continuous (cubeSin Q j p) := fun j =>
    Torus.continuous_boxMode _ _ _ _
  have hb_sin : ∀ j x, |cubeSin Q j p x| ≤ 1 := fun j x => Torus.abs_boxMode_le _ _ _ _ _
  -- the defining identity tested with the cosine mode
  have hint1 : ∀ j ∈ (Finset.univ : Finset (Fin d)), Integrable
      (fun x => w.grad x j * (-cubeFreq Q p j * cubeSin Q j p x)) (normalizedCubeMeasure Q) := by
    intro j _
    have := (memLp_mode_mul (hwG j) (hcont_sin j) (hb_sin j)).const_mul (-cubeFreq Q p j)
    refine this.congr (Eventually.of_forall fun x => ?_)
    ring
  have hint2 : ∀ j ∈ (Finset.univ : Finset (Fin d)), Integrable
      (fun x => G x j * (-cubeFreq Q p j * cubeSin Q j p x)) (normalizedCubeMeasure Q) := by
    intro j _
    have := (memLp_mode_mul (hG j) (hcont_sin j) (hb_sin j)).const_mul (-cubeFreq Q p j)
    refine this.congr (Eventually.of_forall fun x => ?_)
    ring
  have h := hw.2 (cubeCosH1 Q p)
  simp only [cubeCosH1_grad, vecDot] at h
  rw [cubeAverage_eq_integral_normalizedCubeMeasure, cubeAverage_eq_integral_normalizedCubeMeasure,
    integral_finsetSum _ hint1, integral_finsetSum _ hint2] at h
  -- the mixed coefficient identity for `∂_j w`
  have hcoef : ∀ j, ∫ x, cubeSin Q j p x * w.grad x j ∂normalizedCubeMeasure Q =
      -cubeFreq Q p j * ∫ x, cubeCos Q p x * w.toFun x ∂normalizedCubeMeasure Q := by
    intro j
    have hU := openCubeSet_eq_box Q
    have hid := Torus.integral_weakDeriv_mul_boxMode (cubeCorner Q) hℓ j p
      (g := w.toFun) (gi := fun x => w.grad x j)
      (by rw [← hU]; exact w.hasWeakGradient j) (by rw [← hU]; exact integrableOn_open_of_memLp hwL)
      (by rw [← hU]; exact integrableOn_open_of_memLp (hwG j))
    have e1 : ∫ x in openCubeSet Q, cubeSin Q j p x * w.grad x j =
        ∫ x in openCubeSet Q, w.grad x j * cubeSin Q j p x := by
      congr 1
      funext x
      ring
    have e2 : ∫ x in openCubeSet Q, cubeCos Q p x * w.toFun x =
        ∫ x in openCubeSet Q, w.toFun x * cubeCos Q p x := by
      congr 1
      funext x
      ring
    rw [integral_normalized_eq_open, integral_normalized_eq_open, e1, e2]
    simp only [cubeSin, cubeCos, cubeFreq, hU]
    rw [hid]
    ring
  have hL : ∀ j, ∫ x, w.grad x j * (-cubeFreq Q p j * cubeSin Q j p x) ∂normalizedCubeMeasure Q =
      cubeFreq Q p j ^ 2 * ∫ x, cubeCos Q p x * w.toFun x ∂normalizedCubeMeasure Q := by
    intro j
    have : (fun x => w.grad x j * (-cubeFreq Q p j * cubeSin Q j p x)) =
        fun x => -cubeFreq Q p j * (cubeSin Q j p x * w.grad x j) := by
      funext x
      ring
    rw [this, integral_const_mul, hcoef]
    ring
  have hR : ∀ j, ∫ x, G x j * (-cubeFreq Q p j * cubeSin Q j p x) ∂normalizedCubeMeasure Q =
      -cubeFreq Q p j * ∫ x, cubeSin Q j p x * G x j ∂normalizedCubeMeasure Q := by
    intro j
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  simp only [hL, hR] at h
  rw [cubeEig, Finset.sum_mul, h]
  simp only [neg_mul, Finset.sum_neg_distrib]

end GMCExplicitDelta.Haar
