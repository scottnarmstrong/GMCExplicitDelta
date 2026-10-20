module

public import GMCExplicitDelta.Localization.Bridge
public import GMCExplicitDelta.Localization.Subadd
public import Homogenization.Besov.Localization

/-!
# L3 helpers: energy densities, integrability on cubes, restriction to cells

Fix `M, L, ω, p, q`; `A = a_L(ω)` (the scalar cutoff coefficient), `s = ā_L`, and the frozen
maximizers `v_U = frozenSol M L U p q ω` (for `a_L` with `(s^{-1/2}p, s^{1/2}q)`).

* `frozen_density`: `∇v^b·b∇v^b = A|∇v_U|²` (`v^b = √s v_U`, `b = A/s`).
* `memLp_aCutoff_mul`, `integrableOn_aCutoff_vecDot`, …: `L²`/`L¹` bookkeeping on bounded sets.
* `grad_memLp_cell`: gradients of frozen maximizers are `L²` on (sub)cubes.
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open scoped ENNReal

namespace GMCExplicitDelta.Localization

open Assembly Contract

variable {d : ℕ}

theorem cellAt_zero_coe (R : Homogenization.TriadicCube d) :
    ((cellAt 0 R : Ch02.Domain d) : Set (Homogenization.Vec d)) = openCubeSet R := by
  show translateSet 0 (openCubeSet R) = openCubeSet R
  simp

theorem vecDot_smul_right' (c : ℝ) (x y : Homogenization.Vec d) :
    vecDot x (c • y) = c * vecDot x y := by
  simp only [vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem vecDot_scalarCoeff (a : Homogenization.Vec d → ℝ) (x ξ : Homogenization.Vec d) :
    vecDot ξ (matVecMul (scalarCoeffField a x) ξ) = a x * vecNormSq ξ := by
  show vecDot ξ (matVecMul (Homogenization.scalarMatrix (a x)) ξ) = _
  rw [Homogenization.matVecMul_scalarMatrix, vecDot_smul_right']
  rfl

theorem symmPart_scalarCoeff (a : Homogenization.Vec d → ℝ) (x : Homogenization.Vec d) :
    symmPart (scalarCoeffField a x) = scalarCoeffField a x :=
  Coarse.symmPart_of_isSymm (Homogenization.scalarMatrix_isSymm (a x))

section Model

variable (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
  (ω : SubdiffusiveProcess.Model.PotentialSample d)

/-- `∇v^b·b∇v^b = A|∇v_U|²` for the frozen maximizer. -/
theorem frozen_density (U : Ch02.Domain d) (p q : Homogenization.Vec d) (x : Homogenization.Vec d) :
    vecDot ((frozenH1 M L U p q ω).grad x) (frozenFlux M L U p q ω x) =
      SubdiffusiveProcess.Model.aCutoff M L ω x *
        vecNormSq ((frozenSol M L U p q ω).toH1.grad x) := by
  have hs := ahom_pos' M L
  have hsq : Real.sqrt (ahom M L) * Real.sqrt (ahom M L) = ahom M L :=
    Real.mul_self_sqrt hs.le
  have ht0 : Real.sqrt (ahom M L) ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
  set t := Real.sqrt (ahom M L) with ht
  simp only [frozenFlux, frozenH1, H1Function.smul_grad, vecDot, vecNormSq, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hsq]
  field_simp
  rw [Real.sq_sqrt (sq_nonneg t)]

theorem aCutoff_bounded (S : Set (Homogenization.Vec d)) (hS : Bornology.IsBounded S) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ S, |SubdiffusiveProcess.Model.aCutoff M L ω x| ≤ C := by
  obtain ⟨C, hC⟩ := hS.isCompact_closure.exists_bound_of_continuousOn
    (SubdiffusiveProcess.Model.continuous_aCutoff M L ω).continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  have := hC x (subset_closure hx)
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

theorem memLp_aCutoff_mul {S : Set (Homogenization.Vec d)} (hSm : MeasurableSet S)
    (hSb : Bornology.IsBounded S) {f : Homogenization.Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict S)) :
    MemLp (fun x => SubdiffusiveProcess.Model.aCutoff M L ω x * f x) 2 (volume.restrict S) := by
  obtain ⟨C, hC0, hC⟩ := aCutoff_bounded M L ω S hSb
  refine MemLp.of_le (hf.const_mul C)
    ((SubdiffusiveProcess.Model.continuous_aCutoff M L ω).aestronglyMeasurable.mul
      hf.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem hSm] with x hx
  simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hC0]
  exact mul_le_mul_of_nonneg_right (hC x hx) (abs_nonneg _)

theorem integrable_aCutoff_vecDot {S : Set (Homogenization.Vec d)} (hSm : MeasurableSet S)
    (hSb : Bornology.IsBounded S) {g h : Homogenization.Vec d → Homogenization.Vec d}
    (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict S))
    (hh : ∀ i, MemLp (fun x => h x i) 2 (volume.restrict S)) :
    Integrable (fun x => SubdiffusiveProcess.Model.aCutoff M L ω x * vecDot (g x) (h x))
      (volume.restrict S) := by
  have e : (fun x => SubdiffusiveProcess.Model.aCutoff M L ω x * vecDot (g x) (h x)) =
      fun x => ∑ i, (SubdiffusiveProcess.Model.aCutoff M L ω x * g x i) * h x i := by
    funext x
    simp only [vecDot, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  exact integrable_finsetSum _ fun i _ =>
    (memLp_aCutoff_mul M L ω hSm hSb (hg i)).integrable_mul (hh i)

theorem integrable_vecDot_const {S : Set (Homogenization.Vec d)} [IsFiniteMeasure (volume.restrict S)]
    (c : Homogenization.Vec d) {g : Homogenization.Vec d → Homogenization.Vec d}
    (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict S)) :
    Integrable (fun x => vecDot c (g x)) (volume.restrict S) := by
  simp only [vecDot]
  exact integrable_finsetSum _ fun i _ => ((hg i).integrable (by norm_num)).const_mul (c i)

/-- Gradients of frozen maximizers on a cube are `L²` on every open subcube. -/
theorem grad_memLp_sub {Q R : Homogenization.TriadicCube d} (hRQ : openCubeSet R ⊆ openCubeSet Q)
    (p q : Homogenization.Vec d) (i : Fin d) :
    MemLp (fun x => (frozenSol M L (cellAt 0 Q) p q ω).toH1.grad x i) 2
      (volume.restrict (openCubeSet R)) := by
  have h := (frozenSol M L (cellAt 0 Q) p q ω).toH1.gradMemL2 i
  have hsub : openCubeSet R ⊆ ((cellAt 0 Q : Ch02.Domain d) : Set (Homogenization.Vec d)) := by
    rw [cellAt_zero_coe]; exact hRQ
  exact h.mono_measure (Measure.restrict_mono hsub le_rfl)

end Model

end GMCExplicitDelta.Localization
