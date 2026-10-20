module

public import GMCExplicitDelta.Proofs.FluxBound.CellBounds
public import GMCExplicitDelta.Proofs.FluxBound.Haar

/-! # G1(c): Frozen energy identities and partition into descendant cells. -/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open scoped ENNReal

namespace GMCExplicitDelta.Localization.FluxBound

open Assembly Contract

variable {d : ℕ}

theorem pos_of_mem_234 {d : ℕ} (hd : d ∈ ({2, 3, 4} : Finset ℕ)) : 0 < d := by
  have h : d = 2 ∨ d = 3 ∨ d = 4 := by simpa using hd
  omega

theorem vecNormSq_smul' (c : ℝ) (w : Homogenization.Vec d) :
    vecNormSq (c • w) = c ^ 2 * vecNormSq w := by
  simp only [vecNormSq, vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem memLp_frozenGrad (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    (p q : Homogenization.Vec d) (ω : SubdiffusiveProcess.Model.PotentialSample d) (i : Fin d) :
    MemLp (fun x => (frozenH1 M L (cubeAt 0 n) p q ω).grad x i) 2
      (normalizedCubeMeasure (originCube d (n : ℤ))) := by
  have hsub : openCubeSet (originCube d (n : ℤ)) ⊆
      ((cubeAt 0 n : Ch02.Domain d) : Set (Homogenization.Vec d)) := by
    intro x hx
    show x ∈ translateSet 0 (openCubeSet (originCube d (n : ℤ)))
    simpa using hx
  exact H1Function.grad_memL2_normalizedCubeMeasure
    ((frozenH1 M L (cubeAt 0 n) p q ω).restrict (isOpen_openCubeSet _) hsub) i

theorem dot_grad_flux (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (p q : Homogenization.Vec d) (ω : SubdiffusiveProcess.Model.PotentialSample d)
    (x : Homogenization.Vec d) :
    vecDot ((frozenH1 M L U p q ω).grad x) (frozenFlux M L U p q ω x) =
      SubdiffusiveProcess.Model.aCutoff M L ω x *
        vecNormSq ((frozenSol M L U p q ω).toH1.grad x) := by
  have hs := ahom_pos' M L
  have hsq : Real.sqrt (ahom M L) * Real.sqrt (ahom M L) = ahom M L := Real.mul_self_sqrt hs.le
  show vecDot (Real.sqrt (ahom M L) • (frozenSol M L U p q ω).toH1.grad x)
    ((SubdiffusiveProcess.Model.aCutoff M L ω x / ahom M L) •
      (Real.sqrt (ahom M L) • (frozenSol M L U p q ω).toH1.grad x)) = _
  rw [vecDot_smul_left, vecDot_smul_right, vecDot_smul_right]
  have : Real.sqrt (ahom M L) * (SubdiffusiveProcess.Model.aCutoff M L ω x / ahom M L *
      (Real.sqrt (ahom M L) * vecDot ((frozenSol M L U p q ω).toH1.grad x)
        ((frozenSol M L U p q ω).toH1.grad x))) =
      (Real.sqrt (ahom M L) * Real.sqrt (ahom M L)) * (SubdiffusiveProcess.Model.aCutoff M L ω x /
        ahom M L) * vecNormSq ((frozenSol M L U p q ω).toH1.grad x) := by
    unfold vecNormSq; ring
  rw [this, hsq]
  field_simp

theorem twoJ_eq_cubeAverage (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    (p q : Homogenization.Vec d) (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    2 * frozenJ M L (cubeAt 0 n) p q ω =
      cubeAverage (originCube d (n : ℤ)) (fun x => SubdiffusiveProcess.Model.aCutoff M L ω x *
        vecNormSq ((frozenSol M L (cubeAt 0 n) p q ω).toH1.grad x)) := by
  rw [frozenJ_eq_energy_proof M L (cubeAt 0 n) p q ω]
  have hf : (fun x => vecDot ((frozenH1 M L (cubeAt 0 n) p q ω).grad x)
      (frozenFlux M L (cubeAt 0 n) p q ω x)) = fun x => SubdiffusiveProcess.Model.aCutoff M L ω x *
        vecNormSq ((frozenSol M L (cubeAt 0 n) p q ω).toH1.grad x) :=
    funext (dot_grad_flux M L (cubeAt 0 n) p q ω)
  rw [hf, ← average_cellAt_eq_cubeAverage]
  ring

theorem integrableOn_cubeSet_of_domain (R : Homogenization.TriadicCube d)
    {f : Homogenization.Vec d → ℝ}
    (h : Integrable f (volumeMeasureOn ((cellAt 0 R : Ch02.Domain d) : Set (Homogenization.Vec d)))) :
    IntegrableOn f (cubeSet R) volume := by
  rw [integrableOn_cubeSet_iff_integrableOn_openCubeSet]
  rw [cellCarrier_eq R] at h
  simpa [volumeMeasureOn, IntegrableOn] using h

theorem integrableOn_energy (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) (hd0 : 0 < d)
    (p q : Homogenization.Vec d) (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    IntegrableOn (fun x => SubdiffusiveProcess.Model.aCutoff M L ω x *
      vecNormSq ((frozenSol M L (cubeAt 0 n) p q ω).toH1.grad x))
      (cubeSet (originCube d (n : ℤ))) volume :=
  integrableOn_cubeSet_of_domain _
    (Coarse.integrable_energy (aCutoffCoeffOnData M L ω (cubeAt 0 n)) ⟨0, hd0⟩
      (frozenSol M L (cubeAt 0 n) p q ω).toH1.gradMemL2)

/-- The cell averages of `a_L|∇u|²` average to `2J(Q_n)`. -/
theorem avg_cells_energy (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) (hd0 : 0 < d)
    (k : ℕ) (p q : Homogenization.Vec d) (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    descendantsAverage (originCube d (n : ℤ)) k (fun R =>
      cubeAverage R (fun x => SubdiffusiveProcess.Model.aCutoff M L ω x *
        vecNormSq ((frozenSol M L (cubeAt 0 n) p q ω).toH1.grad x))) =
      2 * frozenJ M L (cubeAt 0 n) p q ω := by
  rw [twoJ_eq_cubeAverage,
    cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn _ k _
      (integrableOn_energy M L n hd0 p q ω)]

end GMCExplicitDelta.Localization.FluxBound
