module

public import GMCExplicitDelta.Proofs.GradPieces.CellBounds
public import GMCExplicitDelta.Proofs.GradPieces.Haar

/-!
Pieces of the localization argument on the good event (steps L2, G1).
Helper declarations live in the namespace `Localization.GradPieces`.

# Localization pieces: cube-level facts about the frozen maximizer on `Q_n`

* `memLp_frozenGrad`: the gradient components of `v` are `L²(Q_n)`;
* `twoJ_eq_cubeAverage`: `2J(Q_n) = ⨍_{Q_n} a_L|∇u|²`;
* `frozenJ_eq_cubeAverage_resp`: `J(Q_n) = ⨍_{Q_n} 𝔯` (response integrand of `u`);
* `cell_unit_bound`: the defect bound of the good event on a depth-`k` cell;
* averages over the depth-`k` cells of cell averages of `a_L|∇u|²` and of `𝔯`.
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open scoped ENNReal

namespace GMCExplicitDelta.Localization.GradPieces

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

theorem integrableOn_resp (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) (hd0 : 0 < d)
    (p q : Homogenization.Vec d) (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    IntegrableOn (Ch02.responseIntegrand (cubeAt 0 n) (cutA M L ω (cubeAt 0 n))
      ((Real.sqrt (ahom M L))⁻¹ • p) (Real.sqrt (ahom M L) • q) (frozenSol M L (cubeAt 0 n) p q ω))
      (cubeSet (originCube d (n : ℤ))) volume := by
  set u := frozenSol M L (cubeAt 0 n) p q ω with hu
  refine integrableOn_cubeSet_of_domain _ ?_
  have h1 := Coarse.integrable_energy (aCutoffCoeffOnData M L ω (cubeAt 0 n)) ⟨0, hd0⟩
    u.toH1.gradMemL2
  have h2 := Coarse.integrable_vecDot_const ((Real.sqrt (ahom M L))⁻¹ • p)
    (fun i => Coarse.integrable_comp (Ch02.Solution.flux_memVectorL2 u) i)
  have h3 := Coarse.integrable_vecDot_const (Real.sqrt (ahom M L) • q)
    (fun i => Coarse.integrable_grad_comp u.toH1.gradMemL2 i)
  refine (((h1.const_mul (-(1 / 2 : ℝ))).sub h2).add h3).congr ?_
  filter_upwards [Coarse.symmPart_ae (cutA_symm M L ω (cubeAt 0 n))] with x hx
  simp only [Ch02.responseIntegrand]
  rw [hx, Coarse.vecDot_scalar_coeff (aCutoffCoeffOnData M L ω (cubeAt 0 n)) x]
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

theorem frozenJ_eq_cubeAverage_resp (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    (p q : Homogenization.Vec d) (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    frozenJ M L (cubeAt 0 n) p q ω =
      cubeAverage (originCube d (n : ℤ)) (Ch02.responseIntegrand (cubeAt 0 n)
        (cutA M L ω (cubeAt 0 n)) ((Real.sqrt (ahom M L))⁻¹ • p) (Real.sqrt (ahom M L) • q)
        (frozenSol M L (cubeAt 0 n) p q ω)) := by
  have h := Ch02.responseJ_eq_responseValue_of_isResponseMaximizer
    (frozenSol_isMaximizer M L (cubeAt 0 n) p q ω)
  have hJ : Ch02.responseJ (cubeAt 0 n) (cutA M L ω (cubeAt 0 n))
      ((Real.sqrt (ahom M L))⁻¹ • p) (Real.sqrt (ahom M L) • q) =
      frozenJ M L (cubeAt 0 n) p q ω := rfl
  rw [← hJ, h]
  unfold Ch02.responseValue
  rw [← average_cellAt_eq_cubeAverage]

theorem cell_unit_bound (row : Row d) (hO : row.Obligations)
    (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) (hω : ω ∈ goodEvent row M L 0 n) (k : ℕ)
    {R : Homogenization.TriadicCube d} (hR : R ∈ descendantsAtDepth (originCube d (n : ℤ)) k) :
    ∀ e : Homogenization.Vec d, e ⬝ᵥ e = 1 →
      frozenJ M L (cellAt 0 R) e e ω ≤ row.thetaR * row.qs ^ k := by
  intro e he
  have h := goodEvent_cell_bound_proof row hO M L n ω hω k R hR
  have ht : 0 ≤ row.thetaR * row.qs ^ k :=
    mul_nonneg (thetaR_nonneg row hO) (pow_nonneg (Real.rpow_nonneg (by norm_num) _) _)
  have h1 : ENNReal.ofReal (frozenJ M L (cellAt 0 R) e e ω) ≤
      ENNReal.ofReal (row.thetaR * row.qs ^ k) := by
    refine le_trans ?_ h
    rw [normalizedDefect_eq_iSup]
    exact le_iSup (fun e : {e : Homogenization.Vec d // vecNormSq e = 1} =>
      ENNReal.ofReal (frozenJ M L (cellAt 0 R) e.1 e.1 ω)) ⟨e, he⟩
  exact (ENNReal.ofReal_le_ofReal_iff ht).1 h1

theorem cubeAverageVec_frozenH1 (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (U : Ch02.Domain d) (p q : Homogenization.Vec d)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) (R : Homogenization.TriadicCube d) :
    cubeAverageVec R (frozenH1 M L U p q ω).grad =
      Real.sqrt (ahom M L) • cubeAverageVec R (frozenSol M L U p q ω).toH1.grad := by
  funext i
  show cubeAverage R (fun x => (Real.sqrt (ahom M L) • (frozenSol M L U p q ω).toH1.grad x) i) =
    Real.sqrt (ahom M L) * cubeAverage R (fun x => (frozenSol M L U p q ω).toH1.grad x i)
  simp only [Pi.smul_apply, smul_eq_mul]
  exact cubeAverage_const_mul R _ _

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

/-- The cell averages of the response integrand average to `J(Q_n)`. -/
theorem avg_cells_resp (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) (hd0 : 0 < d)
    (k : ℕ) (p q : Homogenization.Vec d) (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    descendantsAverage (originCube d (n : ℤ)) k (fun R =>
      cubeAverage R (Ch02.responseIntegrand (cubeAt 0 n) (cutA M L ω (cubeAt 0 n))
        ((Real.sqrt (ahom M L))⁻¹ • p) (Real.sqrt (ahom M L) • q)
        (frozenSol M L (cubeAt 0 n) p q ω))) =
      frozenJ M L (cubeAt 0 n) p q ω := by
  rw [frozenJ_eq_cubeAverage_resp,
    cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn _ k _
      (integrableOn_resp M L n hd0 p q ω)]

theorem descendantsAverage_sub' (Q : Homogenization.TriadicCube d) (k : ℕ)
    (F G : Homogenization.TriadicCube d → ℝ) :
    descendantsAverage Q k (fun R => F R - G R) =
      descendantsAverage Q k F - descendantsAverage Q k G := by
  simp only [descendantsAverage_eq, Finset.sum_sub_distrib]
  ring

end GMCExplicitDelta.Localization.GradPieces
