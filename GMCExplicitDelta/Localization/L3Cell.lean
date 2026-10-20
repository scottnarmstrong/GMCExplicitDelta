module

public import GMCExplicitDelta.Localization.L3Basic

/-!
# L3 helpers: second variation on the cells and additivity over the partition

On `Q_n` with depth-`k` cells `R`, for the frozen maximizers (for `a_L`, `(p', q') = (s^{-1/2}p, s^{1/2}q)`):

* `frozenJ_cell_energy`: `J(R) = ½⨍_R A|∇v_R|²`;
* `frozenJ_cell_sub`: `J(R) - ⨍_R ρ = ½⨍_R A|∇v_R - ∇v_Q|²` (second variation with the competitor
  `v_Q|_R`), where `ρ` is the response integrand of `v_Q`;
* `frozenJ_cube_eq_avg_rho`: `J(Q_n) = avg_R ⨍_R ρ` (maximizer on `Q_n`, additivity over the cells).
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open scoped ENNReal

namespace GMCExplicitDelta.Localization

open Assembly Contract

variable {d : ℕ}

theorem cubeAverage_const_mul' (R : Homogenization.TriadicCube d) (c : ℝ)
    (f : Homogenization.Vec d → ℝ) :
    cubeAverage R (fun x => c * f x) = c * cubeAverage R f := by
  unfold cubeAverage
  rw [integral_const_mul]
  ring

theorem isFiniteMeasure_restrict_openCubeSet (Q : Homogenization.TriadicCube d) :
    IsFiniteMeasure (volume.restrict (openCubeSet Q)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact (isBounded_openCubeSet Q).measure_lt_top⟩

section

variable (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
  (ω : SubdiffusiveProcess.Model.PotentialSample d) (n : ℕ) (p q : Homogenization.Vec d)

/-- The response integrand of the frozen maximizer on `Q_n`. -/
noncomputable def rhoQ : Homogenization.Vec d → ℝ :=
  Ch02.responseIntegrand (cubeAt 0 n) (aCutoffCoeffOnData M L ω (cubeAt 0 n)).toCoeffOn
    ((Real.sqrt (ahom M L))⁻¹ • p) (Real.sqrt (ahom M L) • q) (frozenSol M L (cubeAt 0 n) p q ω)

theorem rhoQ_eq (x : Homogenization.Vec d) :
    rhoQ M L ω n p q x =
      -((1 / 2) * (SubdiffusiveProcess.Model.aCutoff M L ω x *
        vecNormSq ((frozenSol M L (cubeAt 0 n) p q ω).toH1.grad x))) -
      SubdiffusiveProcess.Model.aCutoff M L ω x *
        vecDot ((Real.sqrt (ahom M L))⁻¹ • p) ((frozenSol M L (cubeAt 0 n) p q ω).toH1.grad x) +
      vecDot (Real.sqrt (ahom M L) • q) ((frozenSol M L (cubeAt 0 n) p q ω).toH1.grad x) := by
  show -((1 / 2 : ℝ) * vecDot _ (matVecMul (symmPart (scalarCoeffField
      (SubdiffusiveProcess.Model.aCutoff M L ω) x)) _)) -
    vecDot _ (matVecMul (scalarCoeffField (SubdiffusiveProcess.Model.aCutoff M L ω) x) _) +
    vecDot _ _ = _
  rw [symmPart_scalarCoeff, vecDot_scalarCoeff]
  show _ - vecDot _ (matVecMul (Homogenization.scalarMatrix _) _) + _ = _
  rw [Homogenization.matVecMul_scalarMatrix, vecDot_smul_right']

theorem integrableOn_rhoQ :
    IntegrableOn (rhoQ M L ω n p q) (cubeSet (originCube d (n : ℤ))) volume := by
  have := isFiniteMeasure_restrict_openCubeSet (originCube d (n : ℤ))
  have hm := measurableSet_openCubeSet (originCube d (n : ℤ))
  have hb := isBounded_openCubeSet (originCube d (n : ℤ))
  have hg := grad_memLp_sub M L ω (Q := originCube d (n : ℤ)) (R := originCube d (n : ℤ))
    subset_rfl p q
  refine IntegrableOn.congr_set_ae ?_ (cubeSet_ae_eq_openCubeSet _)
  have hc : ∀ i, MemLp (fun _ : Homogenization.Vec d => ((Real.sqrt (ahom M L))⁻¹ • p) i) 2
      (volume.restrict (openCubeSet (originCube d (n : ℤ)))) := fun i => memLp_const _
  have h1 := ((integrable_aCutoff_vecDot M L ω hm hb hg hg).const_mul (1 / 2)).neg
  have h2 := integrable_aCutoff_vecDot M L ω hm hb hc hg
  have h3 := integrable_vecDot_const (Real.sqrt (ahom M L) • q) hg
  have e : rhoQ M L ω n p q = fun x =>
      -((1 / 2) * (SubdiffusiveProcess.Model.aCutoff M L ω x *
        vecDot ((frozenSol M L (cubeAt 0 n) p q ω).toH1.grad x)
          ((frozenSol M L (cubeAt 0 n) p q ω).toH1.grad x))) -
      SubdiffusiveProcess.Model.aCutoff M L ω x *
        vecDot ((Real.sqrt (ahom M L))⁻¹ • p) ((frozenSol M L (cubeAt 0 n) p q ω).toH1.grad x) +
      vecDot (Real.sqrt (ahom M L) • q) ((frozenSol M L (cubeAt 0 n) p q ω).toH1.grad x) := by
    funext x
    rw [rhoQ_eq]
    rfl
  rw [IntegrableOn, e]
  exact (h1.sub h2).add h3

/-- `J(Q_n) = ⨍_{Q_n} ρ` (the frozen maximizer realizes the response). -/
theorem frozenJ_cube_eq_rho :
    frozenJ M L (cubeAt 0 n) p q ω = cubeAverage (originCube d (n : ℤ)) (rhoQ M L ω n p q) := by
  rw [← average_cellAt_eq_cubeAverage]
  exact Ch02.responseJ_eq_responseValue_of_isResponseMaximizer
    (frozenSol_isMaximizer M L (cubeAt 0 n) p q ω)

/-- **Additivity**: `J(Q_n) = avg_{R depth k} ⨍_R ρ`. -/
theorem frozenJ_cube_eq_avg_rho (k : ℕ) :
    frozenJ M L (cubeAt 0 n) p q ω =
      descendantsAverage (originCube d (n : ℤ)) k (fun R => cubeAverage R (rhoQ M L ω n p q)) := by
  rw [frozenJ_cube_eq_rho, cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn _ k _
    (integrableOn_rhoQ M L ω n p q)]

/-- `J(R) = ½⨍_R A|∇v_R|²` on any cell. -/
theorem frozenJ_cell_energy (R : Homogenization.TriadicCube d) :
    frozenJ M L (cellAt 0 R) p q ω = (1 / 2) * cubeAverage R (fun x =>
      SubdiffusiveProcess.Model.aCutoff M L ω x *
        vecNormSq ((frozenSol M L (cellAt 0 R) p q ω).toH1.grad x)) := by
  rw [frozenJ_eq_energy_proof, average_cellAt_eq_cubeAverage]
  congr 2
  funext x
  exact frozen_density M L ω (cellAt 0 R) p q x

/-- **Second variation on a cell**: `J(R) - ⨍_R ρ = ½⨍_R A|∇v_R - ∇v_Q|²`. -/
theorem frozenJ_cell_sub (k : ℕ) {R : Homogenization.TriadicCube d}
    (hR : R ∈ descendantsAtDepth (originCube d (n : ℤ)) k) :
    frozenJ M L (cellAt 0 R) p q ω - cubeAverage R (rhoQ M L ω n p q) =
      (1 / 2) * cubeAverage R (fun x => SubdiffusiveProcess.Model.aCutoff M L ω x *
        vecNormSq ((frozenSol M L (cellAt 0 R) p q ω).toH1.grad x -
          (frozenSol M L (cubeAt 0 n) p q ω).toH1.grad x)) := by
  have hRQ : openCubeSet R ⊆ openCubeSet (originCube d (n : ℤ)) :=
    openCubeSet_subset_of_mem_descendantsAtDepth hR
  have hsub : ((cellAt 0 R : Ch02.Domain d) : Set (Homogenization.Vec d)) ⊆
      ((cubeAt 0 n : Ch02.Domain d) : Set (Homogenization.Vec d)) := by
    show ((cellAt 0 R : Ch02.Domain d) : Set (Homogenization.Vec d)) ⊆
      ((cellAt 0 (originCube d (n : ℤ)) : Ch02.Domain d) : Set (Homogenization.Vec d))
    rw [cellAt_zero_coe, cellAt_zero_coe]
    exact hRQ
  obtain ⟨lam, Lam, hEll⟩ := isEllipticFieldOn_aCutoff M L ω R
  have hEll' : IsEllipticFieldOn lam Lam ((cellAt 0 R : Ch02.Domain d) : Set (Homogenization.Vec d))
      (aCutoffCoeffOnData M L ω (cubeAt 0 n)).toCoeffOn.toCoeffField := by
    rw [cellAt_zero_coe]
    exact hEll
  let w : Ch02.Solution (cellAt 0 R) (aCutoffCoeffOnData M L ω (cellAt 0 R)).toCoeffOn :=
    (frozenSol M L (cubeAt 0 n) p q ω).restrictOfIsEllipticFieldOn (cubeAt 0 n).isOpen
      (cellAt 0 R).isOpen hsub hEll'
  have hw : ∀ x, w.toH1.grad x = (frozenSol M L (cubeAt 0 n) p q ω).toH1.grad x := fun x => rfl
  have hsv := (Ch02.responseBasicVariationalIdentitiesTheory (cellAt 0 R)
    (aCutoffCoeffOnData M L ω (cellAt 0 R)).toCoeffOn).secondVariation_eq
    (frozenSol_isMaximizer M L (cellAt 0 R) p q ω) w
  have hval : Ch02.responseValue (cellAt 0 R) (aCutoffCoeffOnData M L ω (cellAt 0 R)).toCoeffOn
      ((Real.sqrt (ahom M L))⁻¹ • p) (Real.sqrt (ahom M L) • q) w =
      cubeAverage R (rhoQ M L ω n p q) := by
    rw [Ch02.responseValue, average_cellAt_eq_cubeAverage]
    rfl
  have hsec : Ch02.secondVariationEnergyValue (cellAt 0 R)
      (aCutoffCoeffOnData M L ω (cellAt 0 R)).toCoeffOn (frozenSol M L (cellAt 0 R) p q ω) w =
      (1 / 2) * cubeAverage R (fun x => SubdiffusiveProcess.Model.aCutoff M L ω x *
        vecNormSq ((frozenSol M L (cellAt 0 R) p q ω).toH1.grad x -
          (frozenSol M L (cubeAt 0 n) p q ω).toH1.grad x)) := by
    rw [Ch02.secondVariationEnergyValue, average_cellAt_eq_cubeAverage, ← cubeAverage_const_mul']
    congr 1
    funext x
    rw [hw]
    show (1 / 2 : ℝ) * vecDot _ (matVecMul (symmPart (scalarCoeffField
      (SubdiffusiveProcess.Model.aCutoff M L ω) x)) _) = _
    rw [symmPart_scalarCoeff, vecDot_scalarCoeff]
  rw [← hval, ← hsec]
  exact hsv

end

end GMCExplicitDelta.Localization
