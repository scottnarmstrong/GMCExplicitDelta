module

public import GMCExplicitDelta.Localization.CoreDefs
public import GMCExplicitDelta.Coarse.Competitors
public import GMCExplicitDelta.Coarse.CompetitorsScalar
public import SubdiffusiveProcess.Providers.Section5.ReciprocalLower

/-!
# Localization lane: bridges between the model, Chapter 2 and the triadic cube

* `ahom_pos'`: `ā_m > 0` (from the Section 5 lower bound `e^{-(m+1)τ²} ≤ ā_m`).
* `average_cellAt_eq_cubeAverage`: the Chapter 2 average over the open cell `cellAt 0 R` equals the
  triadic `cubeAverage R` over the half-open cube (null boundary).
* `frozenSol_isMaximizer`, `frozenJ_eq_energy_proof` (C1(b) with C3: `J(U,p,q;b_L) = ½⨍∇v·b_L∇v`),
  `avgVec_frozenGrad` (C1(b) with C3: `⨍_{Q_n}∇v = -p + Y_{Q_n}q`).
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta.Localization

open Assembly Contract

variable {d : ℕ}

theorem ahom_pos' (M : SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) : 0 < ahom M m :=
  (Real.exp_pos _).trans_le
    (SubdiffusiveProcess.Providers.Section5.homogenized_coefficient_reciprocal_lower M m)

/-- The Chapter 2 average over the open cell equals the triadic cube average. -/
theorem average_cellAt_eq_cubeAverage (R : Homogenization.TriadicCube d)
    (f : Homogenization.Vec d → ℝ) : Ch02.average (cellAt 0 R) f = cubeAverage R f := by
  have hc : ((cellAt 0 R : Ch02.Domain d) : Set (Homogenization.Vec d)) = openCubeSet R := by
    show translateSet 0 (openCubeSet R) = openCubeSet R
    simp
  unfold Ch02.average cubeAverage
  rw [hc, volume_openCubeSet_eq_volume_cubeSet, volume_cubeSet_toReal,
    ← setIntegral_cubeSet_eq_setIntegral_openCubeSet]

theorem frozenSol_isMaximizer (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (U : Ch02.Domain d) (p q : Homogenization.Vec d)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    Ch02.IsResponseMaximizer U (aCutoffCoeffOnData M L ω U).toCoeffOn
      ((Real.sqrt (ahom M L))⁻¹ • p) (Real.sqrt (ahom M L) • q) (frozenSol M L U p q ω) :=
  Ch02.canonicalMaximizer_isMaximizer _ _ _

/-- **C1(b) with C3**: `J(U, p, q; b_L) = ½⨍_U ∇v·b_L∇v` for the frozen maximizer `v`. -/
theorem frozenJ_eq_energy_proof (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (U : Ch02.Domain d) (p q : Homogenization.Vec d)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    frozenJ M L U p q ω = (1 / 2) * Ch02.average U fun x =>
      vecDot ((frozenH1 M L U p q ω).grad x) (frozenFlux M L U p q ω x) := by
  have hs := ahom_pos' M L
  have hsym := (aCutoffCoeffOnData M L ω U).isSymmetric
  have hJ := (Ch02.responseBasicVariationalIdentitiesTheory U _).responseJ_eq_energy
    (frozenSol_isMaximizer M L U p q ω)
  rw [Coarse.variationEnergyValue_eq_average hsym] at hJ
  rw [show frozenJ M L U p q ω = Ch02.responseJ U (aCutoffCoeffOnData M L ω U).toCoeffOn
    ((Real.sqrt (ahom M L))⁻¹ • p) (Real.sqrt (ahom M L) • q) from rfl, hJ]
  congr 2
  funext x
  rw [Coarse.vecDot_scalar_coeff]
  simp only [frozenFlux, frozenH1, H1Function.smul_grad]
  have hsq : Real.sqrt (ahom M L) * Real.sqrt (ahom M L) = ahom M L :=
    Real.mul_self_sqrt hs.le
  have ht0 : Real.sqrt (ahom M L) ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
  set t := Real.sqrt (ahom M L) with ht
  simp only [vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hsq]
  field_simp

/-- **C1(b) with C3**: `⨍_{Q_n}∇v = -p + Y_{Q_n}q` (as a triadic cube average). -/
theorem avgVec_frozenGrad (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    (p q : Homogenization.Vec d) (ω : SubdiffusiveProcess.Model.PotentialSample d)
    (i : Fin d) :
    cubeAverage (originCube d (n : ℤ)) (fun x => (frozenH1 M L (cubeAt 0 n) p q ω).grad x i) =
      (-p + (frozenY M L (cubeAt 0 n) ω).mulVec q) i := by
  have hs := ahom_pos' M L
  have hsym := (aCutoffCoeffOnData M L ω (cubeAt 0 n)).isSymmetric
  have hg := (Ch02.responseBasicVariationalIdentitiesTheory (cubeAt 0 n) _).averageGradient_eq
    (frozenSol_isMaximizer M L (cubeAt 0 n) p q ω)
  rw [← average_cellAt_eq_cubeAverage (originCube d (n : ℤ))]
  show Ch02.average (cubeAt 0 n) (fun x => (Real.sqrt (ahom M L) •
    (frozenSol M L (cubeAt 0 n) p q ω).toH1.grad x) i) = _
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Coarse.average_const_mul']
  have hgi := congrFun hg i
  simp only [Ch02.averageGradient, Ch02.averageVec] at hgi
  rw [hgi]
  have hk : Ch02.kappaCoarse (cubeAt 0 n) (aCutoffCoeffOnData M L ω (cubeAt 0 n)).toCoeffOn = 0 :=
    Coarse.kappa_eq_zero hsym
  have hY := Coarse.YU_eq_sigmaStarInv hsym
  simp only [Ch02.coarseMatrices, hk, ← hY]
  have hsq : Real.sqrt (ahom M L) * Real.sqrt (ahom M L) = ahom M L :=
    Real.mul_self_sqrt hs.le
  have hsne : Real.sqrt (ahom M L) ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
  simp only [frozenY, Coarse.YU, Coarse.matVecMul_eq_mulVec, Matrix.zero_mulVec,
    Matrix.mulVec_smul, Matrix.smul_mulVec, Pi.add_apply, Pi.neg_apply, Pi.smul_apply,
    smul_eq_mul, aStarMatrix]
  set t := Real.sqrt (ahom M L) with ht
  rw [← hsq]
  simp only [smul_zero, add_zero, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  have hti : t * t⁻¹ = 1 := mul_inv_cancel₀ hsne
  linear_combination (-(p i)) * hti

end GMCExplicitDelta.Localization
