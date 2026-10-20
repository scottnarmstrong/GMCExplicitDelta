module

public import GMCExplicitDelta.Proofs.GradPieces.Restriction

/-!
Pieces of the localization argument on the good event (steps L2, G1).
Helper declarations live in the namespace `Localization.GradPieces`.

# Localization pieces: the frozen solution on the cells of `Q_n`

For a depth-`k` cell `R` of `Q_n` on which `J^max(R; b_L) ≤ θ`:
* `cell_grad_bound`: `ā |(∇u)_R|² ≤ 𝗑(θ) ⨍_R a_L|∇u|²` (C5);
* `cell_diff_bound`: `ā |(∇u)_R - (∇u_R)_R|² ≤ 2𝗑(θ)(J(R) - ⨍_R 𝔯)` (G1(c) for `u|_R - u_R`, C1(d)),
where `u = frozenSol Q_n` and `u_R` is the maximizer on `R`, `𝔯` the response integrand of `u`.
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta.Localization.GradPieces

open Assembly Contract

variable {d : ℕ}

/-- The restriction of the frozen solution of `Q_n` to a depth-`k` cell. -/
noncomputable def cellRestr (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) (n k : ℕ) (p q : Homogenization.Vec d)
    {R : Homogenization.TriadicCube d}
    (hR : R ∈ descendantsAtDepth (originCube d (n : ℤ)) k) :
    Ch02.Solution (cellAt 0 R) (cutA M L ω (cellAt 0 R)) :=
  restrictSol M L ω (cell_subset hR) (frozenSol M L (cubeAt 0 n) p q ω)

theorem varE_cell_eq (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) (R : Homogenization.TriadicCube d)
    (w : Ch02.Solution (cellAt 0 R) (cutA M L ω (cellAt 0 R))) :
    Ch02.variationEnergyValue (cellAt 0 R) (cutA M L ω (cellAt 0 R)) w =
      cubeAverage R (fun x => SubdiffusiveProcess.Model.aCutoff M L ω x *
        vecNormSq (w.toH1.grad x)) := by
  rw [Coarse.variationEnergyValue_eq_average (cutA_symm M L ω (cellAt 0 R)),
    ← average_cellAt_eq_cubeAverage]
  congr 1
  funext x
  exact Coarse.vecDot_scalar_coeff (aCutoffCoeffOnData M L ω (cellAt 0 R)) x _

theorem avgGrad_cell_eq (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) (R : Homogenization.TriadicCube d)
    (w : Ch02.Solution (cellAt 0 R) (cutA M L ω (cellAt 0 R))) :
    Ch02.averageGradient (cellAt 0 R) (cutA M L ω (cellAt 0 R)) w =
      cubeAverageVec R w.toH1.grad := by
  funext i
  exact average_cellAt_eq_cubeAverage R _

theorem cell_grad_bound (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) (n k : ℕ) (p q : Homogenization.Vec d)
    {R : Homogenization.TriadicCube d} (hR : R ∈ descendantsAtDepth (originCube d (n : ℤ)) k)
    {θ : ℝ} (hθ : 0 ≤ θ)
    (hdef : ∀ e : Homogenization.Vec d, e ⬝ᵥ e = 1 → frozenJ M L (cellAt 0 R) e e ω ≤ θ) :
    ahom M L * vecNormSq (cubeAverageVec R (frozenSol M L (cubeAt 0 n) p q ω).toH1.grad) ≤
      Coarse.xfun θ * cubeAverage R (fun x => SubdiffusiveProcess.Model.aCutoff M L ω x *
        vecNormSq ((frozenSol M L (cubeAt 0 n) p q ω).toH1.grad x)) := by
  have h := c5_grad M L ω (cellAt 0 R) hθ hdef (cellRestr M L ω n k p q hR)
  rw [avgGrad_cell_eq, varE_cell_eq] at h
  exact h

/-- The averaged gradient of the frozen maximizer on `U` is `-p + Y_U q`. -/
theorem average_frozenGrad (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (U : Ch02.Domain d) (p q : Homogenization.Vec d)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) (i : Fin d) :
    Ch02.average U (fun x => (frozenH1 M L U p q ω).grad x i) =
      (-p + (frozenY M L U ω).mulVec q) i := by
  have hs := ahom_pos' M L
  have hsym := (aCutoffCoeffOnData M L ω U).isSymmetric
  have hg := (Ch02.responseBasicVariationalIdentitiesTheory U _).averageGradient_eq
    (frozenSol_isMaximizer M L U p q ω)
  show Ch02.average U (fun x => (Real.sqrt (ahom M L) •
    (frozenSol M L U p q ω).toH1.grad x) i) = _
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Coarse.average_const_mul']
  have hgi := congrFun hg i
  simp only [Ch02.averageGradient, Ch02.averageVec] at hgi
  rw [hgi]
  have hk : Ch02.kappaCoarse U (aCutoffCoeffOnData M L ω U).toCoeffOn = 0 :=
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

/-- `√ā · (∇u_U)_U = -p + Y_U q` for the unscaled maximizer `u_U`. -/
theorem sqrt_smul_avgGrad (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (U : Ch02.Domain d) (p q : Homogenization.Vec d)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    Real.sqrt (ahom M L) • Ch02.averageGradient U (cutA M L ω U) (frozenSol M L U p q ω) =
      -p + (frozenY M L U ω).mulVec q := by
  funext i
  rw [← average_frozenGrad M L U p q ω i]
  show Real.sqrt (ahom M L) * Ch02.average U (fun x => (frozenSol M L U p q ω).toH1.grad x i) =
    Ch02.average U (fun x => (Real.sqrt (ahom M L) • (frozenSol M L U p q ω).toH1.grad x) i)
  rw [← Coarse.average_const_mul']
  rfl

/-- **G1(c) for the difference `u|_R - u_R`, with C1(d).** -/
theorem cell_diff_bound (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) (n k : ℕ) (p q : Homogenization.Vec d)
    {R : Homogenization.TriadicCube d} (hR : R ∈ descendantsAtDepth (originCube d (n : ℤ)) k)
    {θ : ℝ} (hθ : 0 ≤ θ)
    (hdef : ∀ e : Homogenization.Vec d, e ⬝ᵥ e = 1 → frozenJ M L (cellAt 0 R) e e ω ≤ θ) :
    ahom M L * vecNormSq (cubeAverageVec R (frozenSol M L (cubeAt 0 n) p q ω).toH1.grad -
        Ch02.averageGradient (cellAt 0 R) (cutA M L ω (cellAt 0 R))
          (frozenSol M L (cellAt 0 R) p q ω)) ≤
      Coarse.xfun θ * (2 * (frozenJ M L (cellAt 0 R) p q ω -
        cubeAverage R (Ch02.responseIntegrand (cubeAt 0 n) (cutA M L ω (cubeAt 0 n))
          ((Real.sqrt (ahom M L))⁻¹ • p) (Real.sqrt (ahom M L) • q)
          (frozenSol M L (cubeAt 0 n) p q ω)))) := by
  set w := cellRestr M L ω n k p q hR with hw
  set uR := frozenSol M L (cellAt 0 R) p q ω with huR
  set dd := solDiff M L ω (cellAt 0 R) w uR with hdd
  have hc := c5_grad M L ω (cellAt 0 R) hθ hdef dd
  -- the averaged gradient of the difference
  have havg : Ch02.averageGradient (cellAt 0 R) (cutA M L ω (cellAt 0 R)) dd =
      cubeAverageVec R (frozenSol M L (cubeAt 0 n) p q ω).toH1.grad -
        Ch02.averageGradient (cellAt 0 R) (cutA M L ω (cellAt 0 R)) uR := by
    funext i
    have hf : (fun x => dd.toH1.grad x i) =
        fun x => w.toH1.grad x i - uR.toH1.grad x i := by
      funext x
      rw [hdd, solDiff_grad]
      rfl
    show Ch02.average (cellAt 0 R) (fun x => dd.toH1.grad x i) = _
    rw [hf, Coarse.average_sub' (Coarse.integrable_grad_comp w.toH1.gradMemL2 i)
      (Coarse.integrable_grad_comp uR.toH1.gradMemL2 i)]
    have h1 := congrFun (avgGrad_cell_eq M L ω R w) i
    show Ch02.averageGradient (cellAt 0 R) (cutA M L ω (cellAt 0 R)) w i -
      Ch02.averageGradient (cellAt 0 R) (cutA M L ω (cellAt 0 R)) uR i = _
    rw [h1]
    rfl
  -- the energy of the difference
  have hE : Ch02.variationEnergyValue (cellAt 0 R) (cutA M L ω (cellAt 0 R)) dd =
      2 * Ch02.secondVariationEnergyValue (cellAt 0 R) (cutA M L ω (cellAt 0 R)) uR w := by
    unfold Ch02.variationEnergyValue Ch02.secondVariationEnergyValue
    rw [← Coarse.average_const_mul']
    congr 1
    funext x
    simp only [Ch02.variationEnergyIntegrand]
    have hneg : uR.toH1.grad x - w.toH1.grad x = -(dd.toH1.grad x) := by
      rw [hdd, solDiff_grad]
      abel
    rw [hneg, matVecMul_neg, vecDot_neg_left, vecDot_neg_right]
    ring
  have hsv := (Ch02.responseBasicVariationalIdentitiesTheory (cellAt 0 R)
    (cutA M L ω (cellAt 0 R))).second_variation _ _ uR
    (frozenSol_isMaximizer M L (cellAt 0 R) p q ω) w
  have hJ : Ch02.responseJ (cellAt 0 R) (cutA M L ω (cellAt 0 R))
      ((Real.sqrt (ahom M L))⁻¹ • p) (Real.sqrt (ahom M L) • q) =
      frozenJ M L (cellAt 0 R) p q ω := rfl
  have hv : Ch02.responseValue (cellAt 0 R) (cutA M L ω (cellAt 0 R))
      ((Real.sqrt (ahom M L))⁻¹ • p) (Real.sqrt (ahom M L) • q) w =
      cubeAverage R (Ch02.responseIntegrand (cubeAt 0 n) (cutA M L ω (cubeAt 0 n))
        ((Real.sqrt (ahom M L))⁻¹ • p) (Real.sqrt (ahom M L) • q)
        (frozenSol M L (cubeAt 0 n) p q ω)) := by
    unfold Ch02.responseValue
    rw [average_cellAt_eq_cubeAverage]
    rfl
  rw [havg, hE, ← hsv, hJ, hv] at hc
  exact hc

end GMCExplicitDelta.Localization.GradPieces
