module

public import GMCExplicitDelta.Proofs.Variance.Initial
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.ProbeSubadditivity

/-! # Cell averages and the frozen subadditivity decrements -/

@[expose] public section

open MeasureTheory Matrix Homogenization Homogenization.Book SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge

namespace GMCExplicitDelta.Assembly

variable {d : ℕ}

theorem frozenVar_cells_eq_depth (n k : ℕ) (hkn : k ≤ n) :
    descendantsAtScale (originCube d (n : ℤ)) (k : ℤ) =
      descendantsAtDepth (originCube d (n : ℤ)) (n - k) := by
  have hknz : (k : ℤ) ≤ (originCube d (n : ℤ)).scale := by
    change (k : ℤ) ≤ (n : ℤ)
    exact_mod_cast hkn
  rw [descendantsAtScale_eq_descendantsAtDepth _ hknz]
  congr 1
  change (Int.toNat ((n : ℤ) - k)) = n - k
  omega

theorem frozenVar_cells_card (n k : ℕ) (hkn : k ≤ n) :
    (descendantsAtScale (originCube d (n : ℤ)) (k : ℤ)).card = 3 ^ (d * (n - k)) := by
  rw [frozenVar_cells_eq_depth n k hkn, descendantsAtDepth_card, ← pow_mul]

theorem frozenVar_cellAvg_add (n k : ℕ) (A B : Ch02.Domain d → Homogenization.Mat d) :
    cellAvg n k (fun U => A U + B U) = cellAvg n k A + cellAvg n k B := by
  simp only [cellAvg, Finset.sum_add_distrib, smul_add]

theorem frozenVar_cellAvg_smul (n k : ℕ) (A : Ch02.Domain d → Homogenization.Mat d) (c : ℝ) :
    cellAvg n k (fun U => c • A U) = c • cellAvg n k A := by
  unfold cellAvg
  rw [← Finset.smul_sum]
  exact smul_comm _ _ _

theorem frozenVar_cellAvg_const (n k : ℕ) (hkn : k ≤ n) (A : Homogenization.Mat d) :
    cellAvg n k (fun _ => A) = A := by
  have hc : ((descendantsAtScale (originCube d (n : ℤ)) (k : ℤ)).card : ℝ) ≠ 0 := by
    rw [frozenVar_cells_card n k hkn]
    positivity
  unfold cellAvg
  rw [Finset.sum_const]
  have hscale : (((descendantsAtScale (originCube d (n : ℤ)) (k : ℤ)).card : ℝ)⁻¹) •
      ((descendantsAtScale (originCube d (n : ℤ)) (k : ℤ)).card • A) = A := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hc, one_smul]
  exact hscale

theorem frozenVar_cellAvg_eq_depth (n k : ℕ) (hkn : k ≤ n)
    (A : Ch02.Domain d → Homogenization.Mat d) :
    cellAvg n k A = descendantsAverageMat (originCube d (n : ℤ)) (n - k)
      (fun R => A (cellAt 0 R)) := by
  ext i j
  simp only [cellAvg, frozenVar_cells_eq_depth n k hkn, descendantsAverageMat,
    descendantsAverage, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]

theorem frozenVar_cellAvg_sub (n k : ℕ) (A B : Ch02.Domain d → Homogenization.Mat d) :
    cellAvg n k (fun U => A U - B U) = cellAvg n k A - cellAvg n k B := by
  simp only [cellAvg, Finset.sum_sub_distrib, smul_sub]

theorem frozenVar_cellAvg_defect (M : SubdiffusiveProcess.Model.GMCModel d) (L n k : ℕ)
    (hkn : k ≤ n) (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    cellAvg n k (fun U => frozenDefect M L U ω) =
      (1 / 2 : ℝ) • (cellAvg n k (fun U => frozenX M L U ω) +
        cellAvg n k (fun U => frozenY M L U ω)) - 1 := by
  simp only [frozenDefect, frozenVar_cellAvg_sub, frozenVar_cellAvg_smul, frozenVar_cellAvg_add,
    frozenVar_cellAvg_const n k hkn]

theorem frozenVar_cellAvg_symm (n k : ℕ) (A : Ch02.Domain d → Homogenization.Mat d)
    (hA : ∀ U, (A U)ᵀ = A U) : (cellAvg n k A)ᵀ = cellAvg n k A := by
  unfold cellAvg
  simp only [Matrix.transpose_smul, Matrix.transpose_sum, hA]

theorem frozenVar_cellAvg_X (M : SubdiffusiveProcess.Model.GMCModel d) (L n k : ℕ)
    (hkn : k ≤ n) (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    cellAvg n k (fun U => frozenX M L U ω) =
      (ahom M L)⁻¹ • descendantsAverageMat (originCube d (n : ℤ)) (n - k)
        (fun R => randomAMatrix M L (Ch02.cubeDomain R) ω) := by
  unfold frozenX
  rw [frozenVar_cellAvg_smul, frozenVar_cellAvg_eq_depth n k hkn]
  congr 1
  apply congrArg (descendantsAverageMat (originCube d (n : ℤ)) (n - k))
  funext R
  rw [Localization.cellMoment_cellAt_zero R]
  rfl

theorem frozenVar_cellAvg_Y (M : SubdiffusiveProcess.Model.GMCModel d) (L n k : ℕ)
    (hkn : k ≤ n) (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    cellAvg n k (fun U => frozenY M L U ω) =
      ahom M L • descendantsAverageMat (originCube d (n : ℤ)) (n - k)
        (fun R => (randomAStarMatrix M L (Ch02.cubeDomain R) ω)⁻¹) := by
  unfold frozenY
  rw [frozenVar_cellAvg_smul, frozenVar_cellAvg_eq_depth n k hkn]
  congr 1
  apply congrArg (descendantsAverageMat (originCube d (n : ℤ)) (n - k))
  funext R
  rw [Localization.cellMoment_cellAt_zero R]
  rfl

/-- Frozen primal and dual subadditivity on the exact scale-k cell average. -/
theorem frozenVar_frozen_subadditive (M : SubdiffusiveProcess.Model.GMCModel d) (L n k : ℕ)
    (hkn : k ≤ n) (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    MatLoewnerLE (frozenX M L (cubeAt 0 n) ω) (cellAvg n k (fun U => frozenX M L U ω)) ∧
      MatLoewnerLE (frozenY M L (cubeAt 0 n) ω) (cellAvg n k (fun U => frozenY M L U ω)) := by
  have hx := matLoewnerLE_randomAMatrix_descendantsAverage' M L ω (originCube d (n : ℤ)) (n - k)
  have hy := matLoewnerLE_randomAStarInv_descendantsAverage M L ω (originCube d (n : ℤ)) (n - k)
  rw [Coarse.matLoewnerLE_iff_qf] at hx hy
  constructor
  · rw [Coarse.matLoewnerLE_iff_qf]
    intro e
    rw [frozenVar_cellAvg_X M L n k hkn ω, frozenX, freshRet_cubeAt_zero]
    simpa only [Coarse.qf, randomAMatrix, randomAStarMatrix, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] using
      mul_le_mul_of_nonneg_left (hx e) (inv_nonneg.mpr (driftSeed_ahom_pos M L).le)
  · rw [Coarse.matLoewnerLE_iff_qf]
    intro e
    rw [frozenVar_cellAvg_Y M L n k hkn ω, frozenY, freshRet_cubeAt_zero]
    simpa only [Coarse.qf, randomAMatrix, randomAStarMatrix, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] using
      mul_le_mul_of_nonneg_left (hy e) (driftSeed_ahom_pos M L).le

end GMCExplicitDelta.Assembly
