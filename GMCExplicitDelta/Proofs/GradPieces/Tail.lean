module

public import GMCExplicitDelta.Proofs.GradPieces.Cube

/-!
Pieces of the localization argument on the good event (steps L2, G1).
Helper declarations live in the namespace `Localization.GradPieces`.

# Localization pieces: `loc_L2_tail` and `loc_L2_drop`

On the good event, for `k ≥ 1`:
`‖D_k∇v‖² ≤ 2y_k J(Q_n)` (C5 on each depth-`k` cell, G1(a), C6) and
`‖D_k∇v‖ ≤ √(2y_k(J_k - J_0)) + √(cellRes k c)` (H1(e) with `c`, Minkowski over the cells,
G1(c) and C1(d) on each cell).
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open scoped ENNReal

namespace GMCExplicitDelta.Localization.GradPieces

open Assembly Contract

variable {d : ℕ}

theorem yk_eq_xfun (row : Row d) (k : ℕ) :
    row.yk k = Coarse.xfun (row.thetaR * row.qs ^ k) := rfl

theorem theta_nonneg (row : Row d) (hO : row.Obligations) (k : ℕ) :
    0 ≤ row.thetaR * row.qs ^ k :=
  mul_nonneg (thetaR_nonneg row hO) (pow_nonneg (Real.rpow_nonneg (by norm_num) _) _)

end GMCExplicitDelta.Localization.GradPieces

namespace GMCExplicitDelta.Localization

open Assembly Contract GradPieces

variable {d : ℕ}

theorem loc_L2_tail_proof (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) (hω : ω ∈ goodEvent row M L 0 n)
    (p q : Homogenization.Vec d) (k : ℕ) (hk : 1 ≤ k) :
    incNorm (originCube d (n : ℤ)) k (frozenH1 M L (cubeAt 0 n) p q ω).grad ^ 2 ≤
      2 * row.yk k * frozenJ M L (cubeAt 0 n) p q ω := by
  have hd0 := pos_of_mem_234 hd
  have hs := ahom_pos' M L
  have h1 := incNorm_sq_le_proj (originCube d (n : ℤ)) hk (memLp_frozenGrad M L n p q ω)
  have hcell : ∀ R ∈ descendantsAtDepth (originCube d (n : ℤ)) k,
      vecNormSq (cubeAverageVec R (frozenH1 M L (cubeAt 0 n) p q ω).grad) ≤
        row.yk k * cubeAverage R (fun x => SubdiffusiveProcess.Model.aCutoff M L ω x *
          vecNormSq ((frozenSol M L (cubeAt 0 n) p q ω).toH1.grad x)) := by
    intro R hR
    have hb := cell_grad_bound M L ω n k p q hR (theta_nonneg row hO k)
      (cell_unit_bound row hO M L n ω hω k hR)
    rw [cubeAverageVec_frozenH1, vecNormSq_smul', Real.sq_sqrt hs.le]
    rw [yk_eq_xfun]
    exact hb
  calc _ ≤ _ := h1
    _ ≤ descendantsAverage (originCube d (n : ℤ)) k (fun R => row.yk k *
        cubeAverage R (fun x => SubdiffusiveProcess.Model.aCutoff M L ω x *
          vecNormSq ((frozenSol M L (cubeAt 0 n) p q ω).toH1.grad x))) :=
        descendantsAverage_le_descendantsAverage _ k hcell
    _ = row.yk k * (2 * frozenJ M L (cubeAt 0 n) p q ω) := by
        rw [descendantsAverage_mul_left, avg_cells_energy M L n hd0 k p q ω]
    _ = _ := by ring

theorem loc_L2_drop_proof (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) (hω : ω ∈ goodEvent row M L 0 n)
    (p q c : Homogenization.Vec d) (k : ℕ) (hk : 1 ≤ k) :
    incNorm (originCube d (n : ℤ)) k (frozenH1 M L (cubeAt 0 n) p q ω).grad ≤
      Real.sqrt (2 * row.yk k * (cellJ M L n k p q ω - frozenJ M L (cubeAt 0 n) p q ω)) +
        Real.sqrt (cellRes M L n k p q c ω) := by
  have hd0 := pos_of_mem_234 hd
  have hs := ahom_pos' M L
  have hdrop := incNorm_le_drop (originCube d (n : ℤ)) hk (memLp_frozenGrad M L n p q ω)
    (fun R => -p + (frozenY M L (cellAt 0 R) ω).mulVec q) c
  refine hdrop.trans (add_le_add (Real.sqrt_le_sqrt ?_) le_rfl)
  have hcell : ∀ R ∈ descendantsAtDepth (originCube d (n : ℤ)) k,
      vecNormSq (cubeAverageVec R (frozenH1 M L (cubeAt 0 n) p q ω).grad -
          (-p + (frozenY M L (cellAt 0 R) ω).mulVec q)) ≤
        row.yk k * 2 * (frozenJ M L (cellAt 0 R) p q ω -
          cubeAverage R (Ch02.responseIntegrand (cubeAt 0 n) (cutA M L ω (cubeAt 0 n))
            ((Real.sqrt (ahom M L))⁻¹ • p) (Real.sqrt (ahom M L) • q)
            (frozenSol M L (cubeAt 0 n) p q ω))) := by
    intro R hR
    have hb := cell_diff_bound M L ω n k p q hR (theta_nonneg row hO k)
      (cell_unit_bound row hO M L n ω hω k hR)
    have hS := sqrt_smul_avgGrad M L (cellAt 0 R) p q ω
    rw [← hS, cubeAverageVec_frozenH1, ← smul_sub, vecNormSq_smul', Real.sq_sqrt hs.le]
    rw [yk_eq_xfun]
    calc _ ≤ _ := hb
      _ = _ := by ring
  calc _ ≤ descendantsAverage (originCube d (n : ℤ)) k (fun R => row.yk k * 2 *
        (frozenJ M L (cellAt 0 R) p q ω -
          cubeAverage R (Ch02.responseIntegrand (cubeAt 0 n) (cutA M L ω (cubeAt 0 n))
            ((Real.sqrt (ahom M L))⁻¹ • p) (Real.sqrt (ahom M L) • q)
            (frozenSol M L (cubeAt 0 n) p q ω)))) :=
        descendantsAverage_le_descendantsAverage _ k hcell
    _ = row.yk k * 2 * (cellJ M L n k p q ω - frozenJ M L (cubeAt 0 n) p q ω) := by
        rw [descendantsAverage_mul_left, descendantsAverage_sub', avg_cells_resp M L n hd0 k p q ω]
        rfl
    _ = _ := by ring

end GMCExplicitDelta.Localization
