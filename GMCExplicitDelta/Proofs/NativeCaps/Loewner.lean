module

public import GMCExplicitDelta.Proofs.NativeCaps.Subadd
public import GMCExplicitDelta.Coarse.Order

/-! # Matrix form of translated frozen subadditivity -/

@[expose] public section

open Homogenization Homogenization.Book Matrix
open GMCExplicitDelta.Averaging GMCExplicitDelta.Insertion
open scoped BigOperators

namespace GMCExplicitDelta.Assembly

/-- Quadratic probes commute with passage from coordinate vectors to Euclidean space. -/
theorem matrixProbe_toLp {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (e : Homogenization.Vec d) :
    matrixProbe (WithLp.toLp 2 e) A = Coarse.qf A e := by
  simp only [matrixProbe_apply, sphereQuadratic, Matrix.inner_toEuclideanCLM,
    Coarse.qf]

/-- Literal Loewner subadditivity of the defect matrices on the translated depth-j partition. -/
theorem frozenDefect_loewner_subadd {d : ℕ}
    (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (z : Homogenization.Vec d)
    (Q : Homogenization.TriadicCube d) (j : ℕ)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    MatLoewnerLE (frozenDefect M L (cellAt z Q) ω)
      (((descendantsAtDepth Q j).card : ℝ)⁻¹ •
        ∑ R ∈ descendantsAtDepth Q j, frozenDefect M L (cellAt z R) ω) := by
  rw [Coarse.matLoewnerLE_iff_qf]
  intro e
  simp only [← matrixProbe_toLp, map_smul, map_sum, smul_eq_mul, matrixProbe_apply]
  exact frozenDefect_subadd_translated M L z Q j ω (WithLp.toLp 2 e)

end GMCExplicitDelta.Assembly
