module

public import GMCExplicitDelta.Proofs.Variance.Cauchy

/-! # Frobenius pairing algebra for scalar centers -/

@[expose] public section

open MeasureTheory Matrix Homogenization Homogenization.Book

namespace GMCExplicitDelta.Assembly

variable {d : ℕ}

theorem frozenVar_matrixPair_add_left (A B C : Homogenization.Mat d) :
    frozenVar_matrixPair (A + B) C = frozenVar_matrixPair A C + frozenVar_matrixPair B C := by
  simp only [frozenVar_matrixPair, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem frozenVar_matrixPair_add_right (A B C : Homogenization.Mat d) :
    frozenVar_matrixPair A (B + C) = frozenVar_matrixPair A B + frozenVar_matrixPair A C := by
  simp only [frozenVar_matrixPair, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem frozenVar_matrixPair_sub_left (A B C : Homogenization.Mat d) :
    frozenVar_matrixPair (A - B) C = frozenVar_matrixPair A C - frozenVar_matrixPair B C := by
  simp only [frozenVar_matrixPair, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem frozenVar_matrixPair_sub_right (A B C : Homogenization.Mat d) :
    frozenVar_matrixPair A (B - C) = frozenVar_matrixPair A B - frozenVar_matrixPair A C := by
  simp only [frozenVar_matrixPair, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem frozenVar_matrixPair_smul_left (A B : Homogenization.Mat d) (c : ℝ) :
    frozenVar_matrixPair (c • A) B = c * frozenVar_matrixPair A B := by
  change Matrix (Fin d) (Fin d) ℝ at A B
  simp only [frozenVar_matrixPair, Matrix.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]

theorem frozenVar_matrixPair_smul_right (A B : Homogenization.Mat d) (c : ℝ) :
    frozenVar_matrixPair A (c • B) = c * frozenVar_matrixPair A B := by
  change Matrix (Fin d) (Fin d) ℝ at A B
  have hpoint (i j : Fin d) : A i j * (c * B i j) = c * (A i j * B i j) := mul_left_comm _ _ _
  simp only [frozenVar_matrixPair, Matrix.smul_apply, smul_eq_mul, hpoint, ← Finset.mul_sum]

theorem frozenVar_matrixPair_one_left (A : Homogenization.Mat d) : frozenVar_matrixPair 1 A = Matrix.trace A := by
  simp [frozenVar_matrixPair, Matrix.one_apply, Matrix.trace, Matrix.diag]

theorem frozenVar_matrixPair_one_right (A : Homogenization.Mat d) : frozenVar_matrixPair A 1 = Matrix.trace A := by
  simp [frozenVar_matrixPair, Matrix.one_apply, Matrix.trace, Matrix.diag]

/-- Splitting both scalar centers leaves only the centered pairing and traces. -/
theorem frozenVar_matrixPair_center (D Z : Homogenization.Mat d) (δ g : ℝ) :
    frozenVar_matrixPair D (Z + g • 1) =
      frozenVar_matrixPair (D - δ • 1) Z + g * Matrix.trace D + δ * Matrix.trace Z := by
  rw [frozenVar_matrixPair_add_right, frozenVar_matrixPair_smul_right, frozenVar_matrixPair_one_right,
    frozenVar_matrixPair_sub_left, frozenVar_matrixPair_smul_left, frozenVar_matrixPair_one_left]
  ring

end GMCExplicitDelta.Assembly
