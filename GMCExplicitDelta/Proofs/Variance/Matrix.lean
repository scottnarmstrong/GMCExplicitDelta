module

public import GMCExplicitDelta.Assembly.ModelFrozen
public import GMCExplicitDelta.Coarse.Order
public import Mathlib.Analysis.Matrix.Order
public import Homogenization.Book.Ch02.Theorems.MatrixOperatorNorm

/-! # Trace estimates for the frozen variance bounds -/

@[expose] public section

open Matrix Homogenization
open scoped MatrixOrder

namespace GMCExplicitDelta.Assembly

variable {d : ℕ}

/-- The trace of a product of positive semidefinite matrices is nonnegative. -/
theorem frozenVar_trace_mul_nonneg {A B : Homogenization.Mat d}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ Matrix.trace (A * B) := by
  let S := CFC.sqrt B
  have hS : Sᴴ = S := (CFC.sqrt_nonneg B).posSemidef.isHermitian.eq
  have hSS : S * S = B := by
    simpa only [pow_two] using CFC.sq_sqrt B
  have h := (hA.mul_mul_conjTranspose_same S).trace_nonneg
  rw [hS, Matrix.trace_mul_cycle, hSS] at h
  rw [Matrix.trace_mul_comm] at h
  exact h

/-- Frobenius square is the trace of the Gram matrix. -/
theorem frozenVar_frobSq_eq_trace (A : Homogenization.Mat d) :
    frobSq A = Matrix.trace (Aᵀ * A) := by
  simp only [frobSq, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, pow_two]
  exact Finset.sum_comm

/-- Positive matrices bounded by a scalar have a dimension-normalized square bound. -/
theorem frozenVar_trace_sq_le {A : Homogenization.Mat d} {θ : ℝ}
    (hA : A.PosSemidef) (hθ : 0 ≤ θ) (hbound : (θ • (1 : Homogenization.Mat d) - A).PosSemidef) :
    Matrix.trace (A * A) ≤ (d : ℝ) * θ ^ 2 := by
  have hprod := frozenVar_trace_mul_nonneg hA hbound
  have htr := hbound.trace_nonneg
  simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub,
    Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul] at hprod htr
  have hmul := mul_nonneg hθ htr
  nlinarith only [hprod, hmul]

/-- Inverse order forces the trace product to be at least the dimension. -/
theorem frozenVar_dimension_le_trace_mul {A B : Homogenization.Mat d}
    (hA : A.PosDef) (hBA : (B - A⁻¹).PosSemidef) :
    (d : ℝ) ≤ Matrix.trace (A * B) := by
  have h := frozenVar_trace_mul_nonneg hA.posSemidef hBA
  have hu : IsUnit A.det := by
    simpa only [Matrix.isUnit_iff_isUnit_det] using hA.isUnit
  rw [Matrix.mul_sub, Matrix.mul_nonsing_inv A hu, Matrix.trace_sub,
    Matrix.trace_one, Fintype.card_fin] at h
  exact sub_nonneg.mp h

/-- Scalar centering expands using only the trace and Frobenius square. -/
theorem frozenVar_frobSq_sub_scalar (A : Homogenization.Mat d) (c : ℝ) :
    frobSq (A - c • (1 : Homogenization.Mat d)) =
      frobSq A - 2 * c * Matrix.trace A + (d : ℝ) * c ^ 2 := by
  change Matrix (Fin d) (Fin d) ℝ at A
  simp only [frobSq, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, sub_sq,
    Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_pow, zero_pow two_ne_zero,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Matrix.trace, Matrix.diag,
    ← Finset.sum_mul]
  rw [← Finset.mul_sum]
  ring

/-- The trace inequality underlying V1 before taking expectations. -/
theorem frozenVar_pair_frobSq_le {X Y : Homogenization.Mat d}
    (hX : Xᵀ = X) (hY : Yᵀ = Y) (hXY : (d : ℝ) ≤ Matrix.trace (X * Y)) :
    frobSq (X - 1) + frobSq (Y - 1) ≤
      4 * Matrix.trace (((1 / 2 : ℝ) • (X + Y) - 1) *
        ((1 / 2 : ℝ) • (X + Y) - 1)) +
      4 * Matrix.trace ((1 / 2 : ℝ) • (X + Y) - 1) := by
  have hid : 4 * Matrix.trace (((1 / 2 : ℝ) • (X + Y) - 1) *
        ((1 / 2 : ℝ) • (X + Y) - 1)) +
      4 * Matrix.trace ((1 / 2 : ℝ) • (X + Y) - 1) -
      (frobSq (X - 1) + frobSq (Y - 1)) =
      2 * (Matrix.trace (X * Y) - (d : ℝ)) := by
    rw [frozenVar_frobSq_eq_trace, frozenVar_frobSq_eq_trace]
    simp only [Matrix.transpose_sub, Matrix.transpose_one, hX, hY,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
      Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one,
      Fintype.card_fin, smul_eq_mul]
    rw [Matrix.trace_mul_comm Y X]
    ring
  linarith only [hid, hXY]

/-- The Frobenius square loses only one dimension against the operator norm. -/
theorem frozenVar_frobSq_le_dim_opNorm_sq (A : Homogenization.Mat d) :
    frobSq A ≤ (d : ℝ) * Homogenization.Book.Ch02.matrixOperatorNorm A ^ 2 := by
  have hcol (j : Fin d) :
      (∑ i, A i j ^ 2) ≤ Homogenization.Book.Ch02.matrixOperatorNorm A ^ 2 := by
    have h := Homogenization.Book.Ch02.vecNormSq_matVecMul_le_matrixOperatorNorm_sq_mul_vecNormSq
      A (Pi.single j 1)
    simpa [vecNormSq, vecDot, matVecMul, Pi.single_apply, pow_two] using h
  calc
    frobSq A = ∑ j, ∑ i, A i j ^ 2 := Finset.sum_comm
    _ ≤ ∑ _j : Fin d, Homogenization.Book.Ch02.matrixOperatorNorm A ^ 2 :=
      Finset.sum_le_sum fun j _ => hcol j
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end GMCExplicitDelta.Assembly
