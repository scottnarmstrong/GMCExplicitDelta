module

public import GMCExplicitDelta.Averaging.SignedSphereDiagonal
public import GMCExplicitDelta.Insertion.SpherePSD

/-! # Spectral normalization for the signed-matrix Gaussian norming bound -/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Matrix Set
open scoped BigOperators RealInnerProductSpace
open GMCExplicitDelta.Insertion

namespace GMCExplicitDelta.Averaging

theorem quadratic_eigenbasis_sum {d : ℕ} (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d))) (ell : Fin d → ℝ)
    (he : ∀ i, T (b i) = ell i • b i) (x : Fin d → ℝ) :
    ⟪∑ i, x i • b i, T (∑ i, x i • b i)⟫ = ∑ i, ell i * x i ^ 2 := by
  simp only [map_sum, map_smul, he, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, orthonormal_iff_ite.mp b.orthonormal]
  simp only [mul_ite, mul_one, mul_zero, sum_ite_eq']
  apply sum_congr rfl
  intro i hi
  rw [ite_eq_left hi]
  ring

theorem eigenvalue_abs_le_opNorm {d : ℕ}
    (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d))) (ell : Fin d → ℝ)
    (he : ∀ i, T (b i) = ell i • b i) (i : Fin d) : |ell i| ≤ ‖T‖ := by
  have h := T.le_opNorm (b i)
  simpa only [he, norm_smul, Real.norm_eq_abs, b.orthonormal.norm_eq_one, mul_one] using h

theorem opNorm_le_of_eigenbasis_bound {d : ℕ}
    (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hT : T.toLinearMap.IsSymmetric)
    (b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d))) (ell : Fin d → ℝ)
    (he : ∀ i, T (b i) = ell i • b i) {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ i, |ell i| ≤ M) :
    ‖T‖ ≤ M := by
  have hq (x : EuclideanSpace ℝ (Fin d)) : |⟪x, T x⟫| ≤ M * ‖x‖ ^ 2 := by
    have hx := quadratic_eigenbasis_sum T b ell he (fun i => b.repr x i)
    rw [b.sum_repr] at hx
    rw [hx]
    calc
      _ ≤ ∑ i, |ell i * b.repr x i ^ 2| := abs_sum_le_sum_abs _ _
      _ = ∑ i, |ell i| * b.repr x i ^ 2 := by
        apply sum_congr rfl
        intro i hi
        rw [abs_mul, abs_of_nonneg (sq_nonneg (b.repr x i))]
      _ ≤ ∑ i, M * b.repr x i ^ 2 := sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_right (hbound i) (sq_nonneg _)
      _ = M * ‖x‖ ^ 2 := by
        rw [← mul_sum, ← EuclideanSpace.real_norm_sq_eq, b.repr.norm_map]
  rw [T.norm_eq_iSup_rayleighQuotient hT]
  apply ciSup_le
  intro x
  by_cases hx : x = 0
  · simp only [hx, ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
      map_zero, inner_zero_left, norm_zero,
      zero_pow (by decide : 2 ≠ 0), zero_div, abs_zero]
    exact hM
  · have hn : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
    change |⟪T x, x⟫ / ‖x‖ ^ 2| ≤ M
    rw [abs_div, abs_of_pos hn, real_inner_comm]
    exact (div_le_iff₀ hn).2 (hq x)

theorem exists_norm_eigenvalue {d : ℕ} [NeZero d]
    (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hT : T.toLinearMap.IsSymmetric)
    (b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d))) (ell : Fin d → ℝ)
    (he : ∀ i, T (b i) = ell i • b i) : ∃ i, |ell i| = ‖T‖ := by
  obtain ⟨i, hi, hmax⟩ := (univ : Finset (Fin d)).exists_max_image (fun i => |ell i|) univ_nonempty
  refine ⟨i, le_antisymm (eigenvalue_abs_le_opNorm T b ell he i) ?_⟩
  exact opNorm_le_of_eigenbasis_bound T hT b ell he (abs_nonneg _) (fun j => hmax j (mem_univ _))

/-- The matrix spectral theorem supplies an orthonormal basis with the required operator action. -/
theorem matrix_eigenbasis_apply {d : ℕ} {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.IsHermitian)
    (i : Fin d) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) H (hH.eigenvectorBasis i) =
      hH.eigenvalues i • hH.eigenvectorBasis i := by
  apply WithLp.ofLp_injective 2
  simpa only [Matrix.ofLp_toEuclideanCLM, WithLp.ofLp_smul] using hH.mulVec_eigenvectorBasis i

/-- The Gaussian law written in any orthonormal eigenbasis. -/
theorem integral_quadratic_eigenbasis {d : ℕ} (H : Matrix (Fin d) (Fin d) ℝ)
    (b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d))) (ell : Fin d → ℝ)
    (he : ∀ i, Matrix.toEuclideanCLM (𝕜 := ℝ) H (b i) = ell i • b i) :
    (∫ g, sphereQuadratic H g ^ 32 ∂stdGaussian (EuclideanSpace ℝ (Fin d))) =
      ∫ x : Fin d → ℝ, (∑ i, ell i * x i ^ 2) ^ 32 ∂gaussianPi d := by
  have hc : Continuous (fun x : Fin d → ℝ => ∑ i, x i • b i) := by fun_prop
  unfold gaussianPi
  rw [stdGaussian_eq_map_pi_orthonormalBasis b, integral_map hc.measurable.aemeasurable (by
    exact (continuous_sphereQuadratic_fixed H).pow 32 |>.aestronglyMeasurable)]
  apply integral_congr_ae
  filter_upwards [] with x
  exact congrArg (fun t : ℝ => t ^ 32)
    (quadratic_eigenbasis_sum (Matrix.toEuclideanCLM (𝕜 := ℝ) H) b ell he x)

/-- Pull out the distinguished eigenvalue, after splitting the first Gaussian coordinate. -/
theorem integral_diagonal_normalize {n : ℕ} (ell : Fin (n + 1) → ℝ) {c : ℝ}
    (hc : c ≠ 0) (he : ell 0 = c) :
    (∫ x : Fin (n + 1) → ℝ, (∑ i, ell i * x i ^ 2) ^ 32 ∂gaussianPi (n + 1)) =
      c ^ 32 * signedDiagonalMoment (fun i : Fin n => ell i.succ / c) := by
  unfold gaussianPi
  rw [← ((measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => gaussianReal 0 1) 0).symm).integral_comp']
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.sum_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
    Fin.zero_succAbove, cast_eq, Fin.cons_zero, he]
  have hf (z : ℝ × (Fin n → ℝ)) :
      c * z.1 ^ 2 + ∑ i, ell i.succ * z.2 i ^ 2 =
        c * signedDiagonalForm (fun i : Fin n => ell i.succ / c) z := by
    unfold signedDiagonalForm
    rw [mul_add, mul_sum]
    congr 1
    apply sum_congr rfl
    intro i hi
    field_simp
  simp_rw [hf, mul_pow]
  rw [integral_const_mul]
  rfl

end GMCExplicitDelta.Averaging
