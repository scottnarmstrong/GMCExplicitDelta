module

public import GMCExplicitDelta.Averaging.MatrixAverageColors

/-! # Deterministic and norm consequences used by native caps -/

@[expose] public section

open MeasureTheory Matrix
open scoped BigOperators ENNReal Matrix.Norms.L2Operator
open GMCExplicitDelta.Insertion

namespace GMCExplicitDelta.Averaging

/-- A PSD matrix dominated on unit probes by `F I + H` has norm at most `F + ‖H‖`. -/
theorem psd_opNorm_le_constant_add {d : ℕ} {A H : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.PosSemidef) {F : ℝ} (hF : 0 ≤ F)
    (h : ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 →
      sphereQuadratic A u ≤ F + sphereQuadratic H u) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ ≤ F + ‖Matrix.toEuclideanCLM (𝕜 := ℝ) H‖ := by
  have hsym : (Matrix.toEuclideanCLM (𝕜 := ℝ) A).toLinearMap.IsSymmetric := by
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr hA.1
  apply opNorm_le_of_eigenbasis_bound _ hsym hA.1.eigenvectorBasis hA.1.eigenvalues
    (matrix_eigenbasis_apply hA.1) (add_nonneg hF (norm_nonneg _))
  intro i
  have hu := hA.1.eigenvectorBasis.orthonormal.norm_eq_one i
  have he : sphereQuadratic A (hA.1.eigenvectorBasis i) = hA.1.eigenvalues i := by
    simp only [sphereQuadratic, matrix_eigenbasis_apply hA.1, inner_smul_right,
      real_inner_self_eq_norm_sq, hu, one_pow, mul_one]
  have hpos : 0 ≤ hA.1.eigenvalues i := by
    rw [← he]
    exact sphereQuadratic_nonneg hA _
  rw [abs_of_nonneg hpos, ← he]
  apply (h _ hu).trans
  apply add_le_add le_rfl
  have hb := abs_sphereQuadratic_le H (hA.1.eigenvectorBasis i)
  rw [hu, one_pow, mul_one] at hb
  exact (le_abs_self _).trans hb

/-- After a matrix averaging estimate, only scalar norm inequalities remain in A6.
The two minima retain both the induction cap and the improved fluctuation estimate. -/
theorem matrix_average_caps {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {d : ℕ} {A H : Ω → Matrix (Fin d) (Fin d) ℝ}
    (hA : ∀ ω, (A ω).PosSemidef) (hmA : MemLp A 32 μ) (hmH : MemLp H 32 μ)
    {F D K : ℝ} (hF : 0 ≤ F)
    (hprobe : ∀ ω u, ‖u‖ = 1 → sphereQuadratic (A ω) u ≤ F + sphereQuadratic (H ω) u)
    (hCrude : lpNorm A 32 μ ≤ D) (hFluct : lpNorm H 32 μ ≤ K) :
    lpNorm A 32 μ ≤ min D (F + K) ∧
      lpNorm (fun ω => max 0 (‖Matrix.toEuclideanCLM (𝕜 := ℝ) (A ω)‖ - F)) 32 μ ≤ min D K := by
  simp only [← Matrix.cstar_norm_def]
  have hb ω : ‖A ω‖ ≤ F + ‖H ω‖ := by
    simpa only [Matrix.cstar_norm_def] using psd_opNorm_le_constant_add (hA ω) hF (hprobe ω)
  have hsum : MemLp (fun ω => F + ‖H ω‖) 32 μ := (memLp_const F).add hmH.norm
  have hnorm : lpNorm A 32 μ ≤ F + lpNorm H 32 μ := by
    apply (lpNorm_mono_real hsum hb).trans
    have ht := lpNorm_add_le (memLp_const (μ := μ) (p := (32 : ℝ≥0∞)) F) (g := fun ω => ‖H ω‖)
      (by norm_num)
    simpa only [lpNorm_const' (by norm_num : (32 : ℝ≥0∞) ≠ 0) (by norm_num),
      probReal_univ, Real.one_rpow, mul_one, Real.norm_eq_abs,
      abs_of_nonneg hF, lpNorm_norm hmH.aestronglyMeasurable, Pi.add_def] using ht
  constructor
  · exact le_min hCrude (hnorm.trans (add_le_add le_rfl hFluct))
  · apply le_min
    · apply (lpNorm_mono_real hmA.norm (fun ω => ?_)).trans
        (by simpa only [lpNorm_norm hmA.aestronglyMeasurable] using hCrude)
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
      exact max_le (norm_nonneg _) (sub_le_self _ hF)
    · apply (lpNorm_mono_real hmH.norm (fun ω => ?_)).trans
        (by simpa only [lpNorm_norm hmH.aestronglyMeasurable] using hFluct)
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
      exact max_le (norm_nonneg _) (by linarith only [hb ω])

end GMCExplicitDelta.Averaging
