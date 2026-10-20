module

public import GMCExplicitDelta.Averaging.MatrixAverage

/-! # The bound for one independent class -/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal Matrix.Norms.L2Operator
open GMCExplicitDelta.Insertion

namespace GMCExplicitDelta.Averaging

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {d n : ℕ} {M : Fin n → Ω → Matrix (Fin d) (Fin d) ℝ} {F D T : ℝ}

omit [IsProbabilityMeasure μ] in
/-- The scalar A3 hypotheses follow from PSD matrix moment and mean bounds. -/
theorem matrixProbe_avgHyp (hF : 0 < F) (hD : 0 < D)
    (hM : ∀ i, Measurable (M i)) (hm : ∀ i, MemLp (M i) 32 μ)
    (hPSD : ∀ i ω, (M i ω).PosSemidef) (hind : iIndepFun M μ)
    (hmean : ∀ i u, ‖u‖ = 1 → ∫ ω, sphereQuadratic (M i ω) u ∂μ ≤ F)
    (hmoment : ∀ i, ∫ ω, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (M i ω)‖ ^ 32 ∂μ ≤ D ^ 32)
    (hT : (min (F / D) 1) ^ ((32 : ℝ) / 31) ≤ T)
    (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) :
    AvgHyp μ (fun i ω => sphereQuadratic (M i ω) u) 32 F D T := by
  have hq i : Measurable (fun ω => sphereQuadratic (M i ω) u) :=
    (matrixProbe u).continuous.measurable.comp (hM i)
  have hi i : Integrable (fun ω => sphereQuadratic (M i ω) u ^ 32) μ := by
    simpa only [(by decide : Even 32).pow_abs, Real.norm_eq_abs,
      Function.comp_apply, matrixProbe_apply] using
      ((matrixProbe u).comp_memLp' (hm i)).integrable_norm_pow (by norm_num : 32 ≠ 0)
  refine ⟨by norm_num, hF, hD, hind.comp (fun _ => matrixProbe u)
    (fun _ => (matrixProbe u).continuous.measurable), hq,
    fun i ω => sphereQuadratic_nonneg (hPSD i ω) u, hi, fun i => hmean i u hu, ?_, ?_⟩
  · intro i
    refine (integral_mono (hi i) ((hm i).integrable_norm_pow (by norm_num)) fun ω => ?_).trans
      (hmoment i)
    have hb := abs_sphereQuadratic_le (M i ω) u
    rw [hu, one_pow, mul_one] at hb
    simpa only [(by decide : Even 32).pow_abs, Matrix.cstar_norm_def] using
      pow_le_pow_left₀ (abs_nonneg _) hb 32
  · norm_num only [show (32 : ℝ) - 1 = 31 by norm_num]
    exact hT

/-- **A5, one class**, in moment form. -/
theorem integral_centeredMatrixAverage_pow_le (hd : 2 ≤ d) (hn : 0 < n)
    (hF : 0 < F) (hD : 0 < D)
    (hM : ∀ i, Measurable (M i)) (hm : ∀ i, MemLp (M i) 32 μ)
    (hPSD : ∀ i ω, (M i ω).PosSemidef) (hind : iIndepFun M μ)
    (hmean : ∀ i u, ‖u‖ = 1 → ∫ ω, sphereQuadratic (M i ω) u ∂μ ≤ F)
    (hmoment : ∀ i, ∫ ω, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (M i ω)‖ ^ 32 ∂μ ≤ D ^ 32)
    (hT : (min (F / D) 1) ^ ((32 : ℝ) / 31) ≤ T)
    (hL : 0 < Contract.sphereLower d)
    (hcert : 1 < Contract.sigmaNorm d ^ 32 * Contract.sphereLower d) :
    (∫ ω, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (centeredMatrixAverage μ M ω)‖ ^ 32 ∂μ) ≤
      (Contract.sigmaNorm d : ℝ) ^ 32 * (D ^ 32 * avgBoundPow 32 n T) := by
  have hH : Measurable (centeredMatrixAverage μ M) := by
    unfold centeredMatrixAverage
    exact (Finset.measurable_sum _ (fun i _ => (hM i).sub_const _)).const_smul ((n : ℝ)⁻¹)
  have hi := (memLp_centeredMatrixAverage hm).integrable_norm_pow (by norm_num : 32 ≠ 0)
  have hs := integral_signed_opNorm_pow_le_sigmaNorm hd hH
    (Filter.Eventually.of_forall (centeredMatrixAverage_isHermitian hm (fun i ω => (hPSD i ω).1)))
    hi hL hcert
  apply hs.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply csSup_le
  · have : NeZero d := ⟨by omega⟩
    obtain ⟨u, hu⟩ := (NormedSpace.sphere_nonempty (E := EuclideanSpace ℝ (Fin d))).mpr
      (by norm_num : (0 : ℝ) ≤ 1)
    exact ⟨_, ⟨u, hu, rfl⟩⟩
  · rintro _ ⟨u, hu, rfl⟩
    have hu' : ‖u‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hu
    have h := mean_sensitive_average
      (matrixProbe_avgHyp hF hD hM hm hPSD hind hmean hmoment hT u hu') hn
    simpa only [matrixProbe_centeredMatrixAverage hm] using h

/-- **A5, one class**, in the Euclidean operator L32 norm. -/
theorem lpNorm_centeredMatrixAverage_le (hd : 2 ≤ d) (hn : 0 < n)
    (hF : 0 < F) (hD : 0 < D)
    (hM : ∀ i, Measurable (M i)) (hm : ∀ i, MemLp (M i) 32 μ)
    (hPSD : ∀ i ω, (M i ω).PosSemidef) (hind : iIndepFun M μ)
    (hmean : ∀ i u, ‖u‖ = 1 → ∫ ω, sphereQuadratic (M i ω) u ∂μ ≤ F)
    (hmoment : ∀ i, ∫ ω, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (M i ω)‖ ^ 32 ∂μ ≤ D ^ 32)
    (hT : (min (F / D) 1) ^ ((32 : ℝ) / 31) ≤ T)
    (hL : 0 < Contract.sphereLower d)
    (hcert : 1 < Contract.sigmaNorm d ^ 32 * Contract.sphereLower d) :
    lpNorm (centeredMatrixAverage μ M) 32 μ ≤
      (Contract.sigmaNorm d : ℝ) * D * avgBound 32 n T := by
  have h := integral_centeredMatrixAverage_pow_le hd hn hF hD hM hm hPSD hind hmean
    hmoment hT hL hcert
  have hT0 : 0 ≤ T := (Real.rpow_nonneg (le_min (div_nonneg hF.le hD.le) zero_le_one) _).trans hT
  have hB := avgBoundPow_nonneg (p := 32) (Nat.cast_nonneg n) hT0
  have hs : 0 ≤ (Contract.sigmaNorm d : ℝ) := by
    unfold Contract.sigmaNorm
    split_ifs <;> norm_num
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
    (memLp_centeredMatrixAverage hm).aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, Real.rpow_ofNat, Matrix.cstar_norm_def]
  refine (Real.rpow_le_rpow (integral_nonneg fun _ => by positivity) h (by norm_num : 0 ≤ (32 : ℝ)⁻¹)).trans
    (le_of_eq ?_)
  rw [Real.mul_rpow (pow_nonneg hs _) (mul_nonneg (pow_nonneg hD.le _) hB),
    Real.mul_rpow (pow_nonneg hD.le _) hB]
  simp only [← Real.rpow_natCast, ← Real.rpow_mul hs, ← Real.rpow_mul hD.le]
  norm_num [avgBound, mul_assoc]

end GMCExplicitDelta.Averaging
