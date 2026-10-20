module

public import GMCExplicitDelta.Averaging.SignedSphereNorming
public import GMCExplicitDelta.Insertion.SphereRandom

/-! # The random signed-matrix norming inequality, by Gaussian Fubini -/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Metric Set
open scoped BigOperators ENNReal
open GMCExplicitDelta.Insertion

namespace GMCExplicitDelta.Averaging

/-- For order 32 the directional moment is the absolute quadratic-form moment. -/
theorem sphereDirectionalMoment_signed {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) (H : Ω → Matrix (Fin d) (Fin d) ℝ) :
    sphereDirectionalMoment μ H 32 =
      sSup ((fun u : EuclideanSpace ℝ (Fin d) => ∫ ω, |sphereQuadratic (H ω) u| ^ 32 ∂μ) ''
        sphere 0 1) := by
  simp only [(by decide : Even 32).pow_abs, sphereDirectionalMoment]

/-- Random A4 in the Contract normalization, with the Euclidean operator norm. -/
theorem integral_signed_opNorm_pow_le {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (hd : 2 ≤ d) {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : Ω → Matrix (Fin d) (Fin d) ℝ} (hH : Measurable H)
    (hSymm : ∀ᵐ ω ∂μ, (H ω).IsHermitian)
    (hm : Integrable (fun ω => ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (H ω)‖ ^ 32) μ)
    (hL : 0 < (Contract.sphereLower d : ℝ)) :
    (∫ ω, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (H ω)‖ ^ 32 ∂μ) ≤
      (Contract.sphereLower d : ℝ)⁻¹ * sphereDirectionalMoment μ H 32 := by
  have hiJoint := integrable_joint_sphereQuadratic_pow hH hm
  have hiRad := (IsGaussian.memLp_id (stdGaussian (EuclideanSpace ℝ (Fin d)))
    (64 : ℝ≥0∞) (by norm_num)).integrable_norm_pow' (p := 64)
  have hR : 0 < radialMoment d 32 := radialMoment_pos (by exact_mod_cast (show 0 < d by omega)) 32
  have hlow := integral_mono_ae
    (hm.mul_const ((Contract.sphereLower d : ℝ) * radialMoment d 32))
    hiJoint.integral_prod_left (hSymm.mono fun ω hω => by
      have h := signed_sphere_gaussian_lower hd hω
      simp only [(by decide : Even 32).pow_abs] at h
      rw [integral_norm_pow_stdGaussian_even d 32] at h
      simpa only [radialMoment, mul_assoc] using h)
  rw [integral_mul_const, integral_integral_swap hiJoint] at hlow
  have hupp := integral_mono hiJoint.integral_prod_right
    (hiRad.mul_const (sphereDirectionalMoment μ H 32))
    (integral_random_sphereQuadratic_pow_le hH hm (by norm_num : 1 ≤ 32))
  simp only [id_eq] at hupp
  rw [integral_mul_const, integral_norm_pow_stdGaussian_even d 32] at hupp
  have hmul : (∫ ω, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (H ω)‖ ^ 32 ∂μ) *
      (Contract.sphereLower d : ℝ) ≤ sphereDirectionalMoment μ H 32 := by
    apply le_of_mul_le_mul_right (a := radialMoment d 32) ?_ hR
    calc
      _ ≤ _ := by simpa only [mul_assoc] using hlow.trans hupp
      _ = _ := by change radialMoment d 32 * sphereDirectionalMoment μ H 32 = _; ring
  calc
    _ ≤ sphereDirectionalMoment μ H 32 / (Contract.sphereLower d : ℝ) := (le_div_iff₀ hL).2 hmul
    _ = _ := by ring

/-- The rational Contract certificate upgrades the sharp inverse lower bound to sigmaNorm^32. -/
theorem integral_signed_opNorm_pow_le_sigmaNorm {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (hd : 2 ≤ d) {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : Ω → Matrix (Fin d) (Fin d) ℝ} (hH : Measurable H)
    (hSymm : ∀ᵐ ω ∂μ, (H ω).IsHermitian)
    (hm : Integrable (fun ω => ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (H ω)‖ ^ 32) μ)
    (hL : 0 < Contract.sphereLower d)
    (hcert : 1 < Contract.sigmaNorm d ^ 32 * Contract.sphereLower d) :
    (∫ ω, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (H ω)‖ ^ 32 ∂μ) ≤
      (Contract.sigmaNorm d : ℝ) ^ 32 * sphereDirectionalMoment μ H 32 := by
  have hL' : 0 < (Contract.sphereLower d : ℝ) := by exact_mod_cast hL
  have hcert' : (1 : ℝ) ≤ (Contract.sigmaNorm d : ℝ) ^ 32 * (Contract.sphereLower d : ℝ) := by
    exact_mod_cast hcert.le
  have hc : (Contract.sphereLower d : ℝ)⁻¹ ≤ (Contract.sigmaNorm d : ℝ) ^ 32 := by
    rw [← one_div]
    exact (div_le_iff₀ hL').2 hcert'
  have : NeZero d := ⟨by omega⟩
  obtain ⟨u, hu⟩ := (NormedSpace.sphere_nonempty (E := EuclideanSpace ℝ (Fin d))).mpr
    (by norm_num : (0 : ℝ) ≤ 1)
  have hnonneg : 0 ≤ ∫ ω, sphereQuadratic (H ω) u ^ 32 ∂μ :=
    integral_nonneg fun _ => by positivity
  have hdir : 0 ≤ sphereDirectionalMoment μ H 32 :=
    hnonneg.trans (le_csSup (sphereDirectionalMoment_bddAbove hH hm) ⟨u, hu, rfl⟩)
  exact (integral_signed_opNorm_pow_le hd hH hSymm hm hL').trans
    (mul_le_mul_of_nonneg_right hc hdir)

end GMCExplicitDelta.Averaging
