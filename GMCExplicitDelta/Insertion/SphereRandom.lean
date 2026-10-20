module

public import GMCExplicitDelta.Insertion.SpherePSD
public import GMCExplicitDelta.Insertion.SphereRadial
public import GMCExplicitDelta.Insertion.SphereConstants

/-! # The random PSD sphere inequality, by Gaussian averaging and Fubini -/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Metric Set
open scoped Nat NNReal ENNReal RealInnerProductSpace BigOperators

namespace GMCExplicitDelta.Insertion

/-- The supremum of directional p-th moments on the Euclidean unit sphere. -/
noncomputable def sphereDirectionalMoment {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (μ : Measure Ω) (N : Ω → Matrix (Fin d) (Fin d) ℝ) (p : ℕ) : ℝ :=
  sSup ((fun e : EuclideanSpace ℝ (Fin d) => ∫ ω, sphereQuadratic (N ω) e ^ p ∂μ) ''
    sphere 0 1)

theorem sphereQuadratic_smul {d : ℕ} (N : Matrix (Fin d) (Fin d) ℝ)
    (c : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    sphereQuadratic N (c • x) = c ^ 2 * sphereQuadratic N x := by
  simp only [sphereQuadratic, map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

theorem norm_sphereQuadratic_pow_le {d : ℕ} (N : Matrix (Fin d) (Fin d) ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (p : ℕ) :
    ‖sphereQuadratic N x ^ p‖ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) N‖ ^ p * ‖x‖ ^ (2 * p) := by
  simpa only [Real.norm_eq_abs, abs_pow, mul_pow, ← pow_mul] using
    pow_le_pow_left₀ (abs_nonneg (sphereQuadratic N x)) (abs_sphereQuadratic_le N x) p

theorem integrable_random_sphereQuadratic_pow {Ω : Type*} [MeasurableSpace Ω]
    {d p : ℕ} {μ : Measure Ω} {N : Ω → Matrix (Fin d) (Fin d) ℝ}
    (hN : Measurable N) (hm : Integrable (fun ω => ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (N ω)‖ ^ p) μ)
    (x : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun ω => sphereQuadratic (N ω) x ^ p) μ := by
  refine (hm.mul_const (‖x‖ ^ (2 * p))).mono' ?_ ?_
  · exact (((continuous_sphereQuadratic (d := d)).measurable.comp (hN.prodMk measurable_const)).pow_const p).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun ω => norm_sphereQuadratic_pow_le (N ω) x p

theorem integrable_joint_sphereQuadratic_pow {Ω : Type*} [MeasurableSpace Ω]
    {d p : ℕ} {μ : Measure Ω} [SFinite μ] {N : Ω → Matrix (Fin d) (Fin d) ℝ}
    (hN : Measurable N) (hm : Integrable (fun ω => ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (N ω)‖ ^ p) μ) :
    Integrable (fun z : Ω × EuclideanSpace ℝ (Fin d) => sphereQuadratic (N z.1) z.2 ^ p)
      (μ.prod (stdGaussian (EuclideanSpace ℝ (Fin d)))) := by
  have hi := (IsGaussian.memLp_id (stdGaussian (EuclideanSpace ℝ (Fin d)))
    ((2 * p : ℕ) : ℝ≥0∞) (ENNReal.natCast_ne_top _)).integrable_norm_pow' (p := 2 * p)
  refine (hm.mul_prod hi).mono' ?_ ?_
  · exact (((continuous_sphereQuadratic (d := d)).measurable.comp
      ((hN.comp measurable_fst).prodMk measurable_snd)).pow_const p).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun z => norm_sphereQuadratic_pow_le (N z.1) z.2 p

theorem sphereDirectionalMoment_bddAbove {Ω : Type*} [MeasurableSpace Ω]
    {d p : ℕ} {μ : Measure Ω} {N : Ω → Matrix (Fin d) (Fin d) ℝ}
    (hN : Measurable N) (hm : Integrable (fun ω => ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (N ω)‖ ^ p) μ) :
    BddAbove ((fun e : EuclideanSpace ℝ (Fin d) => ∫ ω, sphereQuadratic (N ω) e ^ p ∂μ) ''
      sphere 0 1) := by
  refine ⟨∫ ω, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (N ω)‖ ^ p ∂μ, ?_⟩
  rintro _ ⟨e, he, rfl⟩
  apply integral_mono (integrable_random_sphereQuadratic_pow hN hm e) hm
  intro ω
  have he' : ‖e‖ = 1 := mem_sphere_zero_iff_norm.mp he
  exact (le_abs_self _).trans (by
    simpa only [Real.norm_eq_abs, he', one_pow, mul_one] using
      (norm_sphereQuadratic_pow_le (N ω) e p))

theorem integral_random_sphereQuadratic_pow_le {Ω : Type*} [MeasurableSpace Ω]
    {d p : ℕ} {μ : Measure Ω} {N : Ω → Matrix (Fin d) (Fin d) ℝ}
    (hN : Measurable N) (hm : Integrable (fun ω => ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (N ω)‖ ^ p) μ)
    (hp : 1 ≤ p) (g : EuclideanSpace ℝ (Fin d)) :
    (∫ ω, sphereQuadratic (N ω) g ^ p ∂μ) ≤
      ‖g‖ ^ (2 * p) * sphereDirectionalMoment μ N p := by
  by_cases hg : g = 0
  · simp only [hg, sphereQuadratic, map_zero, inner_zero_left, norm_zero,
      zero_pow (by omega : p ≠ 0), zero_pow (by omega : 2 * p ≠ 0), integral_zero, zero_mul, le_refl]
  · let u := ‖g‖⁻¹ • g
    have hu : ‖u‖ = 1 := by
      simp only [u, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hg)]
    have hgu : g = ‖g‖ • u := by
      simp only [u, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hg), one_smul]
    have he : (∫ ω, sphereQuadratic (N ω) u ^ p ∂μ) ≤ sphereDirectionalMoment μ N p :=
      le_csSup (sphereDirectionalMoment_bddAbove hN hm) ⟨u, mem_sphere_zero_iff_norm.mpr hu, rfl⟩
    calc
      _ = ‖g‖ ^ (2 * p) * ∫ ω, sphereQuadratic (N ω) u ^ p ∂μ := by
        have heq : (fun ω => sphereQuadratic (N ω) g ^ p) =
            (fun ω => ‖g‖ ^ (2 * p) * sphereQuadratic (N ω) u ^ p) := by
          funext ω
          calc
            _ = sphereQuadratic (N ω) (‖g‖ • u) ^ p := congrArg (fun x => sphereQuadratic (N ω) x ^ p) hgu
            _ = _ := by rw [sphereQuadratic_smul, mul_pow, ← pow_mul]
        rw [heq, integral_const_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left he (pow_nonneg (norm_nonneg _) _)

theorem sphereMomentRatio_mul_doubleFactorial (d p : ℕ) :
    sphereMomentRatio d p * ((2 * p - 1)‼ : ℝ) = radialMoment d p := by
  have hden : (∏ j ∈ Finset.range p, (2 * (j : ℝ) + 1)) = ((2 * p - 1)‼ : ℝ) := by
    rw [← radialMoment_one]
    unfold radialMoment
    apply Finset.prod_congr rfl
    intro j hj
    ring
  unfold sphereMomentRatio radialMoment
  rw [Finset.prod_div_distrib, hden]
  exact div_mul_cancel₀ _ (by exact_mod_cast (Nat.ne_of_gt (Nat.doubleFactorial_pos (2 * p - 1))))

/-- The finite product is exactly the Gaussian radial-to-projection moment ratio. -/
theorem sphereMomentRatio_eq_gaussian_moment_ratio (d p : ℕ) :
    sphereMomentRatio d p =
      (∫ g : EuclideanSpace ℝ (Fin d), ‖g‖ ^ (2 * p)
        ∂stdGaussian (EuclideanSpace ℝ (Fin d))) / ((2 * p - 1)‼ : ℝ) := by
  rw [integral_norm_pow_stdGaussian_even]
  apply (eq_div_iff (by exact_mod_cast Nat.ne_of_gt (Nat.doubleFactorial_pos (2 * p - 1)))).2
  simpa only [radialMoment] using sphereMomentRatio_mul_doubleFactorial d p

/-- C13 in Gaussian form: the top Rayleigh moment is controlled by the largest
expected unit-direction moment, with the exact dimension-dependent coefficient.
The integrability premise uses the Euclidean operator norm of the matrix. -/
theorem integral_sphereTop_pow_le_of_ne_zero {Ω : Type*} [MeasurableSpace Ω]
    {d p : ℕ} [NeZero d] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {N : Ω → Matrix (Fin d) (Fin d) ℝ} (hN : Measurable N)
    (hPSD : ∀ᵐ ω ∂μ, (N ω).PosSemidef)
    (hm : Integrable (fun ω => ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (N ω)‖ ^ p) μ)
    (hp : 1 ≤ p) :
    (∫ ω, sphereTop (N ω) ^ p ∂μ) ≤ sphereMomentRatio d p * sphereDirectionalMoment μ N p := by
  have hiTop : Integrable (fun ω => sphereTop (N ω) ^ p) μ := by
    refine hm.mono' ?_ ?_
    · exact (((continuous_sphereTop d).measurable.comp hN).pow_const p).aestronglyMeasurable
    · filter_upwards [hPSD] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (sphereTop_nonneg hω) p)]
      exact pow_le_pow_left₀ (sphereTop_nonneg hω) (sphereTop_le_opNorm (N ω)) p
  have hiJoint := integrable_joint_sphereQuadratic_pow hN hm
  have hiRad := (IsGaussian.memLp_id (stdGaussian (EuclideanSpace ℝ (Fin d)))
    ((2 * p : ℕ) : ℝ≥0∞) (ENNReal.natCast_ne_top _)).integrable_norm_pow' (p := 2 * p)
  have hlow := integral_mono_ae (hiTop.mul_const ((2 * p - 1)‼ : ℝ))
    hiJoint.integral_prod_left (hPSD.mono fun ω hω =>
      sphereTop_pow_mul_doubleFactorial_le_integral hω p)
  rw [integral_mul_const, integral_integral_swap hiJoint] at hlow
  have hupp := integral_mono hiJoint.integral_prod_right
    (hiRad.mul_const (sphereDirectionalMoment μ N p))
    (integral_random_sphereQuadratic_pow_le hN hm hp)
  simp only [id_eq] at hupp
  rw [integral_mul_const, integral_norm_pow_stdGaussian_even] at hupp
  have hdf : (0 : ℝ) < ((2 * p - 1)‼ : ℝ) := by
    exact_mod_cast Nat.doubleFactorial_pos (2 * p - 1)
  apply le_of_mul_le_mul_right (a := ((2 * p - 1)‼ : ℝ)) ?_ hdf
  calc
    _ ≤ _ := hlow.trans hupp
    _ = (sphereMomentRatio d p * sphereDirectionalMoment μ N p) * ((2 * p - 1)‼ : ℝ) := by
      change radialMoment d p * sphereDirectionalMoment μ N p = _
      rw [← sphereMomentRatio_mul_doubleFactorial]
      ring

@[simp] theorem sphereDirectionalMoment_fin_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (N : Ω → Matrix (Fin 0) (Fin 0) ℝ) (p : ℕ) :
    sphereDirectionalMoment μ N p = 0 := by
  have hs : sphere (0 : EuclideanSpace ℝ (Fin 0)) 1 = ∅ := by
    apply Set.eq_empty_of_forall_notMem
    intro x hx
    have hn := mem_sphere_zero_iff_norm.mp hx
    have hx0 : x = 0 := Subsingleton.elim _ _
    rw [hx0, norm_zero] at hn
    norm_num at hn
  simp only [sphereDirectionalMoment, hs, Set.image_empty, Real.sSup_empty]

/-- The C13 inequality in all dimensions, using the Rayleigh-supremum convention
for the top eigenvalue and the Euclidean operator norm for integrability. -/
theorem integral_sphereTop_pow_le {Ω : Type*} [MeasurableSpace Ω]
    {d p : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {N : Ω → Matrix (Fin d) (Fin d) ℝ} (hN : Measurable N)
    (hPSD : ∀ᵐ ω ∂μ, (N ω).PosSemidef)
    (hm : Integrable (fun ω => ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (N ω)‖ ^ p) μ)
    (hp : 1 ≤ p) :
    (∫ ω, sphereTop (N ω) ^ p ∂μ) ≤ sphereMomentRatio d p * sphereDirectionalMoment μ N p := by
  by_cases hd : d = 0
  · subst d
    simp only [sphereTop_fin_zero, zero_pow (by omega : p ≠ 0), integral_zero,
      sphereDirectionalMoment_fin_zero, mul_zero, le_refl]
  · have : NeZero d := ⟨hd⟩
    exact integral_sphereTop_pow_le_of_ne_zero hN hPSD hm hp

end GMCExplicitDelta.Insertion
