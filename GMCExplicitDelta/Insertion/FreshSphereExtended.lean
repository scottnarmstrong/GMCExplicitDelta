module

public import GMCExplicitDelta.Insertion.SphereRandom

/-! # C13 for nonnegative moments without a prior matrix-norm moment assumption -/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Metric
open scoped ENNReal Nat

namespace GMCExplicitDelta.Insertion

/-- Unit-direction moment bounds control every Gaussian direction by homogeneity. -/
theorem lintegral_sphereQuadratic_pow_le_radial {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {d p : ℕ} {N : Ω → Matrix (Fin d) (Fin d) ℝ}
    (hN : Measurable N) (hp : 1 ≤ p) {C : ℝ≥0∞}
    (hdir : ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 →
      (∫⁻ ω, ENNReal.ofReal (sphereQuadratic (N ω) u ^ p) ∂μ) ≤ C)
    (g : EuclideanSpace ℝ (Fin d)) :
    (∫⁻ ω, ENNReal.ofReal (sphereQuadratic (N ω) g ^ p) ∂μ) ≤
      ENNReal.ofReal (‖g‖ ^ (2 * p)) * C := by
  by_cases hg : g = 0
  · subst g
    simp only [sphereQuadratic, map_zero, inner_zero_left, zero_pow (by omega : p ≠ 0),
      ENNReal.ofReal_zero, lintegral_zero, norm_zero,
      zero_pow (by omega : 2 * p ≠ 0), zero_mul, le_refl]
  · let u := ‖g‖⁻¹ • g
    have hu : ‖u‖ = 1 := by
      simp only [u, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hg)]
    have hgu : g = ‖g‖ • u := by
      simp only [u, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hg), one_smul]
    have hm : Measurable (fun ω => ENNReal.ofReal (sphereQuadratic (N ω) u ^ p)) :=
      (((continuous_sphereQuadratic (d := d)).measurable.comp
        (hN.prodMk measurable_const)).pow_const p).ennreal_ofReal
    have heq (ω : Ω) : ENNReal.ofReal (sphereQuadratic (N ω) g ^ p) =
        ENNReal.ofReal (‖g‖ ^ (2 * p)) * ENNReal.ofReal (sphereQuadratic (N ω) u ^ p) := by
      have hh : sphereQuadratic (N ω) g ^ p = ‖g‖ ^ (2 * p) * sphereQuadratic (N ω) u ^ p := by
        calc
          _ = sphereQuadratic (N ω) (‖g‖ • u) ^ p := congrArg (fun x => sphereQuadratic (N ω) x ^ p) hgu
          _ = _ := by rw [sphereQuadratic_smul, mul_pow, ← pow_mul]
      rw [hh, ENNReal.ofReal_mul (pow_nonneg (norm_nonneg _) _)]
    calc
      _ = ∫⁻ ω, ENNReal.ofReal (‖g‖ ^ (2 * p)) *
          ENNReal.ofReal (sphereQuadratic (N ω) u ^ p) ∂μ := lintegral_congr heq
      _ = _ := lintegral_const_mul _ hm
      _ ≤ _ := mul_le_mul_right (hdir u hu) _

/-- C13 in the nonnegative-integral setting. Directional bounds supply finiteness
at the end, so no matrix-norm moment is assumed in advance. -/
theorem lintegral_sphereTop_pow_le_of_directional {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [SFinite μ] {d p : ℕ} [NeZero d]
    {N : Ω → Matrix (Fin d) (Fin d) ℝ} (hN : Measurable N)
    (hPSD : ∀ ω, (N ω).PosSemidef) (hp : 1 ≤ p) {C : ℝ≥0∞}
    (hdir : ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 →
      (∫⁻ ω, ENNReal.ofReal (sphereQuadratic (N ω) u ^ p) ∂μ) ≤ C) :
    (∫⁻ ω, ENNReal.ofReal (sphereTop (N ω) ^ p) ∂μ) ≤
      ENNReal.ofReal (sphereMomentRatio d p) * C := by
  have ht : Measurable (fun ω => ENNReal.ofReal (sphereTop (N ω) ^ p)) :=
    (((continuous_sphereTop d).measurable.comp hN).pow_const p).ennreal_ofReal
  have hj : Measurable (fun z : Ω × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal (sphereQuadratic (N z.1) z.2 ^ p)) :=
    (((continuous_sphereQuadratic (d := d)).measurable.comp
      ((hN.comp measurable_fst).prodMk measurable_snd)).pow_const p).ennreal_ofReal
  have hlow (ω : Ω) : ENNReal.ofReal (sphereTop (N ω) ^ p) * ((2 * p - 1)‼ : ℝ≥0∞) ≤
      ∫⁻ g, ENNReal.ofReal (sphereQuadratic (N ω) g ^ p)
        ∂stdGaussian (EuclideanSpace ℝ (Fin d)) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (pow_nonneg (sphereTop_nonneg (hPSD ω)) _),
      ← ofReal_integral_eq_lintegral_ofReal (integrable_sphereQuadratic_pow (N ω) p)
        (Filter.Eventually.of_forall fun g => pow_nonneg (sphereQuadratic_nonneg (hPSD ω) g) p)]
    exact ENNReal.ofReal_le_ofReal (sphereTop_pow_mul_doubleFactorial_le_integral (hPSD ω) p)
  have hrad : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ‖g‖ ^ (2 * p))
      (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    (IsGaussian.memLp_id (stdGaussian (EuclideanSpace ℝ (Fin d)))
      ((2 * p : ℕ) : ℝ≥0∞) (ENNReal.natCast_ne_top _)).integrable_norm_pow' (p := 2 * p)
  have hrm : Measurable (fun g : EuclideanSpace ℝ (Fin d) => ENNReal.ofReal (‖g‖ ^ (2 * p))) :=
    (continuous_norm.pow _).measurable.ennreal_ofReal
  have hupp := lintegral_mono (μ := stdGaussian (EuclideanSpace ℝ (Fin d))) (fun g => lintegral_sphereQuadratic_pow_le_radial hN hp hdir g)
  rw [lintegral_mul_const _ hrm,
    ← ofReal_integral_eq_lintegral_ofReal hrad
      (Filter.Eventually.of_forall fun g => pow_nonneg (norm_nonneg g) (2 * p)),
    integral_norm_pow_stdGaussian_even] at hupp
  have hratio : 0 ≤ sphereMomentRatio d p := by
    unfold sphereMomentRatio
    exact Finset.prod_nonneg fun i _ => div_nonneg (by positivity) (by positivity)
  have hradEq : ENNReal.ofReal (radialMoment d p) =
      ENNReal.ofReal (sphereMomentRatio d p) * ((2 * p - 1)‼ : ℝ≥0∞) := by
    rw [← sphereMomentRatio_mul_doubleFactorial, ENNReal.ofReal_mul hratio, ENNReal.ofReal_natCast]
  have hdf0 : ((2 * p - 1)‼ : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.doubleFactorial_pos (2 * p - 1)).ne'
  apply (ENNReal.mul_le_mul_iff_left hdf0 (ENNReal.natCast_ne_top _)).mp
  calc
    _ = ∫⁻ ω, ENNReal.ofReal (sphereTop (N ω) ^ p) * ((2 * p - 1)‼ : ℝ≥0∞) ∂μ :=
      (lintegral_mul_const _ ht).symm
    _ ≤ ∫⁻ ω, ∫⁻ g, ENNReal.ofReal (sphereQuadratic (N ω) g ^ p)
        ∂stdGaussian (EuclideanSpace ℝ (Fin d)) ∂μ := lintegral_mono hlow
    _ = ∫⁻ g, ∫⁻ ω, ENNReal.ofReal (sphereQuadratic (N ω) g ^ p) ∂μ
        ∂stdGaussian (EuclideanSpace ℝ (Fin d)) := lintegral_lintegral_swap hj.aemeasurable
    _ ≤ _ := hupp
    _ = _ := by
      change ENNReal.ofReal (radialMoment d p) * C = _
      rw [hradEq]
      ring

end GMCExplicitDelta.Insertion
