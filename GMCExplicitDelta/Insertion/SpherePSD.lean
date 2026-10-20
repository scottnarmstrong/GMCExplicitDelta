module

public import GMCExplicitDelta.Insertion.SphereGaussianVector
public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-! # PSD quadratic forms and their Gaussian averages -/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Metric Set
open scoped Nat NNReal ENNReal RealInnerProductSpace

namespace GMCExplicitDelta.Insertion

/-- Quadratic form of a real matrix, with the Euclidean scalar product. -/
noncomputable def sphereQuadratic {d : ℕ} (N : Matrix (Fin d) (Fin d) ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ := ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) N x⟫

/-- The top Rayleigh value, as a supremum on the Euclidean unit sphere. -/
noncomputable def sphereTop {d : ℕ} (N : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  sSup (sphereQuadratic N '' sphere 0 1)

theorem continuous_sphereQuadratic {d : ℕ} :
    Continuous (fun z : Matrix (Fin d) (Fin d) ℝ × EuclideanSpace ℝ (Fin d) =>
      sphereQuadratic z.1 z.2) := by
  unfold sphereQuadratic
  exact continuous_snd.inner Matrix.continuous_uncurry_toEuclideanCLM

theorem continuous_sphereQuadratic_fixed {d : ℕ} (N : Matrix (Fin d) (Fin d) ℝ) :
    Continuous (sphereQuadratic N) := by
  change Continuous (fun x : EuclideanSpace ℝ (Fin d) => ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) N x⟫)
  exact continuous_id.inner (Matrix.toEuclideanCLM (𝕜 := ℝ) N).continuous

theorem continuous_sphereTop (d : ℕ) :
    Continuous (sphereTop : Matrix (Fin d) (Fin d) ℝ → ℝ) := by
  exact (isCompact_sphere (0 : EuclideanSpace ℝ (Fin d)) 1).continuous_sSup
    continuous_sphereQuadratic

theorem sphereQuadratic_nonneg {d : ℕ} {N : Matrix (Fin d) (Fin d) ℝ}
    (hN : N.PosSemidef) (x : EuclideanSpace ℝ (Fin d)) : 0 ≤ sphereQuadratic N x := by
  simpa only [sphereQuadratic, Matrix.inner_toEuclideanCLM, star_trivial] using
    hN.dotProduct_mulVec_nonneg (WithLp.ofLp x)

theorem abs_sphereQuadratic_le {d : ℕ} (N : Matrix (Fin d) (Fin d) ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    |sphereQuadratic N x| ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) N‖ * ‖x‖ ^ 2 := by
  calc
    _ ≤ ‖x‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) N x‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖Matrix.toEuclideanCLM (𝕜 := ℝ) N‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left ((Matrix.toEuclideanCLM (𝕜 := ℝ) N).le_opNorm x) (norm_nonneg x)
    _ = _ := by ring

theorem sphereQuadratic_rank_one_le {d : ℕ} {N : Matrix (Fin d) (Fin d) ℝ}
    (hN : N.PosSemidef) {v : EuclideanSpace ℝ (Fin d)} {ell : ℝ}
    (hv : ‖v‖ = 1) (heig : Matrix.toEuclideanCLM (𝕜 := ℝ) N v = ell • v)
    (x : EuclideanSpace ℝ (Fin d)) :
    ell * ⟪v, x⟫ ^ 2 ≤ sphereQuadratic N x := by
  have hsym : (Matrix.toEuclideanCLM (𝕜 := ℝ) N).toLinearMap.IsSymmetric := by
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr hN.isHermitian
  have hc : ⟪v, Matrix.toEuclideanCLM (𝕜 := ℝ) N x⟫ = ell * ⟪v, x⟫ := by
    calc
      _ = ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) N v, x⟫ := (hsym v x).symm
      _ = _ := by rw [heig, real_inner_smul_left]
  have hp := sphereQuadratic_nonneg hN (x - ⟪v, x⟫ • v)
  simp only [sphereQuadratic, map_sub, map_smul, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, hc, heig, real_inner_comm x v,
    real_inner_self_eq_norm_sq, hv, one_pow, mul_one] at hp
  change ell * ⟪v, x⟫ ^ 2 ≤ ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) N x⟫
  rw [← real_inner_comm v x]
  nlinarith only [hp]

theorem sphereTop_bddAbove {d : ℕ} (N : Matrix (Fin d) (Fin d) ℝ) :
    BddAbove (sphereQuadratic N '' sphere 0 1) := by
  refine ⟨‖Matrix.toEuclideanCLM (𝕜 := ℝ) N‖, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hx' : ‖x‖ = 1 := by simpa only [mem_sphere_zero_iff_norm] using hx
  exact (le_abs_self _).trans (by simpa only [hx', one_pow, mul_one] using abs_sphereQuadratic_le N x)

theorem sphereTop_le_opNorm {d : ℕ} (N : Matrix (Fin d) (Fin d) ℝ) :
    sphereTop N ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) N‖ := by
  by_cases hs : (sphere (0 : EuclideanSpace ℝ (Fin d)) 1).Nonempty
  · apply csSup_le (hs.image _)
    rintro _ ⟨x, hx, rfl⟩
    have hx' : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
    exact (le_abs_self _).trans (by simpa only [hx', one_pow, mul_one] using abs_sphereQuadratic_le N x)
  · simp only [Set.not_nonempty_iff_eq_empty] at hs
    simp only [sphereTop, hs, Set.image_empty, Real.sSup_empty]
    exact norm_nonneg _

theorem sphereTop_nonneg {d : ℕ} [NeZero d] {N : Matrix (Fin d) (Fin d) ℝ}
    (hN : N.PosSemidef) : 0 ≤ sphereTop N := by
  obtain ⟨v, hv⟩ := (NormedSpace.sphere_nonempty (E := EuclideanSpace ℝ (Fin d))).mpr
    (by norm_num : (0 : ℝ) ≤ 1)
  exact (sphereQuadratic_nonneg hN v).trans (le_csSup (sphereTop_bddAbove N) ⟨v, hv, rfl⟩)

theorem exists_unit_top_eigenvector {d : ℕ} [NeZero d]
    {N : Matrix (Fin d) (Fin d) ℝ} (hN : N.PosSemidef) :
    ∃ v : EuclideanSpace ℝ (Fin d), ‖v‖ = 1 ∧
      Matrix.toEuclideanCLM (𝕜 := ℝ) N v = sphereTop N • v := by
  have hcont : Continuous (sphereQuadratic N) :=
    continuous_sphereQuadratic_fixed N
  obtain ⟨v, hv, htop, hmax⟩ :=
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin d)) 1).exists_sSup_image_eq_and_ge
      (NormedSpace.sphere_nonempty.mpr (by norm_num)) hcont.continuousOn
  have hvnorm : ‖v‖ = 1 := by simpa only [mem_sphere_zero_iff_norm] using hv
  have hsym : (Matrix.toEuclideanCLM (𝕜 := ℝ) N).toLinearMap.IsSymmetric := by
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr hN.isHermitian
  have hsa : IsSelfAdjoint (Matrix.toEuclideanCLM (𝕜 := ℝ) N) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hsym
  have hmax' : IsMaxOn (Matrix.toEuclideanCLM (𝕜 := ℝ) N).reApplyInnerSelf (sphere 0 ‖v‖) v := by
    intro x hx
    have hh := hmax x (by simpa only [hvnorm] using hx)
    change ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) N x, x⟫ ≤
      ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) N v, v⟫
    simpa only [sphereQuadratic, real_inner_comm] using hh
  have he := hsa.eq_smul_self_of_isLocalExtrOn (Or.inr hmax'.isLocalMaxOn)
  refine ⟨v, hvnorm, ?_⟩
  convert he using 1
  simp only [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
    RCLike.re_to_real, hvnorm, one_pow, div_one]
  rw [real_inner_comm]
  exact congrArg (fun t : ℝ => t • v) htop

theorem integrable_sphereQuadratic_pow {d : ℕ} (N : Matrix (Fin d) (Fin d) ℝ) (p : ℕ) :
    Integrable (fun g => sphereQuadratic N g ^ p) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  have hi := (IsGaussian.memLp_id (stdGaussian (EuclideanSpace ℝ (Fin d)))
    ((2 * p : ℕ) : ℝ≥0∞) (ENNReal.natCast_ne_top _)).integrable_norm_pow' (p := 2 * p)
  apply (hi.const_mul (‖Matrix.toEuclideanCLM (𝕜 := ℝ) N‖ ^ p)).mono' (by
    exact ((continuous_sphereQuadratic_fixed N).pow p).aestronglyMeasurable)
  filter_upwards [] with g
  simpa only [id_eq, Real.norm_eq_abs, abs_pow, mul_pow, ← pow_mul] using
    pow_le_pow_left₀ (abs_nonneg (sphereQuadratic N g)) (abs_sphereQuadratic_le N g) p

/-- Deterministic C13 Gaussian lower bound, with the top Rayleigh supremum. -/
theorem sphereTop_pow_mul_doubleFactorial_le_integral_of_ne_zero {d : ℕ} [NeZero d]
    {N : Matrix (Fin d) (Fin d) ℝ} (hN : N.PosSemidef) (p : ℕ) :
    sphereTop N ^ p * ((2 * p - 1)‼ : ℝ) ≤
      ∫ g, sphereQuadratic N g ^ p ∂stdGaussian (EuclideanSpace ℝ (Fin d)) := by
  obtain ⟨v, hv, he⟩ := exists_unit_top_eigenvector hN
  have hp : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ⟪v, g⟫ ^ (2 * p))
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    have hm := (IsGaussian.hasGaussianLaw_id (μ := stdGaussian (EuclideanSpace ℝ (Fin d)))).map
      (innerSL ℝ v)
    simpa only [Function.comp_def, id_eq, innerSL_apply_apply, Real.norm_eq_abs,
      pow_abs_two_mul] using
      (hm.memLp (p := ((2 * p : ℕ) : ℝ≥0∞)) (ENNReal.natCast_ne_top _)).integrable_norm_pow'
        (p := 2 * p)
  have hle := integral_mono (hp.const_mul (sphereTop N ^ p)) (integrable_sphereQuadratic_pow N p)
    (fun g => by
      simpa only [mul_pow, ← pow_mul] using
        pow_le_pow_left₀ (mul_nonneg (sphereTop_nonneg hN) (sq_nonneg ⟪v, g⟫))
          (sphereQuadratic_rank_one_le hN hv he g) p)
  simpa only [integral_const_mul, integral_inner_pow_stdGaussian_even, hv, one_pow, mul_one]
    using hle

@[simp] theorem sphereQuadratic_fin_zero (N : Matrix (Fin 0) (Fin 0) ℝ)
    (x : EuclideanSpace ℝ (Fin 0)) : sphereQuadratic N x = 0 := by
  have hx : x = 0 := Subsingleton.elim _ _
  simp only [hx, sphereQuadratic, map_zero, inner_zero_left]

@[simp] theorem sphereTop_fin_zero (N : Matrix (Fin 0) (Fin 0) ℝ) : sphereTop N = 0 := by
  have hs : sphere (0 : EuclideanSpace ℝ (Fin 0)) 1 = ∅ := by
    apply Set.eq_empty_of_forall_notMem
    intro x hx
    have hn := mem_sphere_zero_iff_norm.mp hx
    have hx0 : x = 0 := Subsingleton.elim _ _
    rw [hx0, norm_zero] at hn
    norm_num at hn
  simp only [sphereTop, hs, Set.image_empty, Real.sSup_empty]

/-- The deterministic Gaussian-average PSD bound, including dimension zero. -/
theorem sphereTop_pow_mul_doubleFactorial_le_integral {d : ℕ}
    {N : Matrix (Fin d) (Fin d) ℝ} (hN : N.PosSemidef) (p : ℕ) :
    sphereTop N ^ p * ((2 * p - 1)‼ : ℝ) ≤
      ∫ g, sphereQuadratic N g ^ p ∂stdGaussian (EuclideanSpace ℝ (Fin d)) := by
  by_cases hd : d = 0
  · subst d
    by_cases hp : p = 0
    · subst p
      norm_num
    · simp only [sphereTop_fin_zero, sphereQuadratic_fin_zero, zero_pow hp,
        zero_mul, integral_zero, le_refl]
  · have : NeZero d := ⟨hd⟩
    exact sphereTop_pow_mul_doubleFactorial_le_integral_of_ne_zero hN p

end GMCExplicitDelta.Insertion
