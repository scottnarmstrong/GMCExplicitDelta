module

public import GMCExplicitDelta.Averaging.MatrixAverageContract

/-! # PSD matrix averaging with color classes (A5) -/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal Matrix.Norms.L2Operator
open GMCExplicitDelta.Insertion

namespace GMCExplicitDelta.Averaging

/-- The centered average of all matrices, indexed by their color and index within that color. -/
noncomputable def coloredMatrixAverage {Ω : Type*} [MeasurableSpace Ω] {d r : ℕ}
    (μ : Measure Ω) (n : Fin r → ℕ)
    (M : (c : Fin r) → Fin (n c) → Ω → Matrix (Fin d) (Fin d) ℝ) (ω : Ω) :
    Matrix (Fin d) (Fin d) ℝ :=
  ((∑ c, n c : ℕ) : ℝ)⁻¹ • ∑ c, ∑ i, (M c i ω - ∫ ω', M c i ω' ∂μ)

theorem coloredMatrixAverage_eq_weighted {Ω : Type*} [MeasurableSpace Ω] {d r : ℕ}
    (μ : Measure Ω) (n : Fin r → ℕ) (hn : ∀ c, 0 < n c)
    (M : (c : Fin r) → Fin (n c) → Ω → Matrix (Fin d) (Fin d) ℝ) :
    coloredMatrixAverage μ n M = fun ω =>
      ∑ c, ((n c : ℝ) / (∑ c, n c : ℕ)) • centeredMatrixAverage μ (M c) ω := by
  funext ω
  unfold coloredMatrixAverage centeredMatrixAverage
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [smul_smul]
  congr 1
  have hc : (n c : ℝ) ≠ 0 := by exact_mod_cast (hn c).ne'
  field_simp

/-- **A5.** Arbitrarily sized nonempty independent color classes. No independence is required
between different colors. The matrix norm in `lpNorm` is the Euclidean operator norm. -/
theorem lpNorm_coloredMatrixAverage_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {d r : ℕ} (hd : 2 ≤ d)
    (n : Fin r → ℕ) (hn : ∀ c, 0 < n c)
    (M : (c : Fin r) → Fin (n c) → Ω → Matrix (Fin d) (Fin d) ℝ)
    {D F : ℝ} (hD : 0 < D) (hF : 0 < F)
    (hM : ∀ c i, Measurable (M c i)) (hm : ∀ c i, MemLp (M c i) 32 μ)
    (hPSD : ∀ c i ω, (M c i ω).PosSemidef) (hind : ∀ c, iIndepFun (M c) μ)
    (hmean : ∀ c i u, ‖u‖ = 1 → ∫ ω, sphereQuadratic (M c i ω) u ∂μ ≤ F)
    (hmoment : ∀ c i, ∫ ω, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (M c i ω)‖ ^ 32 ∂μ ≤ D ^ 32)
    (hL : 0 < Contract.sphereLower d)
    (hcert : 1 < Contract.sigmaNorm d ^ 32 * Contract.sphereLower d) :
    lpNorm (coloredMatrixAverage μ n M) 32 μ ≤
      (Contract.sigmaNorm d : ℝ) * D * ((∑ c, n c : ℕ) : ℝ)⁻¹ *
        ∑ c, (n c : ℝ) * Contract.Bbar32 (n c) D F := by
  rw [coloredMatrixAverage_eq_weighted μ n hn M]
  have hclass c := lpNorm_centeredMatrixAverage_le hd (hn c) hF hD (hM c) (hm c)
    (hPSD c) (hind c) (hmean c) (hmoment c)
    (le_refl (Contract.Tvarpi D F)) hL hcert
  simp only [avgBound_eq_Bbar32] at hclass
  have hsum := lpNorm_sum_le (p := (32 : ℝ≥0∞)) (s := Finset.univ)
    (f := fun c => ((n c : ℝ) / (∑ c, n c : ℕ)) • centeredMatrixAverage μ (M c))
    (fun c _ => (memLp_centeredMatrixAverage (hm c)).const_smul
      ((n c : ℝ) / (∑ c, n c : ℕ))) (by norm_num)
  change lpNorm (fun ω => ∑ c, _) 32 μ ≤ _
  have he : (fun ω => ∑ c, ((n c : ℝ) / (∑ c, n c : ℕ)) •
      centeredMatrixAverage μ (M c) ω) =
      ∑ c, ((n c : ℝ) / (∑ c, n c : ℕ)) • centeredMatrixAverage μ (M c) := by
    ext ω i j
    simp only [Finset.sum_apply, Pi.smul_apply]
  rw [he]
  apply hsum.trans
  calc
    _ ≤ ∑ c, ((n c : ℝ) / (∑ c, n c : ℕ)) *
        ((Contract.sigmaNorm d : ℝ) * D * Contract.Bbar32 (n c) D F) := by
      apply Finset.sum_le_sum
      intro c _
      rw [lpNorm_const_smul, coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (hclass c) (by positivity)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      simp only [div_eq_mul_inv]
      ring

/-- The equal-class specialization of A5. -/
theorem lpNorm_coloredMatrixAverage_equal_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {d r n : ℕ} (hd : 2 ≤ d)
    (hr : 0 < r) (hn : 0 < n)
    (M : Fin r → Fin n → Ω → Matrix (Fin d) (Fin d) ℝ)
    {D F : ℝ} (hD : 0 < D) (hF : 0 < F)
    (hM : ∀ c i, Measurable (M c i)) (hm : ∀ c i, MemLp (M c i) 32 μ)
    (hPSD : ∀ c i ω, (M c i ω).PosSemidef) (hind : ∀ c, iIndepFun (M c) μ)
    (hmean : ∀ c i u, ‖u‖ = 1 → ∫ ω, sphereQuadratic (M c i ω) u ∂μ ≤ F)
    (hmoment : ∀ c i, ∫ ω, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (M c i ω)‖ ^ 32 ∂μ ≤ D ^ 32)
    (hL : 0 < Contract.sphereLower d)
    (hcert : 1 < Contract.sigmaNorm d ^ 32 * Contract.sphereLower d) :
    lpNorm (coloredMatrixAverage μ (fun _ : Fin r => n) M) 32 μ ≤
      (Contract.sigmaNorm d : ℝ) * D * Contract.Bbar32 n D F := by
  have h := lpNorm_coloredMatrixAverage_le hd (fun _ : Fin r => n) (fun _ => hn)
    M hD hF hM hm hPSD hind hmean hmoment hL hcert
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_mul, Nat.cast_id] at h
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  convert h using 1
  field_simp

end GMCExplicitDelta.Averaging
