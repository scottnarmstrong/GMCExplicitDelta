module

public import GMCExplicitDelta.Source.SubGaussian
public import GMCExplicitDelta.Source.SubGaussianMoments
public import GMCExplicitDelta.Source.SubGaussianMax
public import GMCExplicitDelta.Source.SubGaussianOrlicz

/-! # The finite maximum and Orlicz conclusions of S8 and S10 -/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace GMCExplicitDelta.Source

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- S8(b), in the squared-norm form used in the proof map. -/
theorem moment_root_sq_le_of_gaussian_tail {Z : Ω → ℝ}
    (hZ : AEMeasurable Z μ) {σ : ℝ} (hσ : 0 < σ) {p : ℕ} (hp : 0 < p)
    (hint : Integrable (fun ω => |Z ω| ^ (4 * p)) μ)
    (htail : ∀ u : ℝ, 0 ≤ u → μ.real {ω | u ≤ |Z ω|} ≤ 2 * exp (-u ^ 2 / σ ^ 2)) :
    ((∫ ω, |Z ω| ^ (4 * p) ∂μ) ^ (1 / (4 * p : ℝ))) ^ 2 ≤
      σ ^ 2 * subgaussianMomentFactor p := by
  have h := moment_root_le_of_gaussian_tail hZ hσ hp hint htail
  have hsq := (sq_le_sq₀ (rpow_nonneg (integral_nonneg fun ω =>
    pow_nonneg (abs_nonneg (Z ω)) (4 * p)) _)
    (mul_nonneg hσ.le (sqrt_nonneg _))).mpr h
  have hP : 0 ≤ subgaussianMomentFactor p := by
    unfold subgaussianMomentFactor
    positivity
  rw [mul_pow, sq_sqrt hP] at hsq
  exact hsq

/-- S8(c): the `4p` moment norm of the maximum, without joint assumptions. -/
theorem moment_root_finset_max_le (s : Finset ι) (hne : s.Nonempty)
    (Z : ι → Ω → ℝ) (hZ : ∀ i ∈ s, Measurable (Z i))
    {σ : ℝ} (hσ : 0 < σ) {p : ℕ} (hp : 0 < p)
    (hint : ∀ i ∈ s, Integrable (fun ω => |Z i ω| ^ (4 * p)) μ)
    (htail : ∀ i ∈ s, ∀ u : ℝ, 0 ≤ u →
      μ.real {ω | u ≤ |Z i ω|} ≤ 2 * exp (-u ^ 2 / σ ^ 2)) :
    (∫ ω, (s.sup' hne (fun i => |Z i ω|)) ^ (4 * p) ∂μ) ^ (1 / (4 * p : ℝ)) ≤
      (s.card : ℝ) ^ (1 / (4 * p : ℝ)) * σ * sqrt (subgaussianMomentFactor p) := by
  have hmeas : ∀ i ∈ s, Measurable (fun ω => |Z i ω|) := by
    intro i hi
    simpa only [Real.norm_eq_abs] using (hZ i hi).norm
  have h := integral_pow_finset_sup'_le s hne (fun i ω => |Z i ω|) hmeas
    (fun _ _ ω => abs_nonneg (Z _ ω)) (4 * p)
    (2 * σ ^ (4 * p) * Gamma ((2 * p : ℕ) + 1)) hint (by
      intro i hi
      simpa only [show 2 * (2 * p) = 4 * p by omega] using
        integral_abs_pow_le_of_gaussian_tail (hZ i hi).aemeasurable hσ
          (by norm_num : (0 : ℝ) ≤ 2) (by omega : 0 < 2 * p)
          (by simpa only [show 2 * (2 * p) = 4 * p by omega] using hint i hi) (htail i hi))
  have hnonneg : 0 ≤ ∫ ω, (s.sup' hne (fun i => |Z i ω|)) ^ (4 * p) ∂μ := by
    apply integral_nonneg
    intro ω
    obtain ⟨i, _, heq⟩ := Finset.exists_mem_eq_sup' hne (fun i => |Z i ω|)
    change 0 ≤ (s.sup' hne (fun i => |Z i ω|)) ^ (4 * p)
    rw [heq]
    exact pow_nonneg (abs_nonneg _) _
  have hnorm : (∫ ω, (s.sup' hne (fun i => |Z i ω|)) ^ (4 * p) ∂μ) ≤
      σ ^ (4 * p) * ((s.card : ℝ) * (2 * Gamma ((2 * p : ℕ) + 1))) := by
    calc
      _ ≤ s.card * (2 * σ ^ (4 * p) * Gamma ((2 * p : ℕ) + 1)) := h
      _ = _ := by ring
  have hroot := moment_root_le hnonneg hσ.le (by positivity)
    (by omega : 4 * p ≠ 0) hnorm
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hroot
  have hsqrt := sqrt_subgaussianMomentFactor hp
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hsqrt
  rw [mul_rpow (Nat.cast_nonneg _) (by positivity), ← hsqrt] at hroot
  calc
    _ ≤ σ * ((s.card : ℝ) ^ (1 / (4 * p : ℝ)) * sqrt (subgaussianMomentFactor p)) := hroot
    _ = _ := by ring

omit [IsProbabilityMeasure μ] in
/-- S8(c): exponential moment of the maximum under a common sub-Gaussian MGF bound. -/
theorem integral_exp_finset_max_le (s : Finset ι) (hne : s.Nonempty)
    (Z : ι → Ω → ℝ) (hZ : ∀ i ∈ s, Measurable (Z i))
    {c : ℝ≥0} (hsub : ∀ i ∈ s, HasSubgaussianMGF (Z i) c μ) (p : ℕ) :
    ∫ ω, exp ((4 * p : ℝ) * s.sup' hne (fun i => |Z i ω|)) ∂μ ≤
      2 * s.card * exp (8 * (p : ℝ) ^ 2 * c) := by
  have hmeas : ∀ i ∈ s, Measurable (fun ω => |Z i ω|) := by
    intro i hi
    simpa only [Real.norm_eq_abs] using (hZ i hi).norm
  have hexp : (c : ℝ) * (4 * p : ℝ) ^ 2 / 2 = 8 * (p : ℝ) ^ 2 * c := by ring
  have h := integral_exp_finset_sup'_le s hne (fun i ω => |Z i ω|) hmeas (4 * p)
    (2 * exp (8 * (p : ℝ) ^ 2 * c))
    (fun i hi => integrable_exp_mul_abs_of_subgaussian (hsub i hi) _)
    (fun i hi => by simpa only [hexp] using
      integral_exp_mul_abs_le_of_subgaussian (hsub i hi) (4 * p))
  calc
    _ ≤ s.card * (2 * exp (8 * (p : ℝ) ^ 2 * c)) := h
    _ = _ := by ring

/-- S10: the Orlicz, moment-norm, and linear exponential bounds together. -/
theorem orlicz_weighted_sum_bounds (s : Finset ι) (c : ι → ℝ) (W : ι → Ω → ℝ)
    {A δ : ℝ} (hA : 0 < A) (hδ : 0 < δ) {p : ℕ} (hp : 0 < p)
    (hc : ∀ i ∈ s, 0 ≤ c i) (hs : ∑ i ∈ s, c i ≤ A)
    (hW : ∀ i ∈ s, AEStronglyMeasurable (W i) μ)
    (hint : ∀ i ∈ s, Integrable (fun ω => exp ((W i ω) ^ 2 / δ ^ 2)) μ)
    (hbound : ∀ i ∈ s, ∫ ω, exp ((W i ω) ^ 2 / δ ^ 2) ∂μ ≤ 2)
    (hpowInt : Integrable (fun ω => |∑ i ∈ s, c i * W i ω| ^ (4 * p)) μ) :
    (∫ ω, exp ((∑ i ∈ s, c i * W i ω) ^ 2 / (A * δ) ^ 2) ∂μ ≤ 2) ∧
    ((∫ ω, |∑ i ∈ s, c i * W i ω| ^ (4 * p) ∂μ) ^ (1 / (4 * p : ℝ)) ≤
      A * δ * sqrt (subgaussianMomentFactor p)) ∧
    (∫ ω, exp ((4 * p : ℝ) * (∑ i ∈ s, c i * W i ω)) ∂μ ≤
      2 * exp (4 * (p : ℝ) ^ 2 * A ^ 2 * δ ^ 2)) := by
  obtain ⟨hInt, hOrlicz⟩ := integrable_integral_exp_sq_weighted_sum_le_two
    s c W hA hc hs hW hint hbound
  refine ⟨hOrlicz, ?_, ?_⟩
  · have h := integral_abs_pow_le_of_orlicz (mul_pos hA hδ).ne' (2 * p) hInt hOrlicz
      (by simpa only [show 2 * (2 * p) = 4 * p by omega] using hpowInt)
    rw [show 2 * (2 * p) = 4 * p by omega] at h
    have hn : (∫ ω, |∑ i ∈ s, c i * W i ω| ^ (4 * p) ∂μ) ≤
        (A * δ) ^ (4 * p) * (2 * Gamma ((2 * p : ℕ) + 1)) := by
      calc
        _ ≤ 2 * (A * δ) ^ (4 * p) * Gamma ((2 * p : ℕ) + 1) := h
        _ = _ := by ring
    have hroot := moment_root_le (integral_nonneg fun ω => pow_nonneg (abs_nonneg _) _)
      (mul_pos hA hδ).le (by positivity) (by omega : 4 * p ≠ 0) hn
    simpa only [Nat.cast_mul, Nat.cast_ofNat, sqrt_subgaussianMomentFactor hp] using hroot
  · have hmeas : AEStronglyMeasurable (fun ω => ∑ i ∈ s, c i * W i ω) μ := by
      exact s.aestronglyMeasurable_fun_sum (fun i hi => (hW i hi).const_mul (c i))
    have h := integral_exp_mul_le_of_orlicz (mul_pos hA hδ).ne' hmeas hInt hOrlicz (4 * p)
    have heq : (4 * p : ℝ) ^ 2 * (A * δ) ^ 2 / 4 =
        4 * (p : ℝ) ^ 2 * A ^ 2 * δ ^ 2 := by ring
    simpa only [heq] using h

end GMCExplicitDelta.Source
