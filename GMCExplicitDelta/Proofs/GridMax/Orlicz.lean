module

public import GMCExplicitDelta.Source.SubGaussian
public import GMCExplicitDelta.Source.SubGaussianMoments
public import GMCExplicitDelta.Source.SubGaussianMax
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Finite Orlicz convexity (step S10)

The convexity estimate does not require the random variables to be nonnegative.
-/

@[expose] public section

open MeasureTheory Real
open GMCExplicitDelta.Source

namespace GMCExplicitDelta.Assembly.GridMax

/-- The square-exponential is convex on the whole real line. -/
theorem convexOn_exp_sq : ConvexOn ℝ Set.univ (fun x : ℝ => exp (x ^ 2)) := by
  have hsq : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) :=
    Even.convexOn_pow (by decide : Even 2)
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  exact (exp_le_exp.mpr (hsq.2 hx hy ha hb hab)).trans
    (convexOn_exp.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab)

/-- Jensen's inequality with the missing mass placed at zero. -/
theorem exp_sq_sum_le {ι : Type*} (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i ≤ 1) :
    exp ((∑ i ∈ s, w i * x i) ^ 2) ≤
      (1 - ∑ i ∈ s, w i) + ∑ i ∈ s, w i * exp ((x i) ^ 2) := by
  have h := convexOn_exp_sq.map_add_sum_le (t := s) (w := w) (p := x)
    (v := 1 - ∑ i ∈ s, w i) (q := 0) hw (by ring)
    (fun _ _ => Set.mem_univ _) (sub_nonneg.mpr hs) (Set.mem_univ _)
  simpa only [smul_eq_mul, mul_zero, zero_add, zero_pow (by decide : 2 ≠ 0),
    exp_zero, mul_one] using h

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- S10 in normalized coordinates: convexity preserves the Orlicz bound. -/
theorem integrable_integral_exp_sq_sum_le_two {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (X : ι → Ω → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i ≤ 1)
    (hX : ∀ i ∈ s, AEStronglyMeasurable (X i) μ)
    (hint : ∀ i ∈ s, Integrable (fun ω => exp ((X i ω) ^ 2)) μ)
    (hbound : ∀ i ∈ s, ∫ ω, exp ((X i ω) ^ 2) ∂μ ≤ 2) :
    Integrable (fun ω => exp ((∑ i ∈ s, w i * X i ω) ^ 2)) μ ∧
      ∫ ω, exp ((∑ i ∈ s, w i * X i ω) ^ 2) ∂μ ≤ 2 := by
  let F : Ω → ℝ := fun ω => (1 - ∑ i ∈ s, w i) +
    ∑ i ∈ s, w i * exp ((X i ω) ^ 2)
  have hF : Integrable F μ := (integrable_const _).add
    (integrable_finsetSum s fun i hi => (hint i hi).const_mul (w i))
  have hmeas : AEStronglyMeasurable (fun ω => exp ((∑ i ∈ s, w i * X i ω) ^ 2)) μ := by
    simpa only [Finset.sum_apply] using
      ((Finset.aemeasurable_sum s fun i hi => (hX i hi).aemeasurable.const_mul (w i)).pow_const 2).exp.aestronglyMeasurable
  have hdom : ∀ ω, exp ((∑ i ∈ s, w i * X i ω) ^ 2) ≤ F ω :=
    fun ω => exp_sq_sum_le s w (fun i => X i ω) hw hs
  have hInt : Integrable (fun ω => exp ((∑ i ∈ s, w i * X i ω) ^ 2)) μ :=
    hF.mono' hmeas (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      exact hdom ω)
  refine ⟨hInt, ?_⟩
  calc
    _ ≤ ∫ ω, F ω ∂μ := integral_mono hInt hF hdom
    _ = (1 - ∑ i ∈ s, w i) + ∑ i ∈ s, w i * ∫ ω, exp ((X i ω) ^ 2) ∂μ := by
      rw [integral_add (integrable_const _) (integrable_finsetSum s
        fun i hi => (hint i hi).const_mul (w i))]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul,
        integral_finsetSum s (fun i hi => (hint i hi).const_mul (w i)), integral_const_mul]
    _ ≤ (1 - ∑ i ∈ s, w i) + ∑ i ∈ s, w i * 2 := by
      exact add_le_add_right (Finset.sum_le_sum fun i hi =>
        mul_le_mul_of_nonneg_left (hbound i hi) (hw i hi)) _
    _ ≤ 2 := by rw [← Finset.sum_mul]; linarith only [hs]

/-- S10: the Orlicz estimate for coefficients of total mass at most `A`.
The convexity conclusion itself permits zero scale, using Lean’s total division. -/
theorem integrable_integral_exp_sq_weighted_sum_le_two {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (W : ι → Ω → ℝ) {A δ : ℝ} (hA : 0 < A)
    (hc : ∀ i ∈ s, 0 ≤ c i) (hs : ∑ i ∈ s, c i ≤ A)
    (hW : ∀ i ∈ s, AEStronglyMeasurable (W i) μ)
    (hint : ∀ i ∈ s, Integrable (fun ω => exp ((W i ω) ^ 2 / δ ^ 2)) μ)
    (hbound : ∀ i ∈ s, ∫ ω, exp ((W i ω) ^ 2 / δ ^ 2) ∂μ ≤ 2) :
    Integrable (fun ω => exp ((∑ i ∈ s, c i * W i ω) ^ 2 / (A * δ) ^ 2)) μ ∧
      ∫ ω, exp ((∑ i ∈ s, c i * W i ω) ^ 2 / (A * δ) ^ 2) ∂μ ≤ 2 := by
  have heq : ∀ ω, (∑ i ∈ s, c i / A * (W i ω / δ)) =
      (∑ i ∈ s, c i * W i ω) / (A * δ) := by
    intro ω
    simp only [div_mul_div_comm, Finset.sum_div]
  have h := integrable_integral_exp_sq_sum_le_two s (fun i => c i / A)
    (fun i ω => W i ω / δ) (fun i hi => div_nonneg (hc i hi) hA.le)
    (by rw [← Finset.sum_div]; exact (div_le_one hA).mpr hs)
    (fun i hi => by
      simpa only [div_eq_mul_inv] using (hW i hi).mul_const δ⁻¹)
    (fun i hi => by simpa only [div_pow] using hint i hi)
    (fun i hi => by simpa only [div_pow] using hbound i hi)
  simpa only [heq, div_pow] using h

/-- Completing the square in the exponential estimate. -/
theorem mul_le_sq_div_add {B : ℝ} (hB : B ≠ 0) (t z : ℝ) :
    t * z ≤ z ^ 2 / B ^ 2 + t ^ 2 * B ^ 2 / 4 := by
  have heq : z ^ 2 / B ^ 2 + t ^ 2 * B ^ 2 / 4 - t * z =
      (z / B - t * B / 2) ^ 2 := by
    field_simp [hB]
    ring
  rw [← sub_nonneg, heq]
  exact sq_nonneg _

omit [IsProbabilityMeasure μ] in
/-- S10's linear exponential estimate from the square-exponential bound. -/
theorem integral_exp_mul_le_of_orlicz {Z : Ω → ℝ} {B : ℝ} (hB : B ≠ 0)
    (hZ : AEStronglyMeasurable Z μ)
    (hint : Integrable (fun ω => exp ((Z ω) ^ 2 / B ^ 2)) μ)
    (hbound : ∫ ω, exp ((Z ω) ^ 2 / B ^ 2) ∂μ ≤ 2) (t : ℝ) :
    ∫ ω, exp (t * Z ω) ∂μ ≤ 2 * exp (t ^ 2 * B ^ 2 / 4) := by
  let K := exp (t ^ 2 * B ^ 2 / 4)
  have hdom : ∀ ω, exp (t * Z ω) ≤ K * exp ((Z ω) ^ 2 / B ^ 2) := by
    intro ω
    rw [← exp_add]
    exact exp_le_exp.mpr (by
      simpa only [add_comm] using mul_le_sq_div_add hB t (Z ω))
  have hInt : Integrable (fun ω => exp (t * Z ω)) μ :=
    (hint.const_mul K).mono'
      (continuous_exp.comp_aestronglyMeasurable (hZ.const_mul t))
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
        exact hdom ω)
  calc
    _ ≤ ∫ ω, K * exp ((Z ω) ^ 2 / B ^ 2) ∂μ :=
      integral_mono hInt (hint.const_mul K) hdom
    _ = K * ∫ ω, exp ((Z ω) ^ 2 / B ^ 2) ∂μ := integral_const_mul _ _
    _ ≤ K * 2 := mul_le_mul_of_nonneg_left hbound (exp_pos _).le
    _ = _ := mul_comm _ _

omit [IsProbabilityMeasure μ] in
/-- Integer moments from the Orlicz estimate, with the exact factorial/Gamma constant. -/
theorem integral_abs_pow_le_of_orlicz {Z : Ω → ℝ} {B : ℝ} (hB : B ≠ 0)
    (n : ℕ) (hint : Integrable (fun ω => exp ((Z ω) ^ 2 / B ^ 2)) μ)
    (hbound : ∫ ω, exp ((Z ω) ^ 2 / B ^ 2) ∂μ ≤ 2)
    (hpowInt : Integrable (fun ω => |Z ω| ^ (2 * n)) μ) :
    ∫ ω, |Z ω| ^ (2 * n) ∂μ ≤ 2 * B ^ (2 * n) * Gamma (n + 1) := by
  have hfactorial : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hdom : ∀ ω, |Z ω| ^ (2 * n) ≤
      (B ^ (2 * n) * n.factorial) * exp ((Z ω) ^ 2 / B ^ 2) := by
    intro ω
    have h := (div_le_iff₀ hfactorial).mp
      (pow_div_factorial_le_exp ((Z ω) ^ 2 / B ^ 2) (div_nonneg (sq_nonneg (Z ω)) (sq_nonneg B)) n)
    have heq : ((Z ω) ^ 2 / B ^ 2) ^ n = |Z ω| ^ (2 * n) / B ^ (2 * n) := by
      rw [← sq_abs (Z ω), div_pow, ← pow_mul, ← pow_mul]
    rw [heq] at h
    have hBp : 0 < B ^ (2 * n) := by
      rw [pow_mul]
      exact pow_pos (sq_pos_of_ne_zero hB) n
    have h := (div_le_iff₀ hBp).mp h
    calc
      _ ≤ (exp ((Z ω) ^ 2 / B ^ 2) * n.factorial) * B ^ (2 * n) := h
      _ = _ := by ring
  calc
    _ ≤ ∫ ω, (B ^ (2 * n) * n.factorial) * exp ((Z ω) ^ 2 / B ^ 2) ∂μ :=
      integral_mono hpowInt (hint.const_mul _) hdom
    _ = (B ^ (2 * n) * n.factorial) * ∫ ω, exp ((Z ω) ^ 2 / B ^ 2) ∂μ :=
      integral_const_mul _ _
    _ ≤ (B ^ (2 * n) * n.factorial) * 2 :=
      mul_le_mul_of_nonneg_left hbound (mul_nonneg (by rw [pow_mul]; exact pow_nonneg (sq_nonneg B) n) hfactorial.le)
    _ = _ := by rw [Gamma_nat_eq_factorial]; ring

end GMCExplicitDelta.Assembly.GridMax


open MeasureTheory ProbabilityTheory Real
open GMCExplicitDelta.Source
open scoped NNReal

namespace GMCExplicitDelta.Assembly.GridMax

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

end GMCExplicitDelta.Assembly.GridMax
