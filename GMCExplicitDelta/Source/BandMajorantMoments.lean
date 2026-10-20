module

public import GMCExplicitDelta.Source.ExpMomentSeries
public import GMCExplicitDelta.Source.BandMajorant
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.IdentDistrib

/-! # Moment series of independent finite sums -/

@[expose] public section

namespace GMCExplicitDelta.Source

open MeasureTheory ProbabilityTheory PowerSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The formal exponential moment series; no convergence is needed for this definition. -/
noncomputable def momentSeries (X : Ω → ℝ) (μ : Measure Ω) : PowerSeries ℝ :=
  PowerSeries.mk fun n => (∫ ω, X ω ^ n ∂μ) / n.factorial

/-- Binomial coefficients normalize to convolution coefficients after division by `n!`. -/
theorem choose_div_factorial {n k : ℕ} (hk : k ≤ n) :
    (n.choose k : ℝ) / n.factorial = 1 / ((k.factorial : ℝ) * (n - k).factorial) := by
  have h : (n.choose k : ℝ) * k.factorial * (n - k).factorial = n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  have hkf : (k.factorial : ℝ) ≠ 0 := by positivity
  have hnkf : ((n - k).factorial : ℝ) ≠ 0 := by positivity
  apply (div_eq_div_iff hf (mul_ne_zero hkf hnkf)).mpr
  simpa only [mul_assoc, one_mul] using h

/-- Products of powers are integrable when both variables have all integrable powers. -/
theorem integrable_mul_powers {X Y : Ω → ℝ}
    (hX : ∀ n : ℕ, Integrable (fun ω => X ω ^ n) μ)
    (hY : ∀ n : ℕ, Integrable (fun ω => Y ω ^ n) μ) (k l : ℕ) :
    Integrable (fun ω => X ω ^ k * Y ω ^ l) μ := by
  have hdom : Integrable (fun ω => (X ω ^ (2 * k) + Y ω ^ (2 * l)) / 2) μ := by
    simpa only [Pi.add_apply] using ((hX (2 * k)).add (hY (2 * l))).div_const 2
  apply hdom.mono' ((hX k).aestronglyMeasurable.mul (hY l).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro ω
  rw [Real.norm_eq_abs]
  change |X ω ^ k * Y ω ^ l| ≤ (X ω ^ (2 * k) + Y ω ^ (2 * l)) / 2
  rw [show 2 * k = k * 2 by omega, show 2 * l = l * 2 by omega, pow_mul, pow_mul]
  have hscalar : ∀ a b : ℝ, |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
    intro a b
    rw [abs_mul]
    nlinarith only [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]
  exact hscalar _ _

/-- Powers of a sum are integrable when both variables have all integrable powers. -/
theorem integrable_add_pow_of_powers {X Y : Ω → ℝ}
    (hX : ∀ n : ℕ, Integrable (fun ω => X ω ^ n) μ)
    (hY : ∀ n : ℕ, Integrable (fun ω => Y ω ^ n) μ) (n : ℕ) :
    Integrable (fun ω => (X ω + Y ω) ^ n) μ := by
  simp_rw [add_pow]
  apply integrable_finsetSum
  intro k _
  exact (integrable_mul_powers hX hY k (n - k)).mul_const _

/-- The formal moment series of two independent variables multiplies. -/
theorem momentSeries_add_of_indep {X Y : Ω → ℝ} (hXY : IndepFun X Y μ)
    (hX : ∀ n : ℕ, Integrable (fun ω => X ω ^ n) μ)
    (hY : ∀ n : ℕ, Integrable (fun ω => Y ω ^ n) μ) :
    momentSeries (fun ω => X ω + Y ω) μ = momentSeries X μ * momentSeries Y μ := by
  ext n
  simp only [momentSeries, coeff_mk, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp_rw [add_pow]
  have hInt : ∀ k : ℕ, k ∈ Finset.range (n + 1) → Integrable
      (fun ω => X ω ^ k * Y ω ^ (n - k) * (n.choose k : ℝ)) μ := by
    intro k _
    exact (integrable_mul_powers hX hY k (n - k)).mul_const _
  rw [integral_finsetSum _ hInt, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hprod := (hXY.comp (measurable_id.pow_const k) (measurable_id.pow_const (n - k))).integral_fun_mul_eq_mul_integral
    (hX k).aestronglyMeasurable (hY (n - k)).aestronglyMeasurable
  rw [integral_mul_const]
  change ((∫ ω, (X ω ^ k) * (Y ω ^ (n - k)) ∂μ) * (n.choose k : ℝ)) / n.factorial = _
  simp only [Function.comp_def, id_eq] at hprod
  rw [hprod]
  have hc := choose_div_factorial (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  calc
    _ = ((∫ ω, X ω ^ k ∂μ) * (∫ ω, Y ω ^ (n - k) ∂μ)) *
        ((n.choose k : ℝ) / n.factorial) := by ring
    _ = _ := by
      rw [hc]
      simp only [mul_inv_rev, div_eq_mul_inv]
      ring

/-- Formal moment series of an independent finite sum are the product of the individual series. -/
theorem momentSeries_finset_sum [IsProbabilityMeasure μ] {ι : Type*} (s : Finset ι)
    (X : ι → Ω → ℝ) (hm : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hint : ∀ i, ∀ n : ℕ, Integrable (fun ω => X i ω ^ n) μ) :
    (∀ n : ℕ, Integrable (fun ω => (∑ i ∈ s, X i ω) ^ n) μ) ∧
      momentSeries (fun ω => ∑ i ∈ s, X i ω) μ = ∏ i ∈ s, momentSeries (X i) μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨fun n => by simpa only [Finset.sum_empty] using integrable_const ((0 : ℝ) ^ n), ?_⟩
    simp only [Finset.sum_empty, Finset.prod_empty]
    ext n
    rw [momentSeries, coeff_mk, coeff_one]
    rcases n with _ | n <;> simp
  | @insert i s hi ih =>
    have hInd : IndepFun (X i) (fun ω => ∑ j ∈ s, X j ω) μ := by
      have heq : (∑ j ∈ s, X j) = (fun ω => ∑ j ∈ s, X j ω) := by
        funext ω
        rw [Finset.sum_apply]
      simpa only [heq] using (hind.indepFun_finsetSum_of_notMem hm hi).symm
    simp_rw [Finset.sum_insert hi]
    refine ⟨fun n => integrable_add_pow_of_powers (hint i) ih.1 n, ?_⟩
    rw [momentSeries_add_of_indep hInd (hint i) ih.1, ih.2, Finset.prod_insert hi]

/-- All powers are integrable as soon as all even powers are. -/
theorem integrable_pow_of_even_powers {X : Ω → ℝ} [IsProbabilityMeasure μ]
    (hm : Measurable X) (hint : ∀ n : ℕ, Integrable (fun ω => X ω ^ (2 * n)) μ) (n : ℕ) :
    Integrable (fun ω => X ω ^ n) μ := by
  apply ((integrable_const 1).add (hint n)).mono' (hm.pow_const n).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  rw [Real.norm_eq_abs]
  change |X ω ^ n| ≤ 1 + X ω ^ (2 * n)
  rw [show 2 * n = n * 2 by omega, pow_mul]
  have hscalar : ∀ z : ℝ, |z| ≤ 1 + z ^ 2 := by
    intro z
    nlinarith only [sq_nonneg (|z| - 1 / 2), sq_abs z]
  exact hscalar _

/-- Symmetry kills each odd coefficient, without any independence requirement. -/
theorem integral_odd_pow_eq_zero {X : Ω → ℝ}
    (hsym : IdentDistrib X (fun ω => -X ω) μ μ) (n : ℕ) :
    ∫ ω, X ω ^ (2 * n + 1) ∂μ = 0 := by
  have heq := (hsym.comp (measurable_id.pow_const (2 * n + 1))).integral_eq
  have hpoint : ∀ ω, (-X ω) ^ (2 * n + 1) = -(X ω ^ (2 * n + 1)) := by
    intro ω
    rw [pow_succ, pow_mul, neg_sq, mul_neg, ← pow_mul, ← pow_succ]
  simp only [Function.comp_def, id_eq, hpoint, integral_neg] at heq
  linarith only [heq]

/-- The even half of the formal moment series. -/
noncomputable def evenMomentSeries (X : Ω → ℝ) (μ : Measure Ω) : PowerSeries ℝ :=
  PowerSeries.mk fun n => (∫ ω, X ω ^ (2 * n) ∂μ) / (2 * n).factorial

/-- Symmetric moment series are obtained by substituting `q²` in the even series. -/
theorem momentSeries_eq_expand {X : Ω → ℝ}
    (hsym : IdentDistrib X (fun ω => -X ω) μ μ) :
    momentSeries X μ = PowerSeries.expand 2 (by decide) (evenMomentSeries X μ) := by
  ext n
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hn : n = 2 * k := by omega
    rw [hn]
    rw [coeff_expand_mul, momentSeries, evenMomentSeries, coeff_mk, coeff_mk]
  · have hn : n = 2 * k + 1 := by omega
    rw [hn]
    rw [coeff_expand_of_not_dvd _ _ _ (by omega), momentSeries, coeff_mk,
      integral_odd_pow_eq_zero hsym, zero_div]

/-- Products of series inherit a common nonnegative coefficientwise majorant. -/
theorem coeff_finset_prod_le_pow {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℝ)
    (B : PowerSeries ℝ) (hf : ∀ i ∈ s, ∀ n, 0 ≤ coeff n (f i))
    (hB : ∀ n, 0 ≤ coeff n B) (hle : ∀ i ∈ s, ∀ n, coeff n (f i) ≤ coeff n B) (n : ℕ) :
    coeff n (∏ i ∈ s, f i) ≤ coeff n (B ^ s.card) := by
  classical
  induction s using Finset.induction_on generalizing n with
  | empty => simp only [Finset.prod_empty, Finset.card_empty, pow_zero, le_refl]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, pow_succ']
    exact coeff_mul_le (hf i (Finset.mem_insert_self _ _)) (coeff_pow_nonneg hB s.card)
      (hle i (Finset.mem_insert_self _ _))
      (fun n => ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
        (fun j hj => hle j (Finset.mem_insert_of_mem hj)) n) n

/-- Each one-point even moment series is dominated by the S9 one-band majorant. -/
theorem evenMomentSeries_coeff_le [IsProbabilityMeasure μ] {X : Ω → ℝ} {a u s c₂ c₃ : ℝ}
    (hvar : ∫ ω, X ω ^ 2 ∂μ ≤ u * s)
    (hfour : ∫ ω, X ω ^ 4 ∂μ ≤ c₂ * 3 * (a * s) ^ 2)
    (hhigh : ∀ n : ℕ, 3 ≤ n → ∫ ω, X ω ^ (2 * n) ∂μ ≤
      c₃ * ((2 * n - 1).doubleFactorial : ℝ) * (a * s) ^ n) (n : ℕ) :
    coeff n (evenMomentSeries X μ) ≤ coeff n (bandEvenMajorant a u s c₂ c₃) := by
  rw [evenMomentSeries, bandEvenMajorant, coeff_mk, coeff_mk]
  split_ifs with hn0 hn1 hn2
  · subst n; norm_num
  · subst n
    norm_num
    exact div_le_div_of_nonneg_right hvar (by norm_num)
  · subst n
    norm_num
    have h := div_le_div_of_nonneg_right hfour (by norm_num : (0 : ℝ) ≤ 24)
    convert h using 1
    ring
  · have h := div_le_div_of_nonneg_right (hhigh n (by omega))
      (show (0 : ℝ) ≤ (2 * n).factorial by positivity)
    calc
      _ ≤ (c₃ * ((2 * n - 1).doubleFactorial : ℝ) * (a * s) ^ n) / (2 * n).factorial := h
      _ = c₃ * (((2 * n - 1).doubleFactorial : ℝ) * (a * s) ^ n / (2 * n).factorial) := by ring
      _ = _ := by rw [doubleFactorial_div_even_factorial]; ring

/-- S9: independent symmetric band sums have the coefficientwise moment majorant. -/
theorem independent_sum_moment_majorant [IsProbabilityMeasure μ] {ι : Type*}
    (I : Finset ι) (X : ι → Ω → ℝ) (hm : ∀ i, Measurable (X i))
    (hind : iIndepFun X μ) (hsym : ∀ i, IdentDistrib (X i) (fun ω => -X i ω) μ μ)
    (hint : ∀ i, ∀ n : ℕ, Integrable (fun ω => X i ω ^ (2 * n)) μ)
    {a u s c₂ c₃ : ℝ} (ha : 0 ≤ a) (hu : 0 ≤ u) (hs : 0 ≤ s)
    (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃)
    (hvar : ∀ i, ∫ ω, X i ω ^ 2 ∂μ ≤ u * s)
    (hfour : ∀ i, ∫ ω, X i ω ^ 4 ∂μ ≤ c₂ * 3 * (a * s) ^ 2)
    (hhigh : ∀ i, ∀ n : ℕ, 3 ≤ n → ∫ ω, X i ω ^ (2 * n) ∂μ ≤
      c₃ * ((2 * n - 1).doubleFactorial : ℝ) * (a * s) ^ n) :
    (∀ n : ℕ, Integrable (fun ω => (∑ i ∈ I, X i ω) ^ n) μ) ∧
    (∀ n : ℕ, ∫ ω, (∑ i ∈ I, X i ω) ^ (2 * n + 1) ∂μ = 0) ∧
    (∀ n : ℕ, ∫ ω, (∑ i ∈ I, X i ω) ^ (2 * n) ∂μ ≤
      ((2 * n).factorial : ℝ) * coeff (2 * n) (bandMajorant a u s c₂ c₃ ^ I.card)) := by
  obtain ⟨hInt, hser⟩ := momentSeries_finset_sum I X hm hind
    (fun i => integrable_pow_of_even_powers (hm i) (hint i))
  have hserEven : momentSeries (fun ω => ∑ i ∈ I, X i ω) μ =
      PowerSeries.expand 2 (by decide) (∏ i ∈ I, evenMomentSeries (X i) μ) := by
    calc
      _ = ∏ i ∈ I, momentSeries (X i) μ := hser
      _ = ∏ i ∈ I, PowerSeries.expand 2 (by decide) (evenMomentSeries (X i) μ) :=
        Finset.prod_congr rfl (fun i _ => momentSeries_eq_expand (hsym i))
      _ = _ := (map_prod _ _ _).symm
  have hfpos : ∀ i ∈ I, ∀ n, 0 ≤ coeff n (evenMomentSeries (X i) μ) := by
    intro i _ n
    rw [evenMomentSeries, coeff_mk]
    apply div_nonneg
    · apply integral_nonneg
      intro ω
      change 0 ≤ X i ω ^ (2 * n)
      rw [pow_mul]
      exact pow_nonneg (sq_nonneg _) _
    · positivity
  have hB := bandEvenMajorant_coeff_nonneg ha hu hs hc₂ hc₃
  have hle : ∀ i ∈ I, ∀ n, coeff n (evenMomentSeries (X i) μ) ≤
      coeff n (bandEvenMajorant a u s c₂ c₃) :=
    fun i _ n => evenMomentSeries_coeff_le (hvar i) (hfour i) (hhigh i) n
  refine ⟨hInt, ?_, ?_⟩
  · intro n
    have heq := congrArg (coeff (2 * n + 1)) hserEven
    rw [momentSeries, coeff_mk, coeff_expand_of_not_dvd _ _ _ (by omega)] at heq
    have h := congrArg (fun z : ℝ => z * (2 * n + 1).factorial) heq
    simpa only [div_mul_cancel₀ _ (by positivity : ((2 * n + 1).factorial : ℝ) ≠ 0), zero_mul] using h
  · intro n
    have heq := congrArg (coeff (2 * n)) hserEven
    rw [momentSeries, coeff_mk, coeff_expand_mul] at heq
    have hbound := coeff_finset_prod_le_pow I (fun i => evenMomentSeries (X i) μ)
      (bandEvenMajorant a u s c₂ c₃) hfpos hB hle n
    rw [bandMajorant_pow_even_coeff]
    have h := (div_le_iff₀ (by positivity : (0 : ℝ) < (2 * n).factorial)).mp (heq.trans_le hbound)
    simpa only [mul_comm] using h

end GMCExplicitDelta.Source
