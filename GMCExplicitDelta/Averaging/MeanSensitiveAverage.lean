module

public import GMCExplicitDelta.Averaging.MeanSensitiveCount
public import GMCExplicitDelta.Averaging.MeanSensitiveMoments
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Mean-sensitive moment bound for averages (A3)
-/

@[expose] public section

namespace GMCExplicitDelta.Averaging

open Finset MeasureTheory ProbabilityTheory

section Index

variable {p n : ℕ}

theorem cnt_eq_card (f : Fin p → Fin n) (a : Fin n) :
    cnt f a = (univ.filter fun j => f j = a).card := (Finset.card_filter _ _).symm

theorem sum_cnt (f : Fin p → Fin n) : ∑ a, cnt f a = p := by
  unfold cnt
  rw [Finset.sum_comm]
  simp

theorem cnt_le (f : Fin p → Fin n) (a : Fin n) : cnt f a ≤ p := by
  rw [cnt_eq_card]
  calc _ ≤ (univ : Finset (Fin p)).card := card_le_univ _
    _ = p := by simp

theorem prod_eq_prod_pow (y : Fin n → ℝ) (f : Fin p → Fin n) :
    ∏ j, y (f j) = ∏ a, y a ^ cnt f a := by
  rw [Finset.prod_comp y f]
  simp only [cnt_eq_card]
  refine Finset.prod_subset (subset_univ _) fun a _ ha => ?_
  have : (univ.filter fun j => f j = a) = ∅ := by
    ext j; simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false]
    intro hj; exact ha (mem_image.2 ⟨j, mem_univ _, hj⟩)
  rw [this]; simp

theorem prod_eq_prod_supp (y : Fin n → ℝ) (f : Fin p → Fin n) :
    ∏ a, y a ^ cnt f a = ∏ a ∈ supp f, y a ^ cnt f a := by
  symm
  refine Finset.prod_subset (subset_univ _) fun a _ ha => ?_
  have : cnt f a = 0 := by
    simpa [supp] using ha
  rw [this]; simp

theorem sum_supp_cnt (f : Fin p → Fin n) : ∑ a ∈ supp f, cnt f a = p := by
  refine (Finset.sum_subset (subset_univ _) fun a _ ha => ?_).trans (sum_cnt f)
  simpa [supp] using ha

theorem two_mul_card_supp_le {f : Fin p → Fin n} (h : NoSingleton f) :
    2 * (supp f).card ≤ p := by
  have h1 : ∑ _a ∈ supp f, 2 ≤ ∑ a ∈ supp f, cnt f a := by
    refine Finset.sum_le_sum fun a ha => ?_
    have h0 : 0 < cnt f a := by simpa [supp] using ha
    have := h a
    omega
  rw [Finset.sum_const, smul_eq_mul, sum_supp_cnt f, mul_comm] at h1
  exact h1

theorem one_le_card_supp {p n : ℕ} (hp : 0 < p) (f : Fin p → Fin n) : 1 ≤ (supp f).card := by
  have : f ⟨0, hp⟩ ∈ supp f := by
    simp only [supp, mem_filter, mem_univ, true_and]
    have : (if f ⟨0, hp⟩ = f ⟨0, hp⟩ then 1 else 0) ≤ cnt f (f ⟨0, hp⟩) :=
      Finset.single_le_sum (f := fun j => if f j = f ⟨0, hp⟩ then 1 else 0)
        (fun _ _ => Nat.zero_le _) (mem_univ _)
    simp at this
    omega
  exact Finset.card_pos.2 ⟨_, this⟩

/-- The deterministic counting bound. -/
theorem sum_noSingleton_le (hp : 0 < p) {T : ℝ} (hT : 0 ≤ T) :
    ∑ f : Fin p → Fin n, (if NoSingleton f then T ^ ((supp f).card - 1) else 0) ≤
      ∑ k ∈ Icc 1 (p / 2), (assocStirling p k : ℝ) * (n : ℝ) ^ k * T ^ (k - 1) := by
  rw [← Finset.sum_filter]
  have hmaps : ∀ f ∈ (univ.filter fun f : Fin p → Fin n => NoSingleton f),
      (supp f).card ∈ Icc 1 (p / 2) := by
    intro f hf
    have hf' := (mem_filter.1 hf).2
    rw [mem_Icc]
    exact ⟨one_le_card_supp hp f, (Nat.le_div_iff_mul_le (by norm_num)).2
      (by have := two_mul_card_supp_le hf'; omega)⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_le_sum fun k hk => ?_
  have : ∑ f ∈ (univ.filter fun f : Fin p → Fin n => NoSingleton f) with (supp f).card = k,
      T ^ ((supp f).card - 1) = (goodCount p n k : ℝ) * T ^ (k - 1) := by
    rw [Finset.sum_congr rfl (g := fun _ => T ^ (k - 1))
      (fun f hf => by rw [(mem_filter.1 hf).2]), Finset.sum_const, nsmul_eq_mul]
    congr 2
    unfold goodCount
    rw [Finset.filter_filter]
  rw [this]
  have := goodCount_le p n k
  have h2 : (goodCount p n k : ℝ) ≤ (assocStirling p k : ℝ) * (n : ℝ) ^ k := by exact_mod_cast this
  exact mul_le_mul_of_nonneg_right h2 (pow_nonneg hT _)

end Index

variable {p n : ℕ}

theorem pow_sum_eq_sum_prod (y : Fin n → ℝ) :
    (∑ i, y i) ^ p = ∑ f : Fin p → Fin n, ∏ j, y (f j) := by
  have h1 : (∑ i, y i) ^ p = ∏ _j : Fin p, ∑ i, y i := by simp
  rw [h1, Finset.prod_univ_sum (fun _ : Fin p => (univ : Finset (Fin n))) (fun _ i => y i),
    Fintype.piFinset_univ]

theorem abs_prod_le (hp : 0 < p) (y : Fin n → ℝ) (f : Fin p → Fin n) :
    |∏ j, y (f j)| ≤ ∑ i, |y i| ^ p := by
  rw [Finset.abs_prod]
  obtain ⟨j0, -, hj0⟩ := Finset.exists_max_image univ (fun j => |y (f j)|)
    ⟨⟨0, hp⟩, mem_univ _⟩
  calc ∏ j, |y (f j)| ≤ ∏ _j : Fin p, |y (f j0)| :=
        Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun j _ => hj0 j (mem_univ _)
    _ = |y (f j0)| ^ p := by simp
    _ ≤ ∑ i, |y i| ^ p :=
        Finset.single_le_sum (f := fun i => |y i| ^ p) (fun _ _ => pow_nonneg (abs_nonneg _) _)
          (mem_univ (f j0))

section Prob

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Fin n → Ω → ℝ}

omit [IsProbabilityMeasure μ] in
theorem indep_centered (hind : iIndepFun X μ) (_hmeas : ∀ i, Measurable (X i)) :
    iIndepFun (fun i ω => X i ω - ∫ ω', X i ω' ∂μ) μ :=
  hind.comp (fun i x => x - ∫ ω', X i ω' ∂μ) (fun _ => measurable_id.sub_const _)

theorem integral_prod_centered (hind : iIndepFun X μ) (hmeas : ∀ i, Measurable (X i))
    (f : Fin p → Fin n) :
    ∫ ω, ∏ j, (X (f j) ω - ∫ ω', X (f j) ω' ∂μ) ∂μ =
      ∏ a, ∫ ω, (X a ω - ∫ ω', X a ω' ∂μ) ^ cnt f a ∂μ := by
  have hY := indep_centered hind hmeas
  have hZ : iIndepFun (fun a ω => (X a ω - ∫ ω', X a ω' ∂μ) ^ cnt f a) μ :=
    hY.comp (fun a y => y ^ cnt f a) (fun _ => measurable_id.pow_const _)
  have := hZ.integral_fun_prod_eq_prod_integral
    (fun a => (((hmeas a).sub_const _).pow_const _).aestronglyMeasurable)
  have e : (fun ω => ∏ j, (X (f j) ω - ∫ ω', X (f j) ω' ∂μ)) =
      fun ω => ∏ a, (X a ω - ∫ ω', X a ω' ∂μ) ^ cnt f a :=
    funext fun ω => prod_eq_prod_pow (fun a => X a ω - ∫ ω', X a ω' ∂μ) f
  rw [e]
  exact this

end Prob

/-- Hypotheses of the mean-sensitive averaging bound: `X i` are independent nonnegative random
variables with `E X i ≤ F`, `E (X i)^p ≤ D^p`, and `T ≥ ϖ^(p/(p-1))`, `ϖ = min (F/D) 1`. -/
structure AvgHyp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {n : ℕ} (X : Fin n → Ω → ℝ)
    (p : ℕ) (F D T : ℝ) : Prop where
  two_le : 2 ≤ p
  F_pos : 0 < F
  D_pos : 0 < D
  indep : iIndepFun X μ
  meas : ∀ i, Measurable (X i)
  nonneg : ∀ i ω, 0 ≤ X i ω
  integrable : ∀ i, Integrable (fun ω => X i ω ^ p) μ
  mean_le : ∀ i, ∫ ω, X i ω ∂μ ≤ F
  moment_le : ∀ i, ∫ ω, X i ω ^ p ∂μ ≤ D ^ p
  T_ge : (min (F / D) 1) ^ ((p : ℝ) / ((p : ℝ) - 1)) ≤ T

section Main

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Fin n → Ω → ℝ} {F D T : ℝ}

omit [IsProbabilityMeasure μ] in
theorem AvgHyp.T_pos (h : AvgHyp μ X p F D T) : 0 < T :=
  lt_of_lt_of_le (Real.rpow_pos_of_pos (lt_min (div_pos h.F_pos h.D_pos) one_pos) _) h.T_ge

theorem integrable_prod_centered (h : AvgHyp μ X p F D T) (f : Fin p → Fin n) :
    Integrable (fun ω => ∏ j, (X (f j) ω - ∫ ω', X (f j) ω' ∂μ)) μ := by
  have hp0 : 0 < p := by have := h.two_le; omega
  refine Integrable.mono' (g := fun ω => ∑ i, |X i ω - ∫ ω', X i ω' ∂μ| ^ p)
    (integrable_finsetSum _ fun i _ =>
      integrable_centered_pow h.two_le le_rfl (h.nonneg i) (h.meas i) (h.integrable i))
    (Finset.measurable_prod _ fun j _ => (h.meas (f j)).sub_const _).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  exact abs_prod_le hp0 (fun i => X i ω - ∫ ω', X i ω' ∂μ) f

theorem integral_prod_centered_eq_zero (h : AvgHyp μ X p F D T) {f : Fin p → Fin n}
    (hf : ¬ NoSingleton f) : ∫ ω, ∏ j, (X (f j) ω - ∫ ω', X (f j) ω' ∂μ) ∂μ = 0 := by
  obtain ⟨a, ha⟩ : ∃ a, cnt f a = 1 := by
    by_contra hne
    exact hf fun a ha => hne ⟨a, ha⟩
  rw [integral_prod_centered h.indep h.meas f]
  refine Finset.prod_eq_zero (mem_univ a) ?_
  have hi : Integrable (fun ω => X a ω) μ := by
    simpa using integrable_pow_of_le (r := 1) (by have := h.two_le; omega) (h.nonneg a)
      (h.meas a) (h.integrable a)
  rw [ha]
  simp only [pow_one]
  rw [integral_sub hi (integrable_const _)]
  simp

theorem abs_integral_prod_centered_le (h : AvgHyp μ X p F D T) {f : Fin p → Fin n}
    (hf : NoSingleton f) :
    |∫ ω, ∏ j, (X (f j) ω - ∫ ω', X (f j) ω' ∂μ) ∂μ| ≤ D ^ p * T ^ ((supp f).card - 1) := by
  have hp0 : 0 < p := by have := h.two_le; omega
  have hTp := h.T_pos
  rw [integral_prod_centered h.indep h.meas f, Finset.abs_prod]
  have hsub : ∏ a, |∫ ω, (X a ω - ∫ ω', X a ω' ∂μ) ^ cnt f a ∂μ| =
      ∏ a ∈ supp f, |∫ ω, (X a ω - ∫ ω', X a ω' ∂μ) ^ cnt f a ∂μ| := by
    symm
    refine Finset.prod_subset (subset_univ _) fun a _ ha => ?_
    have : cnt f a = 0 := by simpa [supp] using ha
    simp [this]
  rw [hsub]
  have hbound : ∀ a ∈ supp f, |∫ ω, (X a ω - ∫ ω', X a ω' ∂μ) ^ cnt f a ∂μ| ≤
      D ^ cnt f a * T ^ (((p : ℝ) - cnt f a) / p) := by
    intro a ha
    have h0 : 0 < cnt f a := by simpa [supp] using ha
    have h1 := hf a
    have h2 : 2 ≤ cnt f a := by omega
    calc _ ≤ ∫ ω, |(X a ω - ∫ ω', X a ω' ∂μ) ^ cnt f a| ∂μ := abs_integral_le_integral_abs
      _ = ∫ ω, |X a ω - ∫ ω', X a ω' ∂μ| ^ cnt f a ∂μ := by simp only [abs_pow]
      _ ≤ _ := centered_moment_le_T h.two_le h2 (cnt_le f a) h.F_pos h.D_pos (h.nonneg a)
          (h.meas a) (h.integrable a) (h.mean_le a) (h.moment_le a) h.T_ge
  refine (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) hbound).trans (le_of_eq ?_)
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, sum_supp_cnt,
    ← Real.rpow_sum_of_pos hTp]
  have hk := one_le_card_supp hp0 f
  have hp0' : (0 : ℝ) < p := by exact_mod_cast hp0
  have hsum : ∑ a ∈ supp f, (((p : ℝ) - cnt f a) / p) = (((supp f).card - 1 : ℕ) : ℝ) := by
    rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Nat.cast_sum, sum_supp_cnt, Nat.cast_sub hk]
    field_simp
    simp
  rw [hsum, Real.rpow_natCast]

theorem integral_pow_sum_centered_le (h : AvgHyp μ X p F D T) :
    ∫ ω, (∑ i, (X i ω - ∫ ω', X i ω' ∂μ)) ^ p ∂μ ≤
      D ^ p * ∑ k ∈ Icc 1 (p / 2), (assocStirling p k : ℝ) * (n : ℝ) ^ k * T ^ (k - 1) := by
  have hp0 : 0 < p := by have := h.two_le; omega
  have hTp := h.T_pos
  simp only [pow_sum_eq_sum_prod]
  rw [integral_finsetSum _ fun f _ => integrable_prod_centered h f]
  calc _ ≤ ∑ f : Fin p → Fin n, (if NoSingleton f then D ^ p * T ^ ((supp f).card - 1) else 0) := by
        refine Finset.sum_le_sum fun f _ => ?_
        by_cases hf : NoSingleton f
        · rw [if_pos hf]; exact (le_abs_self _).trans (abs_integral_prod_centered_le h hf)
        · rw [if_neg hf, integral_prod_centered_eq_zero h hf]
    _ = D ^ p * ∑ f : Fin p → Fin n, (if NoSingleton f then T ^ ((supp f).card - 1) else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun f _ => ?_
        split_ifs <;> simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_noSingleton_le hp0 hTp.le)
        (pow_nonneg h.D_pos.le _)

end Main

/-- `B̄_p(n)^p = ∑_{k=1}^{p/2} 𝒜(p,k) n^(k-p) T^(k-1)`, for real `n`, `T`. -/
noncomputable def avgBoundPow (p : ℕ) (n T : ℝ) : ℝ :=
  ∑ k ∈ Icc 1 (p / 2), (assocStirling p k : ℝ) * n ^ ((k : ℤ) - p) * T ^ (k - 1)

/-- `B̄_p(n)`. -/
noncomputable def avgBound (p : ℕ) (n T : ℝ) : ℝ := avgBoundPow p n T ^ ((1 : ℝ) / p)

section Main2

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Fin n → Ω → ℝ} {F D T : ℝ}

/-- **A3.** `E[(n⁻¹ ∑ (X i - E X i))^p] ≤ D^p B̄_p(n)^p`. -/
theorem mean_sensitive_average (h : AvgHyp μ X p F D T) (hn : 0 < n) :
    ∫ ω, ((n : ℝ)⁻¹ * ∑ i, (X i ω - ∫ ω', X i ω' ∂μ)) ^ p ∂μ ≤
      D ^ p * avgBoundPow p n T := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [mul_pow]
  rw [integral_const_mul]
  have := integral_pow_sum_centered_le h
  calc _ ≤ ((n : ℝ)⁻¹) ^ p * (D ^ p * ∑ k ∈ Icc 1 (p / 2),
        (assocStirling p k : ℝ) * (n : ℝ) ^ k * T ^ (k - 1)) :=
        mul_le_mul_of_nonneg_left this (pow_nonneg (inv_nonneg.2 hn'.le) _)
    _ = _ := by
        unfold avgBoundPow
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hkp : k ≤ p := (mem_Icc.1 hk).2.trans (Nat.div_le_self _ _)
        rw [show ((k : ℤ) - p) = -((p - k : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast]
        have : (n : ℝ) ^ p = (n : ℝ) ^ (p - k) * (n : ℝ) ^ k := by
          rw [← pow_add]; congr 1; omega
        rw [inv_pow, this]
        field_simp

theorem avgBoundPow_nonneg {n T : ℝ} (hn : 0 ≤ n) (hT : 0 ≤ T) : 0 ≤ avgBoundPow p n T :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (zpow_nonneg hn _))
    (pow_nonneg hT _)

/-- **A3** in norm form: for even `p`, `‖n⁻¹ ∑ (X i - E X i)‖_p ≤ D B̄_p(n)`. -/
theorem mean_sensitive_average_norm (h : AvgHyp μ X p F D T) (hn : 0 < n) (hev : Even p) :
    (∫ ω, |(n : ℝ)⁻¹ * ∑ i, (X i ω - ∫ ω', X i ω' ∂μ)| ^ p ∂μ) ^ ((1 : ℝ) / p) ≤
      D * avgBound p n T := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by have := h.two_le; omega : 0 < p)
  simp only [hev.pow_abs]
  have h1 := mean_sensitive_average h hn
  have h2 : 0 ≤ ∫ ω, ((n : ℝ)⁻¹ * ∑ i, (X i ω - ∫ ω', X i ω' ∂μ)) ^ p ∂μ :=
    integral_nonneg fun ω => hev.pow_nonneg _
  have hB := avgBoundPow_nonneg (p := p) hn'.le h.T_pos.le
  refine (Real.rpow_le_rpow h2 h1 (by positivity)).trans (le_of_eq ?_)
  rw [Real.mul_rpow (pow_nonneg h.D_pos.le _) hB, ← Real.rpow_natCast, ← Real.rpow_mul h.D_pos.le]
  unfold avgBound
  rw [mul_one_div_cancel hp0.ne', Real.rpow_one]

/-- `B̄_p(n)^p` is nonincreasing in `n`. -/
theorem avgBoundPow_antitone {n m T : ℝ} (hn : 0 < n) (hnm : n ≤ m) (hT : 0 ≤ T) :
    avgBoundPow p m T ≤ avgBoundPow p n T := by
  unfold avgBoundPow
  refine Finset.sum_le_sum fun k hk => ?_
  have hkp : k ≤ p := (mem_Icc.1 hk).2.trans (Nat.div_le_self _ _)
  rw [show ((k : ℤ) - p) = -((p - k : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast, zpow_neg,
    zpow_natCast]
  gcongr

/-- `B̄_p(n)^p` is nondecreasing in `T`. -/
theorem avgBoundPow_mono_T {n T T' : ℝ} (hn : 0 ≤ n) (hT : 0 ≤ T) (hTT : T ≤ T') :
    avgBoundPow p n T ≤ avgBoundPow p n T' := by
  unfold avgBoundPow
  refine Finset.sum_le_sum fun k _ => ?_
  have := zpow_nonneg hn ((k : ℤ) - p)
  gcongr

theorem avgBound_antitone {n m T : ℝ} (hn : 0 < n) (hnm : n ≤ m) (hT : 0 ≤ T) :
    avgBound p m T ≤ avgBound p n T := by
  unfold avgBound
  exact Real.rpow_le_rpow (avgBoundPow_nonneg (hn.le.trans hnm) hT)
    (avgBoundPow_antitone hn hnm hT) (by positivity)

theorem avgBound_mono_T {n T T' : ℝ} (hn : 0 ≤ n) (hT : 0 ≤ T) (hTT : T ≤ T') :
    avgBound p n T ≤ avgBound p n T' := by
  unfold avgBound
  exact Real.rpow_le_rpow (avgBoundPow_nonneg hn hT) (avgBoundPow_mono_T hn hT hTT) (by positivity)

/-- Scaling of `B̄_p(n)^p`: `B̄_p(cn)^p ≤ c^(-p/2) B̄_p(n)^p` for `c ≥ 1`, `p` even. -/
theorem avgBoundPow_scale (hev : Even p) {n c T : ℝ} (hn : 0 < n) (hc : 1 ≤ c) (hT : 0 ≤ T) :
    avgBoundPow p (c * n) T ≤ c ^ (-((p / 2 : ℕ) : ℤ)) * avgBoundPow p n T := by
  unfold avgBoundPow
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k hk => ?_
  have hk2 : k ≤ p / 2 := (mem_Icc.1 hk).2
  obtain ⟨q, hq⟩ := hev
  have hc0 : 0 < c := by linarith
  have hpq : p / 2 = q := by omega
  have h1 : c ^ ((k : ℤ) - p) ≤ c ^ (-((p / 2 : ℕ) : ℤ)) :=
    zpow_le_zpow_right₀ hc (by omega)
  rw [mul_zpow]
  have h2 : 0 ≤ (assocStirling p k : ℝ) * n ^ ((k : ℤ) - p) * T ^ (k - 1) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (zpow_nonneg hn.le _)) (pow_nonneg hT _)
  calc (assocStirling p k : ℝ) * (c ^ ((k : ℤ) - p) * n ^ ((k : ℤ) - p)) * T ^ (k - 1)
      = c ^ ((k : ℤ) - p) * ((assocStirling p k : ℝ) * n ^ ((k : ℤ) - p) * T ^ (k - 1)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h1 h2 |>.trans (le_of_eq (by ring))

/-- `B̄_p(cn) ≤ c^(-1/2) B̄_p(n)` for `c ≥ 1` and even `p`. -/
theorem avgBound_scale (hev : Even p) (hp : 0 < p) {n c T : ℝ} (hn : 0 < n) (hc : 1 ≤ c)
    (hT : 0 ≤ T) : avgBound p (c * n) T ≤ c ^ (-(1 / 2 : ℝ)) * avgBound p n T := by
  have hc0 : 0 < c := by linarith
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  unfold avgBound
  have hB := avgBoundPow_nonneg (p := p) hn.le hT
  refine (Real.rpow_le_rpow (avgBoundPow_nonneg (by positivity) hT)
    (avgBoundPow_scale hev hn hc hT) (by positivity)).trans (le_of_eq ?_)
  rw [Real.mul_rpow (zpow_nonneg hc0.le _) hB]
  congr 1
  obtain ⟨q, hq⟩ := hev
  have hpq : p / 2 = q := by omega
  rw [hpq, ← Real.rpow_intCast, ← Real.rpow_mul hc0.le]
  congr 1
  have : (p : ℝ) = 2 * q := by exact_mod_cast (by omega : p = 2 * q)
  have hq0 : (0 : ℝ) < q := by
    have : (0 : ℝ) < 2 * q := this ▸ hp0
    linarith
  push_cast
  rw [this]; field_simp

end Main2

end GMCExplicitDelta.Averaging
