module

public import GMCExplicitDelta.Source.EndpointStripMoments

/-!
# The law of the zero layer at a point, and sign averaging
-/

@[expose] public section

namespace GMCExplicitDelta.Source

open Homogenization MeasureTheory ProbabilityTheory
open SubdiffusiveProcess.Model SubdiffusiveProcess.Model.PotentialField

variable {d : ℕ} {δ : ℝ} {μ : Measure (PotentialField d)} [IsProbabilityMeasure μ]

/-- The law of `g 0` under `μ`. -/
noncomputable def lawZero (μ : Measure (PotentialField d)) : Measure ℝ :=
  μ.map (fun g : PotentialField d => g 0)

theorem measurable_eval0 : Measurable (fun g : PotentialField d => g 0) :=
  (continuous_eval 0).measurable

instance : IsProbabilityMeasure (lawZero μ) :=
  ⟨by unfold lawZero; rw [Measure.map_apply measurable_eval0 MeasurableSet.univ]; simp⟩

theorem map_eval_eq (hS : ∀ z : Vec d, Measure.map (translate z) μ = μ) (z : Vec d) :
    μ.map (fun g : PotentialField d => g z) = lawZero μ := by
  unfold lawZero
  conv_rhs => rw [← hS z]
  rw [Measure.map_map measurable_eval0 (measurable_translate z)]
  congr 1
  ext g
  simp [Function.comp_def, translate_apply]

theorem lawZero_neg (hN : Measure.map (negate (d := d)) μ = μ) :
    (lawZero μ).map (fun x : ℝ => -x) = lawZero μ := by
  unfold lawZero
  rw [Measure.map_map measurable_neg measurable_eval0]
  conv_rhs => rw [← hN]
  rw [Measure.map_map measurable_eval0 measurable_negate]
  congr 1
  ext g
  simp [Function.comp_def]

theorem EndpointModel.law_XY (M : EndpointModel d δ μ) :
    μ.map (fun g : PotentialField d => (epX g, epY g)) = (lawZero μ).prod (lawZero μ) := by
  have h1 := (indep_endpoints M.dim_pos M.indep).1
  have hXY : IndepFun epX epY μ := by
    have := h1.comp (measurable_fst) measurable_id
    exact this
  rw [(indepFun_iff_map_prod_eq_prod_map_map measurable_epX.aemeasurable
    measurable_epY.aemeasurable).1 hXY]
  have hx : μ.map (epX (d := d)) = lawZero μ := map_eval_eq M.stat (diagPt d 0)
  have hy : μ.map (epY (d := d)) = lawZero μ := map_eval_eq M.stat (diagPt d 1)
  rw [hx, hy]

/-- The flip `y ↦ -y` preserves the product of the symmetric law. -/
theorem prod_flip (hN : Measure.map (negate (d := d)) μ = μ) :
    ((lawZero μ).prod (lawZero μ)).map (Prod.map id (fun y : ℝ => -y)) =
      (lawZero μ).prod (lawZero μ) := by
  have := Measure.map_prod_map (lawZero μ) (lawZero μ) (measurable_id) (measurable_neg)
  rw [Measure.map_id, lawZero_neg hN] at this
  exact this.symm


/-- Exponential moment of the zero layer. -/
theorem EndpointModel.nu_exp (M : EndpointModel d δ μ) :
    Integrable (fun x : ℝ => Real.exp ((1 + stripK) ^ 2 * x ^ 2 / δ ^ 2)) (lawZero μ) ∧
      ∫ x, Real.exp ((1 + stripK) ^ 2 * x ^ 2 / δ ^ 2) ∂(lawZero μ) ≤ Real.sqrt 3 := by
  set ν := lawZero μ with hν
  have hδ := M.delta_pos
  set E : ℝ × ℝ → ENNReal := fun p => ENNReal.ofReal (Real.exp (envelope p.1 p.2 ^ 2 / δ ^ 2))
    with hE
  have hEm : Measurable E := by
    rw [hE]
    exact ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp ((measurable_envelope.pow_const 2).div_const _))
  set A : ℝ → ENNReal := fun x => ENNReal.ofReal (Real.exp ((1 + stripK) ^ 2 * x ^ 2 / δ ^ 2)) with hA
  have hAm : Measurable A := by
    rw [hA]
    exact ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (((measurable_id.pow_const 2).const_mul _).div_const _))
  have hpair : Measurable (fun g : PotentialField d => (epX g, epY g)) :=
    measurable_epX.prodMk measurable_epY
  have h1 : ∫⁻ p, E p ∂(ν.prod ν) ≤ 2 := by
    rw [← M.law_XY, lintegral_map hEm hpair]
    exact jensen_exp M
  have hflip : ∫⁻ p, E (p.1, -p.2) ∂(ν.prod ν) = ∫⁻ p, E p ∂(ν.prod ν) := by
    have hT : Measurable (Prod.map (id : ℝ → ℝ) (fun y : ℝ => -y)) :=
      measurable_id.prodMap measurable_neg
    have := lintegral_map hEm hT (μ := ν.prod ν)
    rw [prod_flip M.neg] at this
    exact this.symm
  have hE' : Measurable (fun p : ℝ × ℝ => E (p.1, -p.2)) :=
    hEm.comp (measurable_fst.prodMk measurable_snd.neg)
  have hpt : ∀ p : ℝ × ℝ, 1 + A p.1 * A p.2 ≤ E p + E (p.1, -p.2) := by
    intro p
    have h := exp_envelope_sum hδ p.1 p.2
    have ha := (Real.exp_pos ((1 + stripK) ^ 2 * p.1 ^ 2 / δ ^ 2)).le
    have hb := (Real.exp_pos ((1 + stripK) ^ 2 * p.2 ^ 2 / δ ^ 2)).le
    have he1 := (Real.exp_pos (envelope p.1 p.2 ^ 2 / δ ^ 2)).le
    have he2 := (Real.exp_pos (envelope p.1 (-p.2) ^ 2 / δ ^ 2)).le
    calc 1 + A p.1 * A p.2
        = ENNReal.ofReal (1 + Real.exp ((1 + stripK) ^ 2 * p.1 ^ 2 / δ ^ 2) *
            Real.exp ((1 + stripK) ^ 2 * p.2 ^ 2 / δ ^ 2)) := by
          rw [ENNReal.ofReal_add zero_le_one (mul_nonneg ha hb), ENNReal.ofReal_mul ha]
          simp [hA]
      _ ≤ ENNReal.ofReal (Real.exp (envelope p.1 p.2 ^ 2 / δ ^ 2) +
            Real.exp (envelope p.1 (-p.2) ^ 2 / δ ^ 2)) := ENNReal.ofReal_le_ofReal h
      _ = E p + E (p.1, -p.2) := by
          rw [ENNReal.ofReal_add he1 he2]
  have h2 : ∫⁻ p, (1 + A p.1 * A p.2) ∂(ν.prod ν) ≤ 4 := by
    calc _ ≤ ∫⁻ p, (E p + E (p.1, -p.2)) ∂(ν.prod ν) := lintegral_mono hpt
      _ = ∫⁻ p, E p ∂(ν.prod ν) + ∫⁻ p, E (p.1, -p.2) ∂(ν.prod ν) := lintegral_add_left hEm _
      _ = 2 * ∫⁻ p, E p ∂(ν.prod ν) := by rw [hflip, two_mul]
      _ ≤ 2 * 2 := by gcongr
      _ = 4 := by norm_num
  set Mx : ENNReal := ∫⁻ x, A x ∂ν with hMx
  have h3 : ∫⁻ p, (1 + A p.1 * A p.2) ∂(ν.prod ν) = 1 + Mx * Mx := by
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
      lintegral_prod_mul hAm.aemeasurable hAm.aemeasurable]
  rw [h3] at h2
  have h4 : Mx * Mx ≤ 3 := by
    have : (1 : ENNReal) + Mx * Mx ≤ 1 + 3 := by
      refine h2.trans ?_; norm_num
    exact (ENNReal.add_le_add_iff_left (by simp)).1 this
  have hMtop : Mx ≠ ⊤ := by
    intro h; rw [h] at h4; simp at h4
  have hm : Mx.toReal ^ 2 ≤ 3 := by
    have := ENNReal.toReal_mono (by simp) h4
    rw [ENNReal.toReal_mul] at this
    simpa [sq] using this
  have hint : Integrable (fun x : ℝ => Real.exp ((1 + stripK) ^ 2 * x ^ 2 / δ ^ 2)) ν := by
    rw [← lintegral_ofReal_ne_top_iff_integrable]
    · exact hMtop
    · exact (Real.measurable_exp.comp (((measurable_id.pow_const 2).const_mul _).div_const _)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x => (Real.exp_pos _).le
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)
    hint.aestronglyMeasurable]
  have := Real.abs_le_sqrt hm
  rw [abs_of_nonneg ENNReal.toReal_nonneg] at this
  exact this


theorem three_le_stripK : 3 ≤ stripK := by
  unfold stripK; nlinarith [Real.sqrt_nonneg 2]

/-- Second moment of the zero layer. -/
theorem EndpointModel.nu_sq (M : EndpointModel d δ μ) :
    Integrable (fun x : ℝ => x ^ 2) (lawZero μ) ∧
      (1 + stripK) ^ 2 * ∫ x, x ^ 2 ∂(lawZero μ) ≤ δ ^ 2 / 2 := by
  set ν := lawZero μ with hν
  have hδ := M.delta_pos
  have hW2 := M.W_facts.2.1
  have hx2 : Integrable (fun x : ℝ => x ^ 2) ν := by
    rw [hν, lawZero, integrable_map_measure
      (by fun_prop : Measurable (fun x : ℝ => x ^ 2)).aestronglyMeasurable
      measurable_eval0.aemeasurable]
    refine hW2.mono' ((measurable_eval0.pow_const 2).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun g => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h0 : (0 : Vec d) ∈ openCubeSet (originCube d 0) := by
      simpa using zero_smul_mem_openCube (d := d) (t := 0) (by norm_num)
    have := abs_apply_le_g2Observable g h0
    show (g 0) ^ 2 ≤ g2Observable g ^ 2
    exact (sq_abs _).symm.le.trans (pow_le_pow_left₀ (abs_nonneg _) this 2)
  obtain ⟨hΦi, hΦb⟩ := M.envelope_sq_bound
  set Φ : ℝ × ℝ → ℝ := fun p => envelope p.1 p.2 ^ 2 with hΦ
  have hΦm : Measurable Φ := measurable_envelope.pow_const 2
  have hpair : Measurable (fun g : PotentialField d => (epX g, epY g)) :=
    measurable_epX.prodMk measurable_epY
  have hΦint : Integrable Φ (ν.prod ν) := by
    rw [← M.law_XY, integrable_map_measure hΦm.aestronglyMeasurable hpair.aemeasurable]
    exact hΦi
  have hΦval : ∫ p, Φ p ∂(ν.prod ν) ≤ δ ^ 2 * Real.log 2 := by
    rw [← M.law_XY, integral_map hpair.aemeasurable hΦm.aestronglyMeasurable]
    exact hΦb
  have hT : Measurable (Prod.map (id : ℝ → ℝ) (fun y : ℝ => -y)) :=
    measurable_id.prodMap measurable_neg
  have hΦ'int : Integrable (fun p : ℝ × ℝ => Φ (p.1, -p.2)) (ν.prod ν) := by
    have := (integrable_map_measure (μ := ν.prod ν) hΦm.aestronglyMeasurable hT.aemeasurable).1
      (by rw [prod_flip M.neg]; exact hΦint)
    exact this
  have hflip : ∫ p, Φ (p.1, -p.2) ∂(ν.prod ν) = ∫ p, Φ p ∂(ν.prod ν) := by
    have := integral_map (μ := ν.prod ν) hT.aemeasurable hΦm.aestronglyMeasurable
    rw [prod_flip M.neg] at this
    exact this.symm
  have hsq : Integrable (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) (ν.prod ν) :=
    (hx2.comp_fst ν).add (hx2.comp_snd ν)
  have hlow : ∫ p, (((1 + stripK) ^ 2 + stripK ^ 2) * (p.1 ^ 2 + p.2 ^ 2)) ∂(ν.prod ν) ≤
      ∫ p, (Φ p + Φ (p.1, -p.2)) ∂(ν.prod ν) :=
    integral_mono (hsq.const_mul _) (hΦint.add hΦ'int) fun p => envelope_sq_sum p.1 p.2
  rw [integral_add hΦint hΦ'int, hflip, integral_const_mul, integral_add (hx2.comp_fst ν) (hx2.comp_snd ν),
    integral_fun_fst (fun x : ℝ => x ^ 2), integral_fun_snd (fun x : ℝ => x ^ 2)] at hlow
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at hlow
  set S := ∫ x, x ^ 2 ∂ν with hS
  have hS0 : 0 ≤ S := integral_nonneg fun x => sq_nonneg x
  have hlog : Real.log 2 ≤ 3 / 4 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have := Real.quadratic_le_exp_of_nonneg (show (0:ℝ) ≤ 3 / 4 by norm_num)
    linarith
  have hK := three_le_stripK
  have hα : 3 * (1 + stripK) ^ 2 ≤ 2 * ((1 + stripK) ^ 2 + stripK ^ 2) := by nlinarith
  have h1 : ((1 + stripK) ^ 2 + stripK ^ 2) * S ≤ δ ^ 2 * (3 / 4) := by
    have : ((1 + stripK) ^ 2 + stripK ^ 2) * (S + S) ≤ 2 * (δ ^ 2 * Real.log 2) := by
      calc _ ≤ _ := hlow
        _ ≤ 2 * (δ ^ 2 * Real.log 2) := by linarith
    have h5 : δ ^ 2 * Real.log 2 ≤ δ ^ 2 * (3 / 4) := mul_le_mul_of_nonneg_left hlog (sq_nonneg δ)
    nlinarith
  refine ⟨hx2, ?_⟩
  nlinarith [mul_le_mul_of_nonneg_right hα hS0]

end GMCExplicitDelta.Source
