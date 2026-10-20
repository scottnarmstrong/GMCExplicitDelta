module

public import GMCExplicitDelta.Source.EndpointStripCenter
public import GMCExplicitDelta.Source.EndpointStripCenterExt
public import GMCExplicitDelta.Source.EndpointStripIndep

/-!
# Centering of the endpoint derivative sum against functions of both endpoint values
-/

@[expose] public section

namespace GMCExplicitDelta.Source

open Homogenization MeasureTheory ProbabilityTheory
open SubdiffusiveProcess.Model SubdiffusiveProcess.Model.PotentialField

variable {d : ℕ}

theorem measurable_epX : Measurable (epX (d := d)) := (continuous_eval _).measurable
theorem measurable_epY : Measurable (epY (d := d)) := (continuous_eval _).measurable
theorem measurable_epP : Measurable (epP (d := d)) :=
  ((continuous_eval_deriv _).clm_apply continuous_const).measurable
theorem measurable_epQ : Measurable (epQ (d := d)) :=
  ((continuous_eval_deriv _).clm_apply continuous_const).measurable

theorem le_g2Observable_of_le_valueNorm {g : PotentialField d} {a : ℝ}
    (h : a ≤ unitCubeValueNorm g) : a ≤ g2Observable g := by
  have := unitCubeDerivNorm_nonneg g
  have := unitCubeDerivLipschitzSeminorm_nonneg g
  unfold g2Observable; linarith

theorem le_g2Observable_of_le_derivNorm {g : PotentialField d} {a : ℝ}
    (h : a ≤ unitCubeDerivNorm g) : a ≤ g2Observable g := by
  have := unitCubeValueNorm_nonneg g
  have := unitCubeDerivLipschitzSeminorm_nonneg g
  unfold g2Observable; linarith

theorem abs_epX_le (g : PotentialField d) : |epX g| ≤ g2Observable g :=
  le_g2Observable_of_le_valueNorm (diagG_le g ⟨le_rfl, zero_le_one⟩)
theorem abs_epY_le (g : PotentialField d) : |epY g| ≤ g2Observable g :=
  le_g2Observable_of_le_valueNorm (diagG_le g ⟨zero_le_one, le_rfl⟩)
theorem abs_epP_le (g : PotentialField d) : |epP g| ≤ g2Observable g :=
  le_g2Observable_of_le_derivNorm (diagG'_le g ⟨le_rfl, zero_le_one⟩)
theorem abs_epQ_le (g : PotentialField d) : |epQ g| ≤ g2Observable g :=
  le_g2Observable_of_le_derivNorm (diagG'_le g ⟨zero_le_one, le_rfl⟩)

/-- Centering at an arbitrary point, for bounded continuous `f`. -/
theorem integral_centering_at {μ : Measure (PotentialField d)} [IsProbabilityMeasure μ]
    (hS : ∀ z : Vec d, Measure.map (translate z) μ = μ)
    (hW : Integrable (fun g : PotentialField d => g2Observable g) μ)
    {f : ℝ → ℝ} (hf : Continuous f) {Cf : ℝ} (hfb : ∀ x, |f x| ≤ Cf) (z : Vec d) :
    ∫ g, f (g z) * (deriv g z (diagDir d)) ∂μ = 0 := by
  have h0 := integral_centering_origin hS hW hf hfb
  have hm := integral_map (μ := μ) (φ := translate z)
    (f := fun g : PotentialField d => f (g 0) * deriv g 0 (diagDir d))
    (measurable_translate z).aemeasurable
    (((hf.comp (continuous_eval 0)).mul
      ((continuous_eval_deriv 0).clm_apply continuous_const)).aestronglyMeasurable)
  rw [hS z] at hm
  rw [← h0, hm]
  congr 1; ext g
  have : deriv (translate z g) 0 = deriv g z := by
    show deriv g (0 + z) = deriv g z
    rw [zero_add]
  rw [this, translate_apply, zero_add]

theorem centering_X {μ : Measure (PotentialField d)} [IsProbabilityMeasure μ]
    (hS : ∀ z : Vec d, Measure.map (translate z) μ = μ)
    (hW : Integrable (fun g : PotentialField d => g2Observable g) μ) :
    ∀ f : ℝ → ℝ, Measurable f → (∃ C, ∀ x, |f x| ≤ C) → ∫ g, f (epX g) * epP g ∂μ = 0 := by
  refine ext_bounded_measurable measurable_epX measurable_epP
    ((hW.mono' measurable_epP.aestronglyMeasurable (Filter.Eventually.of_forall fun g => by
      rw [Real.norm_eq_abs]; exact abs_epP_le g))) ?_
  rintro f hf ⟨C, hC⟩
  exact integral_centering_at hS hW hf hC (diagPt d 0)

theorem centering_Y {μ : Measure (PotentialField d)} [IsProbabilityMeasure μ]
    (hS : ∀ z : Vec d, Measure.map (translate z) μ = μ)
    (hW : Integrable (fun g : PotentialField d => g2Observable g) μ) :
    ∀ f : ℝ → ℝ, Measurable f → (∃ C, ∀ x, |f x| ≤ C) → ∫ g, f (epY g) * epQ g ∂μ = 0 := by
  refine ext_bounded_measurable measurable_epY measurable_epQ
    ((hW.mono' measurable_epQ.aestronglyMeasurable (Filter.Eventually.of_forall fun g => by
      rw [Real.norm_eq_abs]; exact abs_epQ_le g))) ?_
  rintro f hf ⟨C, hC⟩
  exact integral_centering_at hS hW hf hC (diagPt d 1)

/-- The central identity `E[h(X,Y)(P+Q)] = 0`. -/
theorem centering_pair (hd : 0 < d) {μ : Measure (PotentialField d)} [IsProbabilityMeasure μ]
    (hS : ∀ z : Vec d, Measure.map (translate z) μ = μ)
    (hW : Integrable (fun g : PotentialField d => g2Observable g) μ)
    (hI : ∀ (U V : Set (Vec d)), MeasurableSet U → MeasurableSet V →
      (∀ ⦃x y : Vec d⦄, x ∈ U → y ∈ V → Real.sqrt (d : ℝ) ≤ euclideanNorm (x - y)) →
      Indep (PotentialField.localSigma U) (PotentialField.localSigma V) μ)
    (h : ℝ → ℝ → ℝ) (hh : Measurable (Function.uncurry h)) (hb : ∃ C, ∀ x y, |h x y| ≤ C) :
    ∫ g, h (epX g) (epY g) * epZ g ∂μ = 0 := by
  obtain ⟨i1, i2⟩ := indep_endpoints hd hI
  have hPi : Integrable (fun g : PotentialField d => epP g) μ :=
    hW.mono' measurable_epP.aestronglyMeasurable (Filter.Eventually.of_forall fun g => by
      rw [Real.norm_eq_abs]; exact abs_epP_le g)
  have hQi : Integrable (fun g : PotentialField d => epQ g) μ :=
    hW.mono' measurable_epQ.aestronglyMeasurable (Filter.Eventually.of_forall fun g => by
      rw [Real.norm_eq_abs]; exact abs_epQ_le g)
  have e1 := integral_pair_mul_eq_zero measurable_epX measurable_epP measurable_epY hPi i1
    (centering_X hS hW) h hh hb
  have e2 := integral_pair_mul_eq_zero measurable_epY measurable_epQ measurable_epX hQi i2
    (centering_Y hS hW) (fun a b => h b a) (hh.comp measurable_swap)
    (by obtain ⟨C, hC⟩ := hb; exact ⟨C, fun a b => hC b a⟩)
  have hbC : ∃ C, ∀ x y, |h x y| ≤ C := hb
  obtain ⟨C, hC⟩ := hbC
  have hm : Measurable (fun g : PotentialField d => h (epX g) (epY g)) :=
    hh.comp (measurable_epX.prodMk measurable_epY)
  have iP : Integrable (fun g : PotentialField d => h (epX g) (epY g) * epP g) μ := by
    refine Integrable.mono' (g := fun g => C * |epP g|) (hPi.abs.const_mul _)
      (hm.mul measurable_epP).aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hC _ _) (abs_nonneg _)
  have iQ : Integrable (fun g : PotentialField d => h (epX g) (epY g) * epQ g) μ := by
    refine Integrable.mono' (g := fun g => C * |epQ g|) (hQi.abs.const_mul _)
      (hm.mul measurable_epQ).aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hC _ _) (abs_nonneg _)
  simp only [epZ, mul_add]
  rw [integral_add iP iQ, e1]
  simpa using e2

end GMCExplicitDelta.Source
