module

public import GMCExplicitDelta.Source.EndpointStripAssemble
public import GMCExplicitDelta.Source.EndpointStripJensen
public import GMCExplicitDelta.Source.EndpointStripW
public import GMCExplicitDelta.Source.EndpointStripSigns

/-!
# The endpoint-strip moment inequalities for the law of `g`

Abstract hypotheses `EndpointModel`: stationarity, negation symmetry, range-one independence and
the exponential-square bound for the regularity observable.  Conclusions: the exponential envelope
and squared envelope bounds, in lintegral resp. integral form.
-/

@[expose] public section

namespace GMCExplicitDelta.Source

open Homogenization MeasureTheory ProbabilityTheory
open SubdiffusiveProcess.Model SubdiffusiveProcess.Model.PotentialField

/-- The properties of the law `μ` of `g₀` used by the endpoint-strip argument. -/
structure EndpointModel (d : ℕ) (δ : ℝ) (μ : Measure (PotentialField d)) : Prop where
  dim_pos : 0 < d
  delta_pos : 0 < δ
  stat : ∀ z : Vec d, Measure.map (translate z) μ = μ
  neg : Measure.map (negate (d := d)) μ = μ
  indep : ∀ (U V : Set (Vec d)), MeasurableSet U → MeasurableSet V →
    (∀ ⦃x y : Vec d⦄, x ∈ U → y ∈ V → Real.sqrt (d : ℝ) ≤ euclideanNorm (x - y)) →
    Indep (PotentialField.localSigma U) (PotentialField.localSigma V) μ
  expSq_int : Integrable (fun g : PotentialField d => Real.exp (g2Observable g ^ 2 / δ ^ 2)) μ
  expSq_le : ∫ g, Real.exp (g2Observable g ^ 2 / δ ^ 2) ∂μ ≤ 2

variable {d : ℕ} {δ : ℝ} {μ : Measure (PotentialField d)} [IsProbabilityMeasure μ]

theorem EndpointModel.W_facts (M : EndpointModel d δ μ) :
    AEStronglyMeasurable (fun g : PotentialField d => g2Observable g) μ ∧
    Integrable (fun g : PotentialField d => g2Observable g ^ 2) μ ∧
    Integrable (fun g : PotentialField d => g2Observable g) μ ∧
    ∫ g, g2Observable g ^ 2 ∂μ ≤ δ ^ 2 * Real.log 2 :=
  moments_of_expSq (fun g => g2Observable g) g2Observable_nonneg M.delta_pos M.expSq_int M.expSq_le

theorem EndpointModel.integrable_W (M : EndpointModel d δ μ) :
    Integrable (fun g : PotentialField d => g2Observable g) μ := M.W_facts.2.2.1

theorem convexOn_exp_sq (δ : ℝ) : ConvexOn ℝ Set.univ (fun t : ℝ => Real.exp (t ^ 2 / δ ^ 2)) := by
  have h1 : ConvexOn ℝ Set.univ (fun t : ℝ => t ^ 2 / δ ^ 2) := by
    have := (Even.convexOn_pow (𝕜 := ℝ) (n := 2) even_two).smul (inv_nonneg.2 (sq_nonneg δ))
    simpa [div_eq_mul_inv, mul_comm] using this
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have hf := h1.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  have he := convexOn_exp.2 (Set.mem_univ (x ^ 2 / δ ^ 2)) (Set.mem_univ (y ^ 2 / δ ^ 2)) ha hb hab
  simp only [smul_eq_mul] at hf he ⊢
  exact (Real.exp_le_exp.2 hf).trans he

theorem hasDerivAt_exp_sq (δ x : ℝ) : HasDerivAt (fun t : ℝ => Real.exp (t ^ 2 / δ ^ 2))
    (Real.exp (x ^ 2 / δ ^ 2) * (2 * x / δ ^ 2)) x := by
  have := ((hasDerivAt_pow 2 x).div_const (δ ^ 2)).exp
  convert this using 1
  simp

theorem jensen_exp (M : EndpointModel d δ μ) :
    ∫⁻ g, ENNReal.ofReal (Real.exp (envelope (epX g) (epY g) ^ 2 / δ ^ 2)) ∂μ ≤ 2 := by
  have hδ := M.delta_pos
  have hW := M.integrable_W
  have hPi : Integrable (fun g : PotentialField d => epP g) μ :=
    hW.mono' measurable_epP.aestronglyMeasurable (Filter.Eventually.of_forall fun g => by
      rw [Real.norm_eq_abs]; exact abs_epP_le g)
  have hQi : Integrable (fun g : PotentialField d => epQ g) μ :=
    hW.mono' measurable_epQ.aestronglyMeasurable (Filter.Eventually.of_forall fun g => by
      rw [Real.norm_eq_abs]; exact abs_epQ_le g)
  have hXi : Integrable (fun g : PotentialField d => epX g) μ :=
    hW.mono' measurable_epX.aestronglyMeasurable (Filter.Eventually.of_forall fun g => by
      rw [Real.norm_eq_abs]; exact abs_epX_le g)
  have hYi : Integrable (fun g : PotentialField d => epY g) μ :=
    hW.mono' measurable_epY.aestronglyMeasurable (Filter.Eventually.of_forall fun g => by
      rw [Real.norm_eq_abs]; exact abs_epY_le g)
  have hmain := jensen_trunc (μ := μ) (φ := fun t : ℝ => Real.exp (t ^ 2 / δ ^ 2))
    (φ' := fun t => Real.exp (t ^ 2 / δ ^ 2) * (2 * t / δ ^ 2))
    (convexOn_exp_sq δ) (hasDerivAt_exp_sq δ) (fun t => (Real.exp_pos _).le)
    (fun a _ b _ hab => Real.exp_le_exp.2
      (div_le_div_of_nonneg_right (by nlinarith [(Set.mem_Ici.1 ‹a ∈ Set.Ici 0›)]) (by positivity)))
    (fun t ht => by positivity)
    (X := epX) (Y := epY) (Z := epZ) (w := fun g => g2Observable g)
    measurable_epX measurable_epY (measurable_epP.add measurable_epQ) hXi hYi (hPi.add hQi)
    stripK_pos.le stripR_pos.le
    (fun h hh hb => centering_pair M.dim_pos M.stat hW M.indep h hh hb)
    (fun g => endpoint_pointwise g)
  refine hmain.trans ?_
  calc ∫⁻ g, ENNReal.ofReal (Real.exp (g2Observable g ^ 2 / δ ^ 2)) ∂μ
      = ENNReal.ofReal (∫ g, Real.exp (g2Observable g ^ 2 / δ ^ 2) ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal M.expSq_int
          (Filter.Eventually.of_forall fun g => (Real.exp_pos _).le)).symm
    _ ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal M.expSq_le
    _ = 2 := by simp


theorem measurable_envelope : Measurable (fun p : ℝ × ℝ => envelope p.1 p.2) := by
  unfold envelope; fun_prop

theorem jensen_sq (M : EndpointModel d δ μ) :
    ∫⁻ g, ENNReal.ofReal (envelope (epX g) (epY g) ^ 2) ∂μ ≤ ENNReal.ofReal (δ ^ 2 * Real.log 2) := by
  have hW := M.integrable_W
  have hPi : Integrable (fun g : PotentialField d => epP g) μ :=
    hW.mono' measurable_epP.aestronglyMeasurable (Filter.Eventually.of_forall fun g => by
      rw [Real.norm_eq_abs]; exact abs_epP_le g)
  have hQi : Integrable (fun g : PotentialField d => epQ g) μ :=
    hW.mono' measurable_epQ.aestronglyMeasurable (Filter.Eventually.of_forall fun g => by
      rw [Real.norm_eq_abs]; exact abs_epQ_le g)
  have hXi : Integrable (fun g : PotentialField d => epX g) μ :=
    hW.mono' measurable_epX.aestronglyMeasurable (Filter.Eventually.of_forall fun g => by
      rw [Real.norm_eq_abs]; exact abs_epX_le g)
  have hYi : Integrable (fun g : PotentialField d => epY g) μ :=
    hW.mono' measurable_epY.aestronglyMeasurable (Filter.Eventually.of_forall fun g => by
      rw [Real.norm_eq_abs]; exact abs_epY_le g)
  have hmain := jensen_trunc (μ := μ) (φ := fun t : ℝ => t ^ 2) (φ' := fun t => 2 * t)
    ((Even.convexOn_pow (𝕜 := ℝ) (n := 2) even_two))
    (fun x => by simpa using hasDerivAt_pow 2 x) (fun t => sq_nonneg t)
    (fun a ha b _ hab => pow_le_pow_left₀ ha hab 2)
    (fun t ht => by linarith)
    (X := epX) (Y := epY) (Z := epZ) (w := fun g => g2Observable g)
    measurable_epX measurable_epY (measurable_epP.add measurable_epQ) hXi hYi (hPi.add hQi)
    stripK_pos.le stripR_pos.le
    (fun h hh hb => centering_pair M.dim_pos M.stat hW M.indep h hh hb)
    (fun g => endpoint_pointwise g)
  refine hmain.trans ?_
  calc ∫⁻ g, ENNReal.ofReal (g2Observable g ^ 2) ∂μ
      = ENNReal.ofReal (∫ g, g2Observable g ^ 2 ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal M.W_facts.2.1
          (Filter.Eventually.of_forall fun g => sq_nonneg _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal M.W_facts.2.2.2

theorem EndpointModel.envelope_sq_bound (M : EndpointModel d δ μ) :
    Integrable (fun g : PotentialField d => envelope (epX g) (epY g) ^ 2) μ ∧
      ∫ g, envelope (epX g) (epY g) ^ 2 ∂μ ≤ δ ^ 2 * Real.log 2 := by
  have hW2 := M.W_facts.2.1
  have hmeas : Measurable (fun g : PotentialField d => envelope (epX g) (epY g)) :=
    measurable_envelope.comp (measurable_epX.prodMk measurable_epY)
  have hint : Integrable (fun g : PotentialField d => envelope (epX g) (epY g) ^ 2) μ := by
    refine Integrable.mono' (g := fun g => (4 * (1 + stripK) ^ 2) * g2Observable g ^ 2)
      (hW2.const_mul _) (hmeas.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun g => ?_)
    have h0 := envelope_nonneg (epX g) (epY g)
    have hX := abs_epX_le g
    have hY := abs_epY_le g
    have hK := one_le_stripK
    have h1 : envelope (epX g) (epY g) ≤ 2 * (1 + stripK) * g2Observable g := by
      unfold envelope
      have h2 : |epY g - epX g| ≤ 2 * g2Observable g := by
        have := abs_sub (epY g) (epX g); linarith
      have h3 : max |epX g| |epY g| ≤ g2Observable g := max_le hX hY
      have h4 := mul_le_mul_of_nonneg_left h2 stripK_pos.le
      have h5 := g2Observable_nonneg g
      nlinarith
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc envelope (epX g) (epY g) ^ 2 ≤ (2 * (1 + stripK) * g2Observable g) ^ 2 :=
          pow_le_pow_left₀ h0 h1 2
      _ = _ := by ring
  refine ⟨hint, ?_⟩
  have h1 := jensen_sq M
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun g => sq_nonneg _)] at h1
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg δ)
    (Real.log_nonneg (by norm_num)))).1 h1

end GMCExplicitDelta.Source
