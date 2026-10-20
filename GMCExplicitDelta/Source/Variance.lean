module

public import GMCExplicitDelta.Source.EndpointStripSource
public import GMCExplicitDelta.Source.VarianceSix
public import GMCExplicitDelta.Source.VarianceSup

/-!
# The source variance bound

`E g₀(x)² ≤ log 2 · δ² / (35 + (13 + 2√2) π²)` (steps S5, S6): the standing model supplies the abstract
diagonal process `DiagProc`, whose six-term lower bound and Fejér bound `r ≥ π² s` combine with
`E W² ≤ δ² log 2`.
-/

@[expose] public section

namespace GMCExplicitDelta.Source

open Homogenization MeasureTheory ProbabilityTheory
open SubdiffusiveProcess.Model SubdiffusiveProcess.Model.PotentialField

variable {d : ℕ}

/-- Independence of the diagonal data at distance `t ≥ 1`. -/
theorem indep_diag (hd : 0 < d) {μ : Measure (PotentialField d)}
    (hI : ∀ (U V : Set (Vec d)), MeasurableSet U → MeasurableSet V →
      (∀ ⦃x y : Vec d⦄, x ∈ U → y ∈ V → Real.sqrt (d : ℝ) ≤ euclideanNorm (x - y)) →
      Indep (PotentialField.localSigma U) (PotentialField.localSigma V) μ)
    {t : ℝ} (ht : 1 ≤ t) :
    IndepFun (fun g : PotentialField d => (diagG g 0, diagG' g 0))
      (fun g : PotentialField d => (diagG g t, diagG' g t)) μ := by
  have hind : Indep (PotentialField.localSigma (leftOrthant d))
      (PotentialField.localSigma (rightOrthant d)) μ :=
    hI _ _ isOpen_leftOrthant.measurableSet isOpen_rightOrthant.measurableSet
      (fun x y hx hy => sqrt_le_euclideanNorm_orthants hx hy)
  obtain ⟨hXL, hDL⟩ := measurable_localSigma_of_segment hd isOpen_leftOrthant
    (a := diagPt d 0) (v := -(diagDir d)) (ε := 1) one_pos (fun t ht _ => leftOrthant_segment t ht)
  obtain ⟨hYR, hQR⟩ := measurable_localSigma_of_segment hd isOpen_rightOrthant
    (a := diagPt d t) (v := diagDir d) (ε := 1) one_pos (fun s hs _ => by
      intro i; simp [diagPt, diagDir]; linarith)
  have hPL : Measurable[PotentialField.localSigma (leftOrthant d)]
      (fun g : PotentialField d => diagG' g 0) := by
    have : (fun g : PotentialField d => diagG' g 0) =
        fun g => -(deriv g (diagPt d 0) (-(diagDir d))) := by
      ext g; simp [diagG']
    rw [this]
    exact hDL.neg
  have hPair : Measurable[PotentialField.localSigma (leftOrthant d)]
      (fun g : PotentialField d => (diagG g 0, diagG' g 0)) := by
    let _ : MeasurableSpace (PotentialField d) := PotentialField.localSigma (leftOrthant d)
    exact (show Measurable (fun g : PotentialField d => diagG g 0) from hXL).prodMk hPL
  have hPair' : Measurable[PotentialField.localSigma (rightOrthant d)]
      (fun g : PotentialField d => (diagG g t, diagG' g t)) := by
    let _ : MeasurableSpace (PotentialField d) := PotentialField.localSigma (rightOrthant d)
    exact (show Measurable (fun g : PotentialField d => diagG g t) from hYR).prodMk
      (show Measurable (fun g : PotentialField d => diagG' g t) from hQR)
  exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hind hPair.comap_le) hPair'.comap_le

theorem deriv_negate (g : PotentialField d) (x : Vec d) : deriv (negate g) x = -deriv g x := by
  have h1 := (negate g).hasFDerivAt x
  have h2 := (g.hasFDerivAt x).neg
  have e : (⇑(negate g)) = fun y => -g y := funext fun y => negate_apply g y
  rw [e] at h1
  exact h1.unique h2

theorem integral_neg_symm {μ : Measure (PotentialField d)} {F : PotentialField d → ℝ}
    (hF : Measurable F) (hneg : ∀ g, F (negate g) = -F g)
    (hN : Measure.map (negate (d := d)) μ = μ) : ∫ g, F g ∂μ = 0 := by
  have h := integral_map (μ := μ) measurable_negate.aemeasurable hF.aestronglyMeasurable
  rw [hN] at h
  simp_rw [hneg] at h
  rw [integral_neg] at h
  linarith

theorem deriv_translate (z : Vec d) (g : PotentialField d) (x : Vec d) :
    deriv (translate z g) x = deriv g (x + z) := rfl

theorem diagPt_add (t u : ℝ) : diagPt d t + u • diagDir d = diagPt d (t + u) := by
  ext i; simp [diagPt, diagDir]; ring

theorem diagG_negate (g : PotentialField d) (t : ℝ) : diagG (negate g) t = -diagG g t := by
  simp [diagG]

theorem diagG'_negate (g : PotentialField d) (t : ℝ) : diagG' (negate g) t = -diagG' g t := by
  simp [diagG', deriv_negate]

theorem measurable_diagG (t : ℝ) : Measurable (fun g : PotentialField d => diagG g t) :=
  (continuous_eval (diagPt d t)).measurable

theorem measurable_diagG' (t : ℝ) : Measurable (fun g : PotentialField d => diagG' g t) :=
  ((continuous_eval_deriv (diagPt d t)).clm_apply continuous_const).measurable

/-- **Source variance bound** (steps S5, S6). -/
theorem source_variance {d : ℕ} (M : SubdiffusiveProcess.Model.GMCModel d) (x : Homogenization.Vec d) :
    MeasureTheory.Integrable (fun ω : SubdiffusiveProcess.Model.PotentialSample d => (ω 0 x) ^ 2)
        M.P.toMeasure ∧
    ∫ ω, (ω 0 x) ^ 2 ∂M.P.toMeasure ≤
      Real.log 2 * M.delta ^ 2 / (35 + (13 + 2 * Real.sqrt 2) * Real.pi ^ 2) := by
  have hE := endpointModel_of_gmc M
  set μ := (zeroPotentialLaw M.P).toMeasure with hμ
  have hcG : ∀ g : PotentialField d, Continuous fun t => diagG g t := continuous_diagG
  have hcG' : ∀ g : PotentialField d, Continuous fun t => diagG' g t := continuous_diagG'
  set a : PotentialField d → ℝ := supSurr (fun t g => diagG g t) with ha
  set b : PotentialField d → ℝ := supSurr (fun t g => diagG' g t) with hb
  set c : PotentialField d → ℝ := lipSurr (fun t g => diagG' g t) with hc
  have hW0 : ∀ g : PotentialField d, ∀ t ∈ Set.Icc (0:ℝ) 1, |diagG g t| ≤ unitCubeValueNorm g :=
    fun g t ht => diagG_le g ht
  have hW1 : ∀ g : PotentialField d, ∀ t ∈ Set.Icc (0:ℝ) 1, |diagG' g t| ≤ unitCubeDerivNorm g :=
    fun g t ht => diagG'_le g ht
  have hW2 : ∀ g : PotentialField d, ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1,
      |diagG' g s - diagG' g t| ≤ unitCubeDerivLipschitzSeminorm g * |s - t| :=
    fun g s hs t ht => diagG'_lip g hs ht
  have ha0 : ∀ g, 0 ≤ a g := fun g =>
    (abs_nonneg _).trans (abs_le_supSurr (F := fun t g => diagG g t) hcG hW0 g ⟨le_rfl, zero_le_one⟩)
  have hb0 : ∀ g, 0 ≤ b g := fun g =>
    (abs_nonneg _).trans (abs_le_supSurr (F := fun t g => diagG' g t) hcG' hW1 g ⟨le_rfl, zero_le_one⟩)
  have hc0 : ∀ g, 0 ≤ c g := fun g => by
    have h := abs_sub_le_lipSurr (F := fun t g => diagG' g t) hcG' hW2 g
      ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩
    have := (abs_nonneg _).trans h
    simpa using this
  have hP : ∀ g : PotentialField d, a g + b g + c g ≤ g2Observable g := fun g => by
    have h1 := supSurr_le (F := fun t g => diagG g t) hW0 g
    have h2 := supSurr_le (F := fun t g => diagG' g t) hW1 g
    have h3 := lipSurr_le (F := fun t g => diagG' g t) hW2 g
    unfold g2Observable
    linarith
  have hL2 : Integrable (fun g => (a g + b g + c g) ^ 2) μ :=
    hE.W_facts.2.1.mono'
      ((((measurable_supSurr measurable_diagG).add (measurable_supSurr measurable_diagG')).add
        (measurable_lipSurr measurable_diagG')).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun g => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (by linarith [ha0 g, hb0 g, hc0 g]) (hP g) 2)
  have H : DiagProc μ (fun t g => diagG g t) (fun t g => diagG' g t) a b c :=
    { mG := measurable_diagG
      mG' := measurable_diagG'
      hasDeriv := fun g t => hasDerivAt_diagG g t
      cont' := hcG'
      ma := measurable_supSurr measurable_diagG
      mb := measurable_supSurr measurable_diagG'
      mc := measurable_lipSurr measurable_diagG'
      bG := fun g t ht => abs_le_supSurr (F := fun t g => diagG g t) hcG hW0 g ht
      bG' := fun g t ht => abs_le_supSurr (F := fun t g => diagG' g t) hcG' hW1 g ht
      lip := fun g s hs t ht => abs_sub_le_lipSurr (F := fun t g => diagG' g t) hcG' hW2 g hs ht
      L2 := hL2
      T := fun u g => translate (u • diagDir d) g
      T_mp := fun u => ⟨measurable_translate _, hE.stat _⟩
      T_G := fun u t g => by
        show g (diagPt d t + u • diagDir d) = g (diagPt d (t + u))
        rw [diagPt_add]
      T_G' := fun u t g => by
        show deriv g (diagPt d t + u • diagDir d) (diagDir d) = deriv g (diagPt d (t + u)) (diagDir d)
        rw [diagPt_add]
      indep := fun t ht => indep_diag hE.dim_pos hE.indep ht
      mean_G := integral_neg_symm (measurable_diagG 0) (fun g => diagG_negate g 0) hE.neg
      mean_G' := integral_neg_symm (measurable_diagG' 0) (fun g => diagG'_negate g 0) hE.neg }
  have hXm : Measurable (fun ω : PotentialSample d => ω 0 x) :=
    (PotentialField.measurable_eval x).comp (measurable_pi_apply 0)
  have hlaw : M.P.toMeasure.map (fun ω : PotentialSample d => ω 0 x) = lawZero μ := by
    rw [← map_eval_eq hE.stat x]
    rw [hμ, zeroPotentialLaw, potentialMarginalLaw, ProbabilityMeasure.toMeasure_map,
      Measure.map_map (PotentialField.measurable_eval x) (measurable_pi_apply 0)]
    rfl
  have hsq : Measurable (fun y : ℝ => y ^ 2) := by fun_prop
  have hs_eq : ∫ ω, (ω 0 x) ^ 2 ∂M.P.toMeasure = ∫ g, (diagG g 0) ^ 2 ∂μ := by
    have h1 := integral_map (μ := M.P.toMeasure) hXm.aemeasurable hsq.aestronglyMeasurable
    rw [hlaw] at h1
    have h2 := integral_map (μ := μ) (measurable_diagG 0).aemeasurable hsq.aestronglyMeasurable
    have hmap : μ.map (fun g : PotentialField d => diagG g 0) = lawZero μ :=
      map_eval_eq hE.stat (diagPt d 0)
    rw [hmap] at h2
    rw [← h1, h2]
  refine ⟨by simpa using (source_even_moment M x 1).1, ?_⟩
  rw [hs_eq]
  have h35 := H.variance_lower
  have hpi := H.pi_sq_le
  have hIW : ∫ g, (a g + b g + c g) ^ 2 ∂μ ≤ ∫ g, g2Observable g ^ 2 ∂μ :=
    integral_mono hL2 hE.W_facts.2.1 fun g =>
      pow_le_pow_left₀ (by linarith [ha0 g, hb0 g, hc0 g]) (hP g) 2
  have hWb := hE.W_facts.2.2.2
  have hden : 0 < 35 + (13 + 2 * Real.sqrt 2) * Real.pi ^ 2 := by positivity
  have hk : 0 ≤ 13 + 2 * Real.sqrt 2 := by positivity
  rw [le_div_iff₀ hden]
  have := mul_le_mul_of_nonneg_left hpi hk
  nlinarith

end GMCExplicitDelta.Source
