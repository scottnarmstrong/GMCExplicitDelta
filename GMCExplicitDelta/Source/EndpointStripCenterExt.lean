module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Extending a centering identity and using independence

Generic probabilistic lemmas: if `E[f(U) D] = 0` for bounded continuous `f` then also for bounded
measurable `f`; and if `(U,P)` is independent of `Y` then `E[h(U,Y) P] = 0` for bounded
measurable `h`.
-/

@[expose] public section

namespace GMCExplicitDelta.Source

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem integral_withDensity_ofReal_comp {U D : Ω → ℝ} (hU : Measurable U) (hD : Measurable D)
    {f : ℝ → ℝ} (hf : Measurable f) :
    ∫ x, f x ∂((μ.withDensity fun ω => ENNReal.ofReal (D ω)).map U) =
      ∫ ω, max (D ω) 0 * f (U ω) ∂μ := by
  rw [integral_map hU.aemeasurable hf.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul₀ (hD.ennreal_ofReal.aemeasurable)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal', smul_eq_mul]

theorem ext_bounded_measurable [IsFiniteMeasure μ] {U D : Ω → ℝ} (hU : Measurable U)
    (hDm : Measurable D) (hD : Integrable D μ)
    (hcont : ∀ f : ℝ → ℝ, Continuous f → (∃ C, ∀ x, |f x| ≤ C) →
      ∫ ω, f (U ω) * D ω ∂μ = 0) :
    ∀ f : ℝ → ℝ, Measurable f → (∃ C, ∀ x, |f x| ≤ C) → ∫ ω, f (U ω) * D ω ∂μ = 0 := by
  set νp : Measure ℝ := (μ.withDensity fun ω => ENNReal.ofReal (D ω)).map U with hνp
  set νm : Measure ℝ := (μ.withDensity fun ω => ENNReal.ofReal (-D ω)).map U with hνm
  haveI : IsFiniteMeasure (μ.withDensity fun ω => ENNReal.ofReal (D ω)) :=
    isFiniteMeasure_withDensity_ofReal hD.hasFiniteIntegral
  haveI : IsFiniteMeasure (μ.withDensity fun ω => ENNReal.ofReal (-D ω)) :=
    isFiniteMeasure_withDensity_ofReal hD.neg.hasFiniteIntegral
  haveI : IsFiniteMeasure νp := Measure.isFiniteMeasure_map _ _
  haveI : IsFiniteMeasure νm := Measure.isFiniteMeasure_map _ _
  -- the two integrals
  have key : ∀ f : ℝ → ℝ, Measurable f → (∃ C, ∀ x, |f x| ≤ C) →
      (∫ x, f x ∂νp) - (∫ x, f x ∂νm) = ∫ ω, f (U ω) * D ω ∂μ := by
    intro f hf ⟨C, hC⟩
    rw [hνp, hνm, integral_withDensity_ofReal_comp hU hDm hf,
      integral_withDensity_ofReal_comp (D := fun ω => -D ω) hU hDm.neg hf]
    have hi : ∀ E : Ω → ℝ, Measurable E → Integrable E μ →
        Integrable (fun ω => max (E ω) 0 * f (U ω)) μ := by
      intro E hE hEi
      refine Integrable.mono' (g := fun ω => C * |E ω|) (hEi.abs.const_mul _)
        ((hE.max measurable_const).mul (hf.comp hU)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |max (E ω) 0| ≤ |E ω| := by
        rcases le_total (E ω) 0 with h | h
        · rw [max_eq_right h]; simp
        · rw [max_eq_left h]
      calc _ ≤ |E ω| * C := mul_le_mul h1 (hC _) (abs_nonneg _) (abs_nonneg _)
        _ = _ := mul_comm _ _
    rw [← integral_sub (hi D hDm hD) (hi (fun ω => -D ω) hDm.neg hD.neg)]
    congr 1; ext ω
    rcases le_total (D ω) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith : (0:ℝ) ≤ -D ω)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith : -D ω ≤ 0)]; ring
  have heq : νp = νm := by
    refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
    have := key f f.continuous.measurable ⟨‖f‖, fun x => by simpa using f.norm_coe_le_norm x⟩
    have h0 := hcont f f.continuous ⟨‖f‖, fun x => by simpa using f.norm_coe_le_norm x⟩
    linarith
  intro f hf hb
  rw [← key f hf hb, heq, sub_self]

/-- If `(U,P)` is independent of `Y` and `E[f(U) P] = 0` for bounded measurable `f`, then
`E[h(U,Y) P] = 0` for bounded measurable `h`. -/
theorem integral_pair_mul_eq_zero [IsProbabilityMeasure μ] {U P Y : Ω → ℝ} (hU : Measurable U)
    (hP : Measurable P) (hY : Measurable Y) (hPi : Integrable P μ)
    (hind : IndepFun (fun ω => (U ω, P ω)) Y μ)
    (hcen : ∀ f : ℝ → ℝ, Measurable f → (∃ C, ∀ x, |f x| ≤ C) → ∫ ω, f (U ω) * P ω ∂μ = 0)
    (h : ℝ → ℝ → ℝ) (hh : Measurable (Function.uncurry h)) (hb : ∃ C, ∀ x y, |h x y| ≤ C) :
    ∫ ω, h (U ω) (Y ω) * P ω ∂μ = 0 := by
  obtain ⟨C, hC⟩ := hb
  have hUP : Measurable (fun ω => (U ω, P ω)) := hU.prodMk hP
  have hmap : μ.map (fun ω => ((U ω, P ω), Y ω)) =
      (μ.map (fun ω => (U ω, P ω))).prod (μ.map Y) :=
    (indepFun_iff_map_prod_eq_prod_map_map hUP.aemeasurable hY.aemeasurable).1 hind
  set φ : (ℝ × ℝ) × ℝ → ℝ := fun q => h q.1.1 q.2 * q.1.2 with hφ
  have hφm : Measurable φ := by
    have : Measurable (fun q : (ℝ × ℝ) × ℝ => (q.1.1, q.2)) := by fun_prop
    exact (hh.comp this).mul (measurable_snd.comp measurable_fst)
  have hjoint : Measurable (fun ω => ((U ω, P ω), Y ω)) := hUP.prodMk hY
  have hint_map : Integrable φ (μ.map (fun ω => ((U ω, P ω), Y ω))) := by
    rw [integrable_map_measure hφm.aestronglyMeasurable hjoint.aemeasurable]
    refine Integrable.mono' (g := fun ω => C * |P ω|) (hPi.abs.const_mul _)
      (hφm.comp hjoint).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Function.comp, hφ, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hC _ _) (abs_nonneg _)
  have h1 : ∫ ω, h (U ω) (Y ω) * P ω ∂μ = ∫ q, φ q ∂(μ.map (fun ω => ((U ω, P ω), Y ω))) := by
    rw [integral_map hjoint.aemeasurable hφm.aestronglyMeasurable]
  rw [h1, hmap] at *
  rw [hmap] at hint_map
  rw [integral_prod_symm _ hint_map]
  have : ∀ y, ∫ x, φ (x, y) ∂(μ.map (fun ω => (U ω, P ω))) = 0 := by
    intro y
    have hhy : Measurable (fun u => h u y) := hh.comp (measurable_id.prodMk measurable_const)
    have hb' : ∃ C, ∀ x, |h x y| ≤ C := ⟨C, fun x => hC x y⟩
    have hc := hcen (fun u => h u y) hhy hb'
    have hmm : Measurable (fun x : ℝ × ℝ => φ (x, y)) :=
      hφm.comp (measurable_id.prodMk measurable_const)
    rw [integral_map hUP.aemeasurable hmm.aestronglyMeasurable]
    simpa [hφ] using hc
  simp [this]

end GMCExplicitDelta.Source
