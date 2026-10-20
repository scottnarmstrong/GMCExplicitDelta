module

public import SubdiffusiveProcess.Model.LocalSigma
public import SubdiffusiveProcess.Model.ShellLawG1
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Local measurability of point values and directional derivatives

If `S` is open and the segment `a + t v` (`0 < t < ε`) lies in `S`, then `g ↦ g a` and
`g ↦ (deriv g a) v` are measurable for the local sigma-field `localSigma S`: they are limits of
averages of `g` over small balls, resp. of difference quotients of such limits.
-/

@[expose] public section

namespace GMCExplicitDelta.Source

open Homogenization MeasureTheory Filter Topology
open SubdiffusiveProcess.Model SubdiffusiveProcess.Model.PotentialField

variable {d : ℕ}

/-- Normalised indicator of the ball `B(y, ρ)`. -/
noncomputable def ballProbe (y : Vec d) (ρ : ℝ) : Vec d → ℝ :=
  fun x => (volume (Metric.ball y ρ)).toReal⁻¹ * (Metric.ball y ρ).indicator (fun _ => (1:ℝ)) x

theorem isProbeR_ballProbe (y : Vec d) (ρ : ℝ) : IsProbeR (ballProbe y ρ) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold ballProbe
    exact measurable_const.mul (measurable_const.indicator Metric.isOpen_ball.measurableSet)
  · refine ⟨(volume (Metric.ball y ρ)).toReal⁻¹, fun x => ?_⟩
    unfold ballProbe
    by_cases hx : x ∈ Metric.ball y ρ
    · simp [hx]
    · simp [hx]
  · refine HasCompactSupport.intro (isCompact_closedBall y ρ) fun x hx => ?_
    have : x ∉ Metric.ball y ρ := fun h => hx (Metric.ball_subset_closedBall h)
    simp [ballProbe, this]

theorem support_ballProbe_subset (y : Vec d) (ρ : ℝ) :
    Function.support (ballProbe y ρ) ⊆ Metric.ball y ρ := by
  intro x hx
  by_contra h
  exact hx (by simp [ballProbe, h])

theorem measurable_entryTest_localSigma (i j : Fin d) {S : Set (Vec d)} {φ : Vec d → ℝ}
    (hφ : IsProbeR φ) (hS : Function.support φ ⊆ S) :
    Measurable[PotentialField.localSigma S]
      (fun g : PotentialField d => entryTestR i j φ (forgetPotential g)) := by
  have h1 : Measurable[LocalSigmaR S] (entryTestR i j φ) := by
    intro t ht
    exact MeasurableSpace.measurableSet_generateFrom ⟨i, j, φ, hφ, hS, t, ht, rfl⟩
  intro t ht
  exact ⟨_, h1 ht, rfl⟩

theorem entryTest_ballProbe (hd : 0 < d) (g : PotentialField d) (y : Vec d) {ρ : ℝ} (hρ : 0 < ρ) :
    entryTestR ⟨0, hd⟩ ⟨0, hd⟩ (ballProbe y ρ) (forgetPotential g) =
      (volume (Metric.ball y ρ)).toReal⁻¹ * ∫ x in Metric.ball y ρ, g x := by
  unfold entryTestR ballProbe
  have : ∀ x, forgetPotential g x ⟨0, hd⟩ ⟨0, hd⟩ *
      ((volume (Metric.ball y ρ)).toReal⁻¹ * (Metric.ball y ρ).indicator (fun _ => (1:ℝ)) x) =
      (volume (Metric.ball y ρ)).toReal⁻¹ * (Metric.ball y ρ).indicator (fun x => g x) x := by
    intro x
    by_cases hx : x ∈ Metric.ball y ρ <;> simp [hx, forgetPotential_apply, Matrix.smul_apply]
    ring
  simp_rw [this]
  rw [integral_const_mul, integral_indicator Metric.isOpen_ball.measurableSet]

theorem entryTest_ballProbe_close (hd : 0 < d) (g : PotentialField d) (y : Vec d) {ρ ε : ℝ}
    (hρ : 0 < ρ) (hε : ∀ x ∈ Metric.ball y ρ, |g x - g y| ≤ ε) :
    |entryTestR ⟨0, hd⟩ ⟨0, hd⟩ (ballProbe y ρ) (forgetPotential g) - g y| ≤ ε := by
  rw [entryTest_ballProbe hd g y hρ]
  set V := (volume (Metric.ball y ρ)).toReal with hV
  have hVpos : 0 < V := by
    rw [hV]; exact ENNReal.toReal_pos (Metric.measure_ball_pos volume y hρ).ne' measure_ball_lt_top.ne
  have hint : IntegrableOn (fun x => g x) (Metric.ball y ρ) volume :=
    (g.1.1.continuous.continuousOn.integrableOn_compact (isCompact_closedBall y ρ)).mono_set
      Metric.ball_subset_closedBall
  have h1 : (∫ x in Metric.ball y ρ, g x) - V * g y = ∫ x in Metric.ball y ρ, (g x - g y) := by
    rw [integral_sub hint (integrableOn_const measure_ball_lt_top.ne)]
    simp [hV, Measure.real]
  have h2 : ‖∫ x in Metric.ball y ρ, (g x - g y)‖ ≤ ε * V := by
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Metric.ball y ρ)
      (f := fun x => g x - g y) (C := ε) measure_ball_lt_top
      (fun x hx => by rw [Real.norm_eq_abs]; exact hε x hx)
    simpa [hV, Measure.real, mul_comm] using this
  have : V⁻¹ * (∫ x in Metric.ball y ρ, g x) - g y = V⁻¹ * ((∫ x in Metric.ball y ρ, g x) - V * g y) := by
    field_simp
  rw [this, abs_mul, abs_of_pos (inv_pos.2 hVpos), ← Real.norm_eq_abs, h1]
  calc V⁻¹ * ‖∫ x in Metric.ball y ρ, (g x - g y)‖ ≤ V⁻¹ * (ε * V) :=
        mul_le_mul_of_nonneg_left h2 (inv_pos.2 hVpos).le
    _ = ε := by field_simp

/-- Point values at interior points of `S` are `localSigma S`-measurable. -/
theorem measurable_eval_localSigma (hd : 0 < d) {S : Set (Vec d)} {y : Vec d} {r : ℝ}
    (hr : 0 < r) (hyS : Metric.ball y r ⊆ S) :
    Measurable[PotentialField.localSigma S] (fun g : PotentialField d => g y) := by
  let ρ : ℕ → ℝ := fun n => r / (n + 1)
  have hρ : ∀ n, 0 < ρ n := fun n => by positivity
  have hmeas : ∀ n, Measurable[PotentialField.localSigma S]
      (fun g : PotentialField d => entryTestR ⟨0, hd⟩ ⟨0, hd⟩ (ballProbe y (ρ n)) (forgetPotential g)) :=
    fun n => measurable_entryTest_localSigma _ _ (isProbeR_ballProbe y _)
      ((support_ballProbe_subset y _).trans
        ((Metric.ball_subset_ball (by
          show r / ((n:ℝ) + 1) ≤ r
          exact div_le_self hr.le (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]))).trans hyS))
  let _ : MeasurableSpace (PotentialField d) := PotentialField.localSigma S
  refine measurable_of_tendsto_metrizable
    (f := fun n g => entryTestR ⟨0, hd⟩ ⟨0, hd⟩ (ballProbe y (ρ n)) (forgetPotential g)) hmeas ?_
  rw [tendsto_pi_nhds]
  intro g
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hc : ContinuousAt (fun x => g x) y := g.1.1.continuous.continuousAt
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 hc (ε / 2) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt (r / δ)
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq]
  refine lt_of_le_of_lt (entryTest_ballProbe_close hd g y (hρ n) (ε := ε / 2) fun x hx => ?_) (by linarith)
  have hxδ : dist x y < δ := by
    refine lt_of_lt_of_le (Metric.mem_ball.1 hx) ?_
    show r / ((n:ℝ) + 1) ≤ δ
    rw [div_le_iff₀ (by positivity)]
    have : r / δ < (n : ℝ) + 1 := by
      have : (N:ℝ) ≤ n := by exact_mod_cast hn
      linarith
    rw [div_lt_iff₀ hδ] at this
    linarith
  have := hδ' hxδ
  rw [Real.dist_eq] at this
  exact this.le


theorem tendsto_seg_param {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => ε / (2 * ((n : ℝ) + 2))) atTop (𝓝[≠] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
  · have : Tendsto (fun n : ℕ => (2 * ((n : ℝ) + 2))) atTop atTop :=
      Tendsto.const_mul_atTop two_pos (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    exact tendsto_const_nhds.div_atTop this
  · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    positivity

theorem measurable_localSigma_of_segment (hd : 0 < d) {S : Set (Vec d)} (hSo : IsOpen S)
    {a v : Vec d} {ε : ℝ} (hε : 0 < ε) (hseg : ∀ t : ℝ, 0 < t → t < ε → a + t • v ∈ S) :
    Measurable[PotentialField.localSigma S] (fun g : PotentialField d => g a) ∧
    Measurable[PotentialField.localSigma S] (fun g : PotentialField d => deriv g a v) := by
  set t : ℕ → ℝ := fun n => ε / (2 * ((n : ℝ) + 2)) with ht
  have ht0 : ∀ n, 0 < t n := fun n => by simp only [ht]; positivity
  have ht1 : ∀ n, t n < ε := fun n => by
    simp only [ht]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have ht2 : ∀ n, 2 * t n < ε := fun n => by
    simp only [ht]
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have hpt : ∀ n (c : ℝ), 0 < c → c * t n < ε →
      Measurable[PotentialField.localSigma S] (fun g : PotentialField d => g (a + (c * t n) • v)) := by
    intro n c hc hct
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hSo _ (hseg _ (mul_pos hc (ht0 n)) hct)
    exact measurable_eval_localSigma hd hr hball
  have hT : Tendsto t atTop (𝓝[≠] 0) := tendsto_seg_param hε
  have hT' : Tendsto t atTop (𝓝 0) := hT.mono_right nhdsWithin_le_nhds
  constructor
  · let _ : MeasurableSpace (PotentialField d) := PotentialField.localSigma S
    refine measurable_of_tendsto_metrizable
      (f := fun n g => g (a + ((1:ℝ) * t n) • v)) (fun n => hpt n 1 one_pos (by simpa using ht1 n)) ?_
    rw [tendsto_pi_nhds]
    intro g
    have hc : Continuous (fun s : ℝ => g (a + s • v)) :=
      g.1.1.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))
    have := (hc.tendsto 0).comp hT'
    simpa [Function.comp_def] using this
  · let _ : MeasurableSpace (PotentialField d) := PotentialField.localSigma S
    refine measurable_of_tendsto_metrizable
      (f := fun n g => (t n)⁻¹ * (g (a + ((2:ℝ) * t n) • v) - g (a + ((1:ℝ) * t n) • v)))
      (fun n => ((hpt n 2 two_pos (ht2 n)).sub (hpt n 1 one_pos (by simpa using ht1 n))).const_mul _) ?_
    rw [tendsto_pi_nhds]
    intro g
    have hG : HasDerivAt (fun s : ℝ => g (a + s • v)) (deriv g a v) 0 := by
      have h1 : HasDerivAt (fun s : ℝ => a + s • v) v 0 := by
        simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add a
      have h2 : HasFDerivAt g (deriv g a) (a + (0:ℝ) • v) := by simpa using g.hasFDerivAt a
      exact h2.comp_hasDerivAt (0:ℝ) h1
    have hs := (hasDerivAt_iff_tendsto_slope_zero.1 hG)
    have hs1 := hs.comp hT
    have h2t : Tendsto (fun n => 2 * t n) atTop (𝓝 0) := by simpa using hT'.const_mul 2
    have hs2 := hs.comp (tendsto_nhdsWithin_iff.2 ⟨h2t,
      Eventually.of_forall fun n => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact (mul_pos two_pos (ht0 n)).ne'⟩ :
        Tendsto (fun n => 2 * t n) atTop (𝓝[≠] 0))
    have := (hs2.const_mul 2).sub hs1
    have e : (2:ℝ) * deriv g a v - deriv g a v = deriv g a v := by ring
    rw [e] at this
    refine this.congr (fun n => ?_)
    simp only [Function.comp_apply, smul_eq_mul, zero_add, mul_zero, add_zero, one_mul]
    have := (ht0 n).ne'
    simp only [mul_sub, zero_add]
    field_simp
    ring

end GMCExplicitDelta.Source
