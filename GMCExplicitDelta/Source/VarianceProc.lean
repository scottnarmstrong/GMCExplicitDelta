module

public import GMCExplicitDelta.Source.VarianceFubini
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# Abstract diagonal process

A stationary process `G` with `C^{1,1}` paths and derivative process `G'`, with measurable envelopes
`a, b, c` (value, derivative, Lipschitz constant of the derivative on `[0,1]`), a measure preserving
shift, independence at distance `≥ 1` and centering.  Basic moment facts.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace GMCExplicitDelta.Source

open MeasureTheory ProbabilityTheory

/-- Data of the abstract diagonal process. -/
structure DiagProc {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (G G' : ℝ → Ω → ℝ)
    (a b c : Ω → ℝ) where
  mG : ∀ t, Measurable (G t)
  mG' : ∀ t, Measurable (G' t)
  hasDeriv : ∀ ω t, HasDerivAt (fun s => G s ω) (G' t ω) t
  cont' : ∀ ω, Continuous fun t => G' t ω
  ma : Measurable a
  mb : Measurable b
  mc : Measurable c
  bG : ∀ ω t, t ∈ Set.Icc (0:ℝ) 1 → |G t ω| ≤ a ω
  bG' : ∀ ω t, t ∈ Set.Icc (0:ℝ) 1 → |G' t ω| ≤ b ω
  lip : ∀ ω, ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1, |G' s ω - G' t ω| ≤ c ω * |s - t|
  L2 : Integrable (fun ω => (a ω + b ω + c ω) ^ 2) P
  T : ℝ → Ω → Ω
  T_mp : ∀ u, MeasurePreserving (T u) P P
  T_G : ∀ u t ω, G t (T u ω) = G (t + u) ω
  T_G' : ∀ u t ω, G' t (T u ω) = G' (t + u) ω
  indep : ∀ t, 1 ≤ t →
    IndepFun (fun ω => (G 0 ω, G' 0 ω)) (fun ω => (G t ω, G' t ω)) P
  mean_G : ∫ ω, G 0 ω ∂P = 0
  mean_G' : ∫ ω, G' 0 ω ∂P = 0

namespace DiagProc

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {G G' : ℝ → Ω → ℝ} {a b c : Ω → ℝ}

/-- The covariance function `C(t) = E G(0) G(t)`. -/
noncomputable def cov (_H : DiagProc P G G' a b c) (t : ℝ) : ℝ := ∫ ω, G 0 ω * G t ω ∂P

variable (H : DiagProc P G G' a b c)
include H

theorem a_nonneg (ω : Ω) : 0 ≤ a ω := (abs_nonneg _).trans (H.bG ω 0 ⟨le_rfl, zero_le_one⟩)
theorem b_nonneg (ω : Ω) : 0 ≤ b ω := (abs_nonneg _).trans (H.bG' ω 0 ⟨le_rfl, zero_le_one⟩)
theorem c_nonneg (ω : Ω) : 0 ≤ c ω := by
  have := (abs_nonneg _).trans (H.lip ω 0 ⟨le_rfl, zero_le_one⟩ 1 ⟨zero_le_one, le_rfl⟩)
  simpa using this

theorem int_sq_a : Integrable (fun ω => a ω ^ 2) P :=
  H.L2.mono' (H.ma.pow_const 2).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (H.a_nonneg ω) (by linarith [H.b_nonneg ω, H.c_nonneg ω]) 2)

theorem int_sq_b : Integrable (fun ω => b ω ^ 2) P :=
  H.L2.mono' (H.mb.pow_const 2).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (H.b_nonneg ω) (by linarith [H.a_nonneg ω, H.c_nonneg ω]) 2)

theorem int_sq_c : Integrable (fun ω => c ω ^ 2) P :=
  H.L2.mono' (H.mc.pow_const 2).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (H.c_nonneg ω) (by linarith [H.b_nonneg ω, H.a_nonneg ω]) 2)

theorem int_ab : Integrable (fun ω => a ω * b ω) P :=
  integrable_mul_of_sq H.ma H.mb H.int_sq_a H.int_sq_b
theorem int_ac : Integrable (fun ω => a ω * c ω) P :=
  integrable_mul_of_sq H.ma H.mc H.int_sq_a H.int_sq_c
theorem int_bc : Integrable (fun ω => b ω * c ω) P :=
  integrable_mul_of_sq H.mb H.mc H.int_sq_b H.int_sq_c

theorem int_sq_G0 : Integrable (fun ω => G 0 ω ^ 2) P :=
  H.int_sq_a.mono' ((H.mG 0).pow_const 2).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs (G 0 ω)]
    exact pow_le_pow_left₀ (abs_nonneg _) (H.bG ω 0 ⟨le_rfl, zero_le_one⟩) 2)

theorem int_sq_G'0 : Integrable (fun ω => G' 0 ω ^ 2) P :=
  H.int_sq_b.mono' ((H.mG' 0).pow_const 2).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs (G' 0 ω)]
    exact pow_le_pow_left₀ (abs_nonneg _) (H.bG' ω 0 ⟨le_rfl, zero_le_one⟩) 2)

/-- The shift preserves integrals. -/
theorem integral_T {f : Ω → ℝ} (hf : Measurable f) (u : ℝ) :
    ∫ ω, f (H.T u ω) ∂P = ∫ ω, f ω ∂P := by
  have := integral_map (μ := P) (H.T_mp u).measurable.aemeasurable hf.aestronglyMeasurable
  rw [(H.T_mp u).map_eq] at this
  exact this.symm

theorem integrable_T {f : Ω → ℝ} (hf : Measurable f) (hi : Integrable f P) (u : ℝ) :
    Integrable (fun ω => f (H.T u ω)) P :=
  (integrable_map_measure hf.aestronglyMeasurable (H.T_mp u).measurable.aemeasurable).1
    (by rw [(H.T_mp u).map_eq]; exact hi)

theorem G_zero_T (u : ℝ) (ω : Ω) : G 0 (H.T u ω) = G u ω := by rw [H.T_G, zero_add]
theorem G'_zero_T (u : ℝ) (ω : Ω) : G' 0 (H.T u ω) = G' u ω := by rw [H.T_G', zero_add]

theorem int_sq_G (t : ℝ) : Integrable (fun ω => G t ω ^ 2) P := by
  have := H.integrable_T ((H.mG 0).pow_const 2) H.int_sq_G0 t
  simpa only [G_zero_T] using this

theorem int_sq_G' (t : ℝ) : Integrable (fun ω => G' t ω ^ 2) P := by
  have := H.integrable_T ((H.mG' 0).pow_const 2) H.int_sq_G'0 t
  simpa only [G'_zero_T] using this

theorem integral_sq_G (t : ℝ) : ∫ ω, G t ω ^ 2 ∂P = ∫ ω, G 0 ω ^ 2 ∂P := by
  have := H.integral_T ((H.mG 0).pow_const 2) t
  simpa only [G_zero_T] using this

theorem integral_sq_G' (t : ℝ) : ∫ ω, G' t ω ^ 2 ∂P = ∫ ω, G' 0 ω ^ 2 ∂P := by
  have := H.integral_T ((H.mG' 0).pow_const 2) t
  simpa only [G'_zero_T] using this

theorem int_GG (s t : ℝ) : Integrable (fun ω => G s ω * G t ω) P :=
  integrable_mul_of_sq (H.mG s) (H.mG t) (H.int_sq_G s) (H.int_sq_G t)
theorem int_GG' (s t : ℝ) : Integrable (fun ω => G s ω * G' t ω) P :=
  integrable_mul_of_sq (H.mG s) (H.mG' t) (H.int_sq_G s) (H.int_sq_G' t)
theorem int_G'G' (s t : ℝ) : Integrable (fun ω => G' s ω * G' t ω) P :=
  integrable_mul_of_sq (H.mG' s) (H.mG' t) (H.int_sq_G' s) (H.int_sq_G' t)

theorem shift_GG (x y u : ℝ) :
    ∫ ω, G (x + u) ω * G (y + u) ω ∂P = ∫ ω, G x ω * G y ω ∂P := by
  have := H.integral_T (f := fun ω => G x ω * G y ω) ((H.mG x).mul (H.mG y)) u
  simpa only [H.T_G] using this

theorem shift_GG' (x y u : ℝ) :
    ∫ ω, G (x + u) ω * G' (y + u) ω ∂P = ∫ ω, G x ω * G' y ω ∂P := by
  have := H.integral_T (f := fun ω => G x ω * G' y ω) ((H.mG x).mul (H.mG' y)) u
  simpa only [H.T_G, H.T_G'] using this

theorem cov_shift (x y : ℝ) : ∫ ω, G x ω * G y ω ∂P = H.cov (y - x) := by
  have := H.shift_GG 0 (y - x) x
  simpa only [zero_add, sub_add_cancel, cov] using this

theorem cov_even (t : ℝ) : H.cov (-t) = H.cov t := by
  have h1 := H.cov_shift t 0
  rw [zero_sub] at h1
  rw [← h1]
  unfold cov
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)

theorem cov_zero : H.cov 0 = ∫ ω, G 0 ω ^ 2 ∂P := by simp [cov, sq]

theorem integral_G (t : ℝ) : ∫ ω, G t ω ∂P = 0 := by
  have := H.integral_T (H.mG 0) t
  simpa only [G_zero_T, H.mean_G] using this

theorem integral_G' (t : ℝ) : ∫ ω, G' t ω ∂P = 0 := by
  have := H.integral_T (H.mG' 0) t
  simpa only [G'_zero_T, H.mean_G'] using this

theorem indep_mul {t : ℝ} (ht : 1 ≤ t) {φ ψ : ℝ × ℝ → ℝ} (hφ : Measurable φ) (hψ : Measurable ψ) :
    ∫ ω, φ (G 0 ω, G' 0 ω) * ψ (G t ω, G' t ω) ∂P =
      (∫ ω, φ (G 0 ω, G' 0 ω) ∂P) * ∫ ω, ψ (G t ω, G' t ω) ∂P := by
  have hi := (H.indep t ht).comp hφ hψ
  have hX : Measurable fun ω => φ (G 0 ω, G' 0 ω) := hφ.comp ((H.mG 0).prodMk (H.mG' 0))
  have hY : Measurable fun ω => ψ (G t ω, G' t ω) := hψ.comp ((H.mG t).prodMk (H.mG' t))
  exact hi.integral_mul_eq_mul_integral hX.aestronglyMeasurable hY.aestronglyMeasurable

theorem cov_of_one_le {t : ℝ} (ht : 1 ≤ t) : H.cov t = 0 := by
  have := H.indep_mul ht (φ := Prod.fst) (ψ := Prod.fst) measurable_fst measurable_fst
  simp only [cov]
  rw [this]
  simp [H.mean_G]

theorem indep_G0_G'1 : ∫ ω, G 0 ω * G' 1 ω ∂P = 0 := by
  have := H.indep_mul (le_refl (1:ℝ)) (φ := Prod.fst) (ψ := Prod.snd) measurable_fst measurable_snd
  rw [this]; simp [H.mean_G]

theorem indep_G'0_G1 : ∫ ω, G' 0 ω * G 1 ω ∂P = 0 := by
  have := H.indep_mul (le_refl (1:ℝ)) (φ := Prod.snd) (ψ := Prod.fst) measurable_snd measurable_fst
  rw [this]; simp [H.mean_G']

theorem indep_G'0_G'1 : ∫ ω, G' 0 ω * G' 1 ω ∂P = 0 := by
  have := H.indep_mul (le_refl (1:ℝ)) (φ := Prod.snd) (ψ := Prod.snd) measurable_snd measurable_snd
  rw [this]; simp [H.mean_G']

end DiagProc

end GMCExplicitDelta.Source
