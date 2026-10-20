module

public import GMCExplicitDelta.Coarse.Phi
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# C7, `L^p` part: `‖Φ_t(J)‖_p ≤ Φ_t(A)` when `‖J‖_p ≤ A`

For a probability measure `μ`, `p ≥ 2` and a nonnegative measurable `J`:
`eLpNorm J p ≤ A` implies `eLpNorm (Φ_t ∘ J) p ≤ Φ_t(A)`.  The proof is Minkowski on the three
terms of `Φ_t(J) = (cosh t - 1) + cosh t · J + sinh t · √(J² + 2J)` together with
`‖√(J²+2J)‖_p² = ‖J²+2J‖_{p/2} ≤ ‖J‖_p² + 2‖J‖_{p/2}` and monotonicity of `L^q` norms on a
probability space.
-/

@[expose] public section

open MeasureTheory Real
open scoped ENNReal

namespace GMCExplicitDelta.Coarse

theorem phi_eq (t j : ℝ) :
    phi t j = (cosh t - 1) + cosh t * j + sinh t * √(j * (j + 2)) := by
  unfold phi; ring

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- `‖f²‖_{p/2} = ‖f‖_p²`. -/
theorem eLpNorm_sq_half {p : ℝ} (hp : 2 ≤ p) {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) :
    eLpNorm (fun ω => f ω ^ 2) (ENNReal.ofReal (p / 2)) μ =
      eLpNorm f (ENNReal.ofReal p) μ ^ 2 := by
  have h := eLpNorm_norm_rpow (μ := μ) (p := ENNReal.ofReal (p / 2)) f hf
    (q := 2) (by norm_num)
  have e1 : ENNReal.ofReal (p / 2) * ENNReal.ofReal 2 = ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_mul (by linarith)]; congr 1; ring
  rw [e1] at h
  have e2 : (fun ω => ‖f ω‖ ^ (2 : ℝ)) = fun ω => f ω ^ 2 := by
    funext ω; rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [e2] at h
  rw [h, ENNReal.rpow_two]

theorem eLpNorm_sqrt_sq_le {p : ℝ} (hp : 2 ≤ p) {J : Ω → ℝ} (hJ : AEMeasurable J μ)
    (hJ0 : ∀ ω, 0 ≤ J ω) :
    eLpNorm (fun ω => √(J ω * (J ω + 2))) (ENNReal.ofReal p) μ ^ 2 ≤
      eLpNorm J (ENNReal.ofReal p) μ ^ 2 + 2 * eLpNorm J (ENNReal.ofReal p) μ := by
  have hJs : AEStronglyMeasurable J μ := hJ.aestronglyMeasurable
  have hKs : AEStronglyMeasurable (fun ω => √(J ω * (J ω + 2))) μ :=
    (Real.continuous_sqrt.measurable.comp_aemeasurable (hJ.mul (hJ.add_const 2))).aestronglyMeasurable
  -- the square of the sqrt term
  have h := eLpNorm_norm_rpow (μ := μ) (p := ENNReal.ofReal (p / 2))
    (fun ω => √(J ω * (J ω + 2))) hKs (q := 2) (by norm_num)
  have e1 : ENNReal.ofReal (p / 2) * ENNReal.ofReal 2 = ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_mul (by linarith)]; congr 1; ring
  rw [e1] at h
  have e2 : (fun ω => ‖√(J ω * (J ω + 2))‖ ^ (2 : ℝ)) = fun ω => J ω ^ 2 + 2 * J ω := by
    funext ω
    rw [Real.rpow_two, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by have := hJ0 ω; positivity)]
    ring
  rw [e2, ENNReal.rpow_two] at h
  rw [← h]
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (p / 2) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  have hsq : AEStronglyMeasurable (fun ω => J ω ^ 2) μ := hJs.pow 2
  have h2J : AEStronglyMeasurable (fun ω => 2 * J ω) μ := hJs.const_mul 2
  have hadd := eLpNorm_add_le (μ := μ) (p := ENNReal.ofReal (p / 2))
    (f := fun ω => J ω ^ 2) (g := fun ω => 2 * J ω) hp1
  have e3 : (fun ω => J ω ^ 2 + 2 * J ω) = (fun ω => J ω ^ 2) + (fun ω => 2 * J ω) := rfl
  rw [e3]
  refine hadd.trans ?_
  rw [eLpNorm_sq_half hp hJs]
  have e4 : eLpNorm (fun ω => 2 * J ω) (ENNReal.ofReal (p / 2)) μ =
      2 * eLpNorm J (ENNReal.ofReal (p / 2)) μ := by
    have := eLpNorm_const_smul (μ := μ) (p := ENNReal.ofReal (p / 2)) (2 : ℝ) J
    have hf : ((2 : ℝ) • J) = fun ω => 2 * J ω := by funext ω; rfl
    rw [hf] at this
    simpa [Real.enorm_eq_ofReal (show (0 : ℝ) ≤ 2 by norm_num)] using this
  rw [e4]
  gcongr
  exact eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal (by linarith))

/-- C7, `L^p` bound: `‖J‖_p ≤ A` implies `‖Φ_t(J)‖_p ≤ Φ_t(A)` for `J ≥ 0`, `p ≥ 2`. -/
theorem eLpNorm_phi_comp_le {p : ℝ} (hp : 2 ≤ p) {J : Ω → ℝ} (hJ : AEMeasurable J μ)
    (hJ0 : ∀ ω, 0 ≤ J ω) {t A : ℝ} (ht : 0 ≤ t) (hA : 0 ≤ A)
    (hJA : eLpNorm J (ENNReal.ofReal p) μ ≤ ENNReal.ofReal A) :
    eLpNorm (fun ω => phi t (J ω)) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (phi t A) := by
  have hJs : AEStronglyMeasurable J μ := hJ.aestronglyMeasurable
  have hKm : AEMeasurable (fun ω => √(J ω * (J ω + 2))) μ :=
    Real.continuous_sqrt.measurable.comp_aemeasurable (hJ.mul (hJ.add_const 2))
  have hKs := hKm.aestronglyMeasurable
  have hP1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  have hP0 : ENNReal.ofReal p ≠ 0 := by
    intro h; rw [ENNReal.ofReal_eq_zero] at h; linarith
  -- bound on the sqrt term
  set M : ℝ := √(A * (A + 2)) with hM
  have hM0 : 0 ≤ M := Real.sqrt_nonneg _
  have hk : eLpNorm (fun ω => √(J ω * (J ω + 2))) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal M := by
    by_contra hlt
    rw [not_le] at hlt
    have h1 : ENNReal.ofReal M ^ 2 <
        eLpNorm (fun ω => √(J ω * (J ω + 2))) (ENNReal.ofReal p) μ ^ 2 := by
      rw [pow_two, pow_two]; exact ENNReal.mul_lt_mul hlt hlt
    have h2 := eLpNorm_sqrt_sq_le hp hJ hJ0 (μ := μ)
    have h3 : eLpNorm J (ENNReal.ofReal p) μ ^ 2 + 2 * eLpNorm J (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal A ^ 2 + 2 * ENNReal.ofReal A := by gcongr
    have h4 : ENNReal.ofReal A ^ 2 + 2 * ENNReal.ofReal A = ENNReal.ofReal M ^ 2 := by
      rw [← ENNReal.ofReal_pow hA, ← ENNReal.ofReal_pow hM0, hM, Real.sq_sqrt (by positivity),
        show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1; ring
    exact absurd (h1.trans_le (h2.trans (h3.trans_eq h4))) (lt_irrefl _)
  -- Minkowski on the three terms
  have e : (fun ω => phi t (J ω)) =
      ((fun _ => cosh t - 1) + (fun ω => cosh t * J ω)) +
        (fun ω => sinh t * √(J ω * (J ω + 2))) := by
    funext ω; simp [phi_eq]
  have hc : 0 ≤ cosh t - 1 := by linarith [Real.one_le_cosh t]
  have hc' : 0 ≤ cosh t := (Real.cosh_pos t).le
  have hs : 0 ≤ sinh t := Real.sinh_nonneg_iff.mpr ht
  rw [e]
  have hA0 : (0 : ℝ) ≤ A * (A + 2) := by positivity
  have n0 : eLpNorm (fun _ : Ω => cosh t - 1) (ENNReal.ofReal p) μ =
      ENNReal.ofReal (cosh t - 1) := by
    rw [eLpNorm_const _ hP0 (IsProbabilityMeasure.ne_zero μ)]
    simp [Real.enorm_eq_ofReal hc]
  have n1 : eLpNorm (fun ω => cosh t * J ω) (ENNReal.ofReal p) μ =
      ENNReal.ofReal (cosh t) * eLpNorm J (ENNReal.ofReal p) μ := by
    have := eLpNorm_const_smul (μ := μ) (p := ENNReal.ofReal p) (cosh t) J
    have hf : (cosh t • J) = fun ω => cosh t * J ω := by funext ω; rfl
    rw [hf] at this
    simpa [Real.enorm_eq_ofReal hc'] using this
  have n2 : eLpNorm (fun ω => sinh t * √(J ω * (J ω + 2))) (ENNReal.ofReal p) μ =
      ENNReal.ofReal (sinh t) *
        eLpNorm (fun ω => √(J ω * (J ω + 2))) (ENNReal.ofReal p) μ := by
    have := eLpNorm_const_smul (μ := μ) (p := ENNReal.ofReal p) (sinh t)
      (fun ω => √(J ω * (J ω + 2)))
    have hf : (sinh t • fun ω => √(J ω * (J ω + 2))) =
        fun ω => sinh t * √(J ω * (J ω + 2)) := by funext ω; rfl
    rw [hf] at this
    simpa [Real.enorm_eq_ofReal hs] using this
  refine (eLpNorm_add_le (μ := μ) (p := ENNReal.ofReal p)
    (f := (fun _ => cosh t - 1) + fun ω => cosh t * J ω)
    (g := fun ω => sinh t * √(J ω * (J ω + 2))) hP1).trans ?_
  refine (add_le_add (eLpNorm_add_le (μ := μ) (p := ENNReal.ofReal p)
    (f := fun _ => cosh t - 1) (g := fun ω => cosh t * J ω) hP1) le_rfl).trans ?_
  rw [n0, n1, n2]
  have hfin : ENNReal.ofReal (phi t A) = ENNReal.ofReal (cosh t - 1) +
      ENNReal.ofReal (cosh t) * ENNReal.ofReal A + ENNReal.ofReal (sinh t) * ENNReal.ofReal M := by
    rw [phi_eq, ← ENNReal.ofReal_mul hc', ← ENNReal.ofReal_mul hs,
      ← ENNReal.ofReal_add hc (by positivity), ← ENNReal.ofReal_add (by positivity)
        (by positivity)]
  rw [hfin]
  gcongr
