module

public import GMCExplicitDelta.Haar.TriadicProjection
public import Mathlib.Analysis.SpecificLimits.Normed

/-! Weighted Haar energies and their Abel identities (H1). -/
@[expose] public section

namespace GMCExplicitDelta.Haar

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

/-- Summation by parts for an absolutely summable weighted sequence. -/
theorem weighted_differences (a : ℕ → ℝ) (w : ℝ)
    (ha : Summable (fun k => w ^ k * a k)) :
    a 0 + ∑' k, w ^ (k + 1) * (a (k + 1) - a k) =
      (1 - w) * ∑' k, w ^ k * a k := by
  have hs : Summable (fun k => w ^ (k + 1) * a (k + 1)) :=
    (summable_nat_add_iff 1).2 ha
  have ht : Summable (fun k => w ^ (k + 1) * a k) := by
    simpa only [pow_succ, mul_assoc, mul_left_comm w] using ha.mul_left w
  have heq : (fun k => w ^ (k + 1) * (a (k + 1) - a k)) =
      (fun k => w ^ (k + 1) * a (k + 1) - w ^ (k + 1) * a k) := by
    funext k
    ring
  rw [heq, hs.tsum_sub ht]
  have htail := ha.tsum_eq_zero_add
  simp only [pow_zero, one_mul] at htail
  have hmul : (∑' k, w ^ (k + 1) * a k) = w * ∑' k, w ^ k * a k := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    rw [pow_succ]
    ring
  rw [hmul]
  linarith only [htail]

/-- The series of weighted differences is absolutely summable. -/
theorem summable_weighted_differences (a : ℕ → ℝ) (w : ℝ)
    (ha : Summable (fun k => w ^ k * a k)) :
    Summable (fun k => w ^ (k + 1) * (a (k + 1) - a k)) := by
  have hs : Summable (fun k => w ^ (k + 1) * a (k + 1)) :=
    (summable_nat_add_iff 1).2 ha
  have ht : Summable (fun k => w ^ (k + 1) * a k) := by
    simpa only [pow_succ, mul_assoc, mul_left_comm w] using ha.mul_left w
  simpa only [mul_sub] using hs.sub ht

variable {d : ℕ}

/-- Squared positive-weight Haar norm; the mean is the level-zero term. -/
noncomputable def primalEnergy (Q : TriadicCube d) (q : ℝ) (h : Vec d → ℝ) : ℝ :=
  energy Q (cubeIncrement Q 0 h) +
    ∑' k, q ^ (k + 1) * energy Q (cubeIncrement Q (k + 1) h)

/-- Squared negative-weight Haar norm. Used with `q > 1` and summable terms. -/
noncomputable def dualEnergy (Q : TriadicCube d) (q : ℝ) (f : Vec d → ℝ) : ℝ :=
  primalEnergy Q q⁻¹ f

/-- H1(b), with the convergence hypothesis stated explicitly. -/
theorem dualEnergy_eq_weighted_projections (Q : TriadicCube d) {q : ℝ}
    (_hq : 1 < q) {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hs : Summable (fun k => (q⁻¹) ^ k * energy Q (cubeProjection Q k f))) :
    dualEnergy Q q f = (1 - q⁻¹) *
      ∑' k, (q⁻¹) ^ k * energy Q (cubeProjection Q k f) := by
  unfold dualEnergy primalEnergy
  simp only [cubeIncrement_zero, energy_increment_succ Q _ hf]
  exact weighted_differences (fun k => energy Q (cubeProjection Q k f)) q⁻¹ hs

/-- H1(c). Summability of the weighted residual energies is the explicit
convergence assumption; no unproved completeness premise is hidden in this statement. -/
theorem primalEnergy_eq_abel (Q : TriadicCube d) {q : ℝ} (_hq : 1 < q)
    {h : Vec d → ℝ} (hh : MemLp h 2 (normalizedCubeMeasure Q))
    (hs : Summable (fun j => q ^ j *
      energy Q (fun x => h x - cubeProjection Q j h x))) :
    primalEnergy Q q h = energy Q h + (q - 1) *
      ∑' j, q ^ j * energy Q (fun x => h x - cubeProjection Q j h x) := by
  have heq := weighted_differences
    (fun j => energy Q (fun x => h x - cubeProjection Q j h x)) q hs
  have hd : ∀ k, energy Q (fun x => h x - cubeProjection Q (k + 1) h x) -
      energy Q (fun x => h x - cubeProjection Q k h x) =
      -energy Q (cubeIncrement Q (k + 1) h) := by
    intro k
    rw [energy_residual Q (k + 1) hh, energy_residual Q k hh,
      energy_increment_succ Q k hh]
    ring
  simp_rw [hd, mul_neg] at heq
  rw [tsum_neg, energy_residual Q 0 hh] at heq
  unfold primalEnergy
  rw [cubeIncrement_zero]
  linarith only [heq]

/-- Finite-depth squared Haar norm, including the mean. -/
noncomputable def partialEnergy (Q : TriadicCube d) (q : ℝ) (N : ℕ)
    (f : Vec d → ℝ) : ℝ :=
  ∑ k ∈ Finset.range (N + 1), q ^ k * energy Q (cubeIncrement Q k f)

theorem sqrt_weight_cancel {v a b : ℝ} (hv : 0 < v) :
    Real.sqrt (v⁻¹ * a) * Real.sqrt (v * b) = Real.sqrt a * Real.sqrt b := by
  rw [Real.sqrt_mul (inv_nonneg.mpr hv.le), Real.sqrt_mul hv.le]
  have h : Real.sqrt v⁻¹ * Real.sqrt v = 1 := by
    rw [← Real.sqrt_mul (inv_nonneg.mpr hv.le), inv_mul_cancel₀ hv.ne', Real.sqrt_one]
  calc
    Real.sqrt v⁻¹ * Real.sqrt a * (Real.sqrt v * Real.sqrt b) =
      (Real.sqrt v⁻¹ * Real.sqrt v) * (Real.sqrt a * Real.sqrt b) := by ring
    _ = Real.sqrt a * Real.sqrt b := by rw [h, one_mul]

/-- H1(a) for the actual finite-depth projections. -/
theorem abs_pairing_projections_le (Q : TriadicCube d) {q : ℝ} (hq : 1 < q)
    (N : ℕ) {f h : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hh : MemLp h 2 (normalizedCubeMeasure Q)) :
    |pairing Q (cubeProjection Q N f) (cubeProjection Q N h)| ≤
      Real.sqrt (partialEnergy Q q⁻¹ N f) * Real.sqrt (partialEnergy Q q N h) := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  rw [pairing_projection_sum Q N hf hh]
  calc
    |∑ k ∈ Finset.range (N + 1), pairing Q (cubeIncrement Q k f) (cubeIncrement Q k h)| ≤
        ∑ k ∈ Finset.range (N + 1), |pairing Q (cubeIncrement Q k f) (cubeIncrement Q k h)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (N + 1),
        Real.sqrt ((q ^ k)⁻¹ * energy Q (cubeIncrement Q k f)) *
        Real.sqrt (q ^ k * energy Q (cubeIncrement Q k h)) := by
      apply Finset.sum_le_sum
      intro k _
      rw [sqrt_weight_cancel (pow_pos hq0 k)]
      exact abs_pairing_le Q (increment_memLp Q k f) (increment_memLp Q k h)
    _ ≤ Real.sqrt (partialEnergy Q q⁻¹ N f) * Real.sqrt (partialEnergy Q q N h) := by
      simpa only [partialEnergy, inv_pow] using
        Real.sum_sqrt_mul_sqrt_le (Finset.range (N + 1))
          (fun k => mul_nonneg (inv_nonneg.mpr (pow_nonneg hq0.le k)) (energy_nonneg Q _))
          (fun k => mul_nonneg (pow_nonneg hq0.le k) (energy_nonneg Q _))

/-- Discounted projection energies are summable for every L² field. -/
theorem summable_weighted_projections (Q : TriadicCube d) {q : ℝ} (hq : 1 < q)
    {f : Vec d → ℝ} (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    Summable (fun k => (q⁻¹) ^ k * energy Q (cubeProjection Q k f)) := by
  have hw0 : 0 ≤ q⁻¹ := inv_nonneg.mpr (le_trans zero_le_one hq.le)
  have hw1 : q⁻¹ < 1 := (inv_lt_one₀ (lt_trans zero_lt_one hq)).2 hq
  apply ((summable_geometric_of_lt_one hw0 hw1).mul_right (energy Q f)).of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hw0 k) (energy_nonneg Q _))]
  exact mul_le_mul_of_nonneg_left (energy_projection_le Q k hf) (pow_nonneg hw0 k)

/-- H1(b) without a separate convergence hypothesis. -/
theorem dualEnergy_eq (Q : TriadicCube d) {q : ℝ} (hq : 1 < q)
    {f : Vec d → ℝ} (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    dualEnergy Q q f = (1 - q⁻¹) *
      ∑' k, (q⁻¹) ^ k * energy Q (cubeProjection Q k f) :=
  dualEnergy_eq_weighted_projections Q hq hf (summable_weighted_projections Q hq hf)

/-- The dual energy really is a convergent series for L² fields. -/
theorem summable_dual_increments (Q : TriadicCube d) {q : ℝ} (hq : 1 < q)
    {f : Vec d → ℝ} (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    Summable (fun k => (q⁻¹) ^ (k + 1) * energy Q (cubeIncrement Q (k + 1) f)) := by
  simpa only [energy_increment_succ Q _ hf] using
    summable_weighted_differences (fun k => energy Q (cubeProjection Q k f)) q⁻¹
      (summable_weighted_projections Q hq hf)

/-- The residual convergence hypothesis in Abel's identity ensures the primal
Haar series is summable as well. -/
theorem summable_primal_increments_of_residuals (Q : TriadicCube d) (q : ℝ)
    {h : Vec d → ℝ} (hh : MemLp h 2 (normalizedCubeMeasure Q))
    (hs : Summable (fun j => q ^ j *
      energy Q (fun x => h x - cubeProjection Q j h x))) :
    Summable (fun k => q ^ (k + 1) * energy Q (cubeIncrement Q (k + 1) h)) := by
  have ht := summable_weighted_differences
    (fun j => energy Q (fun x => h x - cubeProjection Q j h x)) q hs
  have heq : ∀ k, -(q ^ (k + 1) *
      (energy Q (fun x => h x - cubeProjection Q (k + 1) h x) -
        energy Q (fun x => h x - cubeProjection Q k h x))) =
      q ^ (k + 1) * energy Q (cubeIncrement Q (k + 1) h) := by
    intro k
    rw [energy_residual Q (k + 1) hh, energy_residual Q k hh,
      energy_increment_succ Q k hh]
    ring
  simpa only [heq] using ht.neg

/-- Finite weighted norms tend to the norm defined by the convergent series. -/
theorem partialEnergy_tendsto (Q : TriadicCube d) (q : ℝ) (f : Vec d → ℝ)
    (hs : Summable (fun k => q ^ (k + 1) * energy Q (cubeIncrement Q (k + 1) f))) :
    Filter.Tendsto (fun N => partialEnergy Q q N f) Filter.atTop (nhds (primalEnergy Q q f)) := by
  have hall : Summable (fun k => q ^ k * energy Q (cubeIncrement Q k f)) :=
    (summable_nat_add_iff 1).1 hs
  have heq : (∑' k, q ^ k * energy Q (cubeIncrement Q k f)) = primalEnergy Q q f := by
    rw [hall.tsum_eq_zero_add]
    simp only [pow_zero, one_mul, primalEnergy]
  simpa only [partialEnergy, heq, Function.comp_def] using
    hall.hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)

/-- Passage from finite-depth duality to a limiting pairing. The pairing
convergence is explicit: this lemma makes no claim of Haar completeness. -/
theorem abs_pairing_le_dual_primal_of_pairing_limit (Q : TriadicCube d) {q : ℝ}
    (hq : 1 < q) {f h : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hh : MemLp h 2 (normalizedCubeMeasure Q))
    (hs : Summable (fun k => q ^ (k + 1) * energy Q (cubeIncrement Q (k + 1) h)))
    (hlim : Filter.Tendsto
      (fun N => pairing Q (cubeProjection Q N f) (cubeProjection Q N h))
      Filter.atTop (nhds (pairing Q f h))) :
    |pairing Q f h| ≤ Real.sqrt (dualEnergy Q q f) * Real.sqrt (primalEnergy Q q h) := by
  have hleft := hlim.abs
  have hdual := partialEnergy_tendsto Q q⁻¹ f (summable_dual_increments Q hq hf)
  have hprimal := partialEnergy_tendsto Q q h hs
  exact le_of_tendsto_of_tendsto' hleft (hdual.sqrt.mul hprimal.sqrt)
    (fun N => abs_pairing_projections_le Q hq N hf hh)

end GMCExplicitDelta.Haar
