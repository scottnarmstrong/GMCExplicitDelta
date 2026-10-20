module

public import GMCExplicitDelta.Proofs.GridMax.Grid
public import GMCExplicitDelta.HistoryLane.Split
public import GMCExplicitDelta.Insertion.FreshSeedNorm
public import GMCExplicitDelta.Proofs.FineSensitivity.Shift
public import GMCExplicitDelta.Proofs.Normalization.Drift

/-! # A simultaneous affine trial for all subcells of a unit cube -/

@[expose] public section

open Homogenization Homogenization.Book.Ch02 MeasureTheory
open SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

namespace GMCExplicitDelta.Assembly.GridMax

variable {d : ℕ}

/-- Translation preserves descendant containment for the actual open domains. -/
theorem cellAt_subset {R S : Homogenization.TriadicCube d} {k : ℕ} (z : Homogenization.Vec d)
    (hS : S ∈ descendantsAtDepth R k) :
    (cellAt z S : Set (Homogenization.Vec d)) ⊆ cellAt z R := by
  intro x hx
  change x ∈ translateSet z (openCubeSet S) at hx
  change x ∈ translateSet z (openCubeSet R)
  rw [mem_translateSet_iff_sub_mem] at hx ⊢
  exact openCubeSet_subset_of_mem_descendantsAtDepth hS hx

/-- The elementary cosh trial with a uniform absolute logarithm bound. -/
theorem cosh_trial_le {v T : ℝ} (hT : 0 ≤ T) (hv : |v| ≤ T) :
    Real.cosh v - 1 ≤ T ^ 2 * Real.exp T / 2 := by
  have h := fine_exp_symmetric_le v
  have hsq : v ^ 2 ≤ T ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hT).2 hv
  have hm := mul_le_mul hsq (Real.exp_le_exp.2 hv) (Real.exp_pos _).le (sq_nonneg T)
  rw [Real.cosh_eq]
  linarith only [h, hm]

/-- Almost every point for the normalized volume lies in its domain. -/
theorem ae_domainProbability (U : Domain d) : ∀ᵐ x ∂domainProbability U, x ∈ (U : Set (Homogenization.Vec d)) := by
  unfold domainProbability BoundedMeasurableDomain.normalizedVolume
  exact Measure.ae_smul_measure (ae_restrict_mem U.measurableSet) _

/-- A uniform logarithm bound controls every descendant defect at once. -/
theorem subcellMax_le_trial [NeZero d] (M : GMCModel d) (L : ℕ) (z : Homogenization.Vec d)
    (R : Homogenization.TriadicCube d) (ω : PotentialSample d) (ha : 0 < ahom M L) {T : ℝ} (hT : 0 ≤ T)
    (hlog : ∀ x ∈ (cellAt z R : Set (Homogenization.Vec d)), |layerPrefix L ω x - normShift M L| ≤ T) :
    subcellMax M L z R ω ≤ ENNReal.ofReal (T ^ 2 * Real.exp T / 2) := by
  classical
  unfold subcellMax
  refine iSup_le fun k => Finset.sup_le fun S hS => ?_
  refine (normalizedDefect_le_affine M L (cellAt z S) ω ha).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [average_eq_integral_domainProbability]
  have hc : Continuous (fun x : Homogenization.Vec d =>
      Real.cosh ((∑ i ∈ Finset.range (L + 1), ω i x) - normShift M L) - 1) :=
    (Real.continuous_cosh.comp ((continuous_finsetSum _ fun i _ => (ω i).1.1.continuous).sub continuous_const)).sub continuous_const
  have hi := integrable_domainProbability_of_continuous (U := cellAt z S) hc
  calc
    _ ≤ ∫ _x, T ^ 2 * Real.exp T / 2 ∂domainProbability (cellAt z S) := by
      apply integral_mono_ae hi (integrable_const _)
      filter_upwards [ae_domainProbability (cellAt z S)] with x hx
      exact cosh_trial_le hT (hlog x (cellAt_subset z hS hx))
    _ = _ := by simp

end GMCExplicitDelta.Assembly.GridMax
