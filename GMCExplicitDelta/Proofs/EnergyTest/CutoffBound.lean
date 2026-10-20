module

public import GMCExplicitDelta.Proofs.EnergyTest.InteriorCutoff

/-! Uniform bounds for a C¹ cutoff and its coordinate derivatives. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped Topology

namespace GMCExplicitDelta.Localization.EnergyTest

variable {d : ℕ}

theorem exists_c1_cutoff_bound {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {χ : Vec d → ℝ} (hχ : ContDiff ℝ 1 χ) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ x ∈ U, |χ x| ≤ C) ∧
      ∀ x ∈ U, ∀ i, |(fderiv ℝ χ x) (basisVec i)| ≤ C := by
  have hK := hU.isBoundedDomain.isBounded.isCompact_closure
  obtain ⟨C0, h0⟩ := hK.exists_bound_of_continuousOn hχ.continuous.continuousOn
  have hi (i : Fin d) := hK.exists_bound_of_continuousOn
    (((hχ.continuous_fderiv (by norm_num)).clm_apply (continuous_const (y := basisVec i))).continuousOn)
  choose Ci hCi using hi
  let C := max C0 0 + ∑ i, max (Ci i) 0
  have hsum : 0 ≤ ∑ i, max (Ci i) 0 := Finset.sum_nonneg fun i _ => le_max_right _ _
  refine ⟨C, add_nonneg (le_max_right _ _) hsum, ?_, ?_⟩
  · intro x hx
    have hh : |χ x| ≤ C0 := by simpa only [Real.norm_eq_abs] using h0 x (subset_closure hx)
    exact hh.trans ((le_max_left _ _).trans (le_add_of_nonneg_right hsum))
  · intro x hx i
    have hh : |(fderiv ℝ χ x) (basisVec i)| ≤ Ci i := by
      simpa only [Real.norm_eq_abs] using hCi i x (subset_closure hx)
    have hs : max (Ci i) 0 ≤ ∑ j, max (Ci j) 0 :=
      Finset.single_le_sum (fun j _ => le_max_right _ _) (Finset.mem_univ i)
    exact hh.trans ((le_max_left _ _).trans (hs.trans (le_add_of_nonneg_left (le_max_right C0 0))))

end GMCExplicitDelta.Localization.EnergyTest
