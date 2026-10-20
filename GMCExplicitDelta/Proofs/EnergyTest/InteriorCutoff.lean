module

public import GMCExplicitDelta.Proofs.EnergyTest.Ramp
public import GMCExplicitDelta.Proofs.EnergyTest.CompactTest

/-! Interior compactification of a boundary-vanishing C¹ cutoff. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped Topology

namespace GMCExplicitDelta.Localization.EnergyTest

variable {d : ℕ}

/-- Positive cutoff levels are compactly contained in the domain. A smooth
bump on such a level compactifies the C¹ truncation without altering it on U. -/
theorem exists_compact_boundaryRamp {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {χ : Vec d → ℝ} (hχ : ContDiff ℝ 1 χ)
    (hb : ∀ x ∈ closure U, x ∉ U → χ x = 0) {τ : ℝ} (hτ : 0 < τ) :
    ∃ η : Vec d → ℝ, ContDiff ℝ 1 η ∧ HasCompactSupport η ∧ tsupport η ⊆ U ∧
      Set.EqOn η (fun x => boundaryRamp τ (χ x)) U := by
  classical
  let K := closure U ∩ {x | τ ≤ χ x}
  have hK : IsCompact K := hU.isBoundedDomain.isBounded.isCompact_closure.inter_right
    (isClosed_le continuous_const hχ.continuous)
  have hKU : K ⊆ U := by
    intro x hx
    by_contra hxU
    have hz := hb x hx.1 hxU
    have ht := hx.2
    change τ ≤ χ x at ht
    rw [hz] at ht
    exact (not_le.mpr hτ) ht
  obtain ⟨ρ, hρ, _, hρone, hρsub⟩ := exists_contDiff_one_on_compact_tsupport_subset hK hKU hU.isOpen
  have hρc : HasCompactSupport ρ :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_tsupport ρ)
      (hU.isBoundedDomain.isBounded.subset hρsub)
  refine ⟨fun x => ρ x * boundaryRamp τ (χ x),
    (hρ.of_le (by simp)).mul ((boundaryRamp_contDiff hτ).comp hχ), hρc.mul_right,
    tsupport_mul_subset_left.trans hρsub, ?_⟩
  intro x hx
  change ρ x * boundaryRamp τ (χ x) = boundaryRamp τ (χ x)
  by_cases ht : χ x ≤ τ
  · rw [boundaryRamp_eq_zero ht, mul_zero]
  · have hr : ρ x = 1 := by
      simpa using hρone (show x ∈ K from ⟨subset_closure hx, (not_le.mp ht).le⟩)
    rw [hr, one_mul]

end GMCExplicitDelta.Localization.EnergyTest
