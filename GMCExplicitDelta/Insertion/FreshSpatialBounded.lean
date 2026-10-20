module

public import GMCExplicitDelta.Insertion.FreshSeedNorm
public import Mathlib.Analysis.Normed.Group.Bounded

/-! # Continuous multipliers on a deterministic bounded spatial domain -/

@[expose] public section

open MeasureTheory Homogenization Homogenization.Book.Ch02

namespace GMCExplicitDelta.Insertion

/-- A continuous multiplier is bounded on the closure of the spatial domain. -/
theorem integrable_domainProbability_mul_continuous {d : ℕ} {U : Domain d}
    {f g : Vec d → ℝ} (hf : Integrable f (Assembly.domainProbability U)) (hg : Continuous g) :
    Integrable (fun x => f x * g x) (Assembly.domainProbability U) := by
  have hc : IsCompact (closure (U : Set (Vec d))) :=
    U.isBoundedDomain.isBounded.isCompact_closure
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn hg.continuousOn
  have ha : ∀ᵐ x ∂Assembly.domainProbability U, x ∈ (U : Set (Vec d)) :=
    Measure.ae_smul_measure (ae_restrict_mem U.isOpen.measurableSet) _
  exact hf.mul_bdd hg.measurable.aestronglyMeasurable
    (ha.mono fun x hx => hC x (subset_closure hx))

end GMCExplicitDelta.Insertion
