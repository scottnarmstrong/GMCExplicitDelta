module

public import GMCExplicitDelta.Insertion.FreshSeedNorm

/-! # Joint measurability of the finite fresh field -/

@[expose] public section

open MeasureTheory Homogenization SubdiffusiveProcess.Model
open SubdiffusiveProcess.Model.PotentialField

namespace GMCExplicitDelta.Insertion

/-- The finite fresh sum is jointly measurable in the sample and the spatial point. -/
theorem measurable_layer_sum_uncurry {d : ℕ} (I : Finset ℕ) :
    Measurable (fun q : PotentialSample d × Vec d => ∑ k ∈ I, q.1 k q.2) := by
  let T : PotentialSample d → Vec d → ℝ := fun ω x => ∑ k ∈ I, ω k x
  have hc (ω : PotentialSample d) : Continuous (T ω) :=
    continuous_finsetSum I (fun k _ => (ω k).1.1.continuous)
  have hm (x : Vec d) : Measurable (fun ω : PotentialSample d => T ω x) :=
    Finset.measurable_sum I (fun k _ => (measurable_eval x).comp (measurable_pi_apply k))
  have hs : Measurable (fun q : Vec d × PotentialSample d => T q.2 q.1) :=
    measurable_uncurry_of_continuous_of_measurable hc hm
  exact Assembly.measurable_uncurry_of_swapped T hs

end GMCExplicitDelta.Insertion
