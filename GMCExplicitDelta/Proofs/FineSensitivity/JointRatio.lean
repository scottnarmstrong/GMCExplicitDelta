module

public import GMCExplicitDelta.Proofs.FineSensitivity.Ratio
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap

/-! # Spatial continuity and joint measurability of the fresh ratio -/

@[expose] public section

open MeasureTheory Homogenization SubdiffusiveProcess.Model

namespace GMCExplicitDelta.Assembly

variable {d : ℕ}

theorem continuous_fineBand (k L : ℕ) (ω : PotentialSample d) :
    Continuous (fineBand k L ω) :=
  continuous_finsetSum _ (fun i _ => (ω i).1.1.continuous)

theorem measurable_fineBand_uncurry (k L : ℕ) :
    Measurable (fun p : PotentialSample d × Vec d => fineBand k L p.1 p.2) := by
  have hm (x : Vec d) : Measurable (fun ω : PotentialSample d => fineBand k L ω x) :=
    Finset.measurable_sum _ (fun i _ =>
      (PotentialField.measurable_eval x).comp (measurable_pi_apply i))
  have hs := measurable_uncurry_of_continuous_of_measurable
    (continuous_fineBand k L) hm
  exact hs.comp measurable_swap

theorem continuous_cutoffRatio (M : GMCModel d) {k L : ℕ} (hkL : k ≤ L)
    (ω : PotentialSample d) : Continuous (cutoffRatio M k L ω) := by
  change Continuous (fun x => cutoffRatio M k L ω x)
  simp_rw [cutoffRatio_eq_exp M hkL]
  exact Real.continuous_exp.comp ((continuous_fineBand k L ω).sub continuous_const)

theorem measurable_cutoffRatio_uncurry (M : GMCModel d) {k L : ℕ} (hkL : k ≤ L) :
    Measurable (fun p : PotentialSample d × Vec d => cutoffRatio M k L p.1 p.2) := by
  simp_rw [cutoffRatio_eq_exp M hkL]
  exact ((measurable_fineBand_uncurry k L).sub measurable_const).exp

end GMCExplicitDelta.Assembly
