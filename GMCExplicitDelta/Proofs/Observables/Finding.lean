module

public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Tactic.NormNum

/-! A threshold obstruction in the unrestricted-real-F statement of target G8.
This checks the Markov implication's scalar counterexample, not a counterexample
constructed in the GMC model. -/
@[expose] public section

open scoped ENNReal

namespace GMCExplicitDelta.Assembly

/-- With F = -1, theta = 1/2 and statistic 1, the bad-event threshold holds
but the claimed excess threshold does not. -/
theorem negative_cap_threshold_counterexample :
    (-1 : ℝ) < 1 / 2 ∧
      ENNReal.ofReal (1 / 2 : ℝ) < (1 : ℝ≥0∞) ∧
      ¬ ENNReal.ofReal ((1 / 2 : ℝ) - (-1)) ≤
        (1 : ℝ≥0∞) - ENNReal.ofReal (-1) := by
  rw [ENNReal.ofReal_of_nonpos (by norm_num : (-1 : ℝ) ≤ 0)]
  norm_num

/-- On a one-point probability space, the corresponding proposed Markov
conclusion would bound probability one by (2/3)^32. -/
theorem negative_cap_probability_counterexample :
    ¬ (1 : ℝ≥0∞) ≤ ENNReal.ofReal (((1 : ℝ) / (1 / 2 - (-1))) ^ 32) := by
  norm_num

end GMCExplicitDelta.Assembly
