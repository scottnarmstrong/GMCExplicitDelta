module

public import GMCExplicitDelta.Proofs.LocWeights.Abel

/-! Homogeneity of the minimum series in the H9 bound. -/
@[expose] public section

namespace GMCExplicitDelta.Localization.Multiplier

open Contract

theorem minSeries_mul_nonneg (q A H c : ℝ) (hc : 0 ≤ c) :
    minSeries q (A * c) (H * c) = minSeries q A H * c := by
  unfold minSeries
  rw [← tsum_mul_right]
  apply tsum_congr
  intro j
  rw [show H * c / 9 ^ j = (H / 9 ^ j) * c by ring, ← min_mul_of_nonneg _ _ hc]
  ring

end GMCExplicitDelta.Localization.Multiplier
