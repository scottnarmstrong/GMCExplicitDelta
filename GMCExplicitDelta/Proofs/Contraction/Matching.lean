module

public import GMCExplicitDelta.Assembly.ModelEvents

/-! Monotonicity of the matching factors on the normalized cap interval. -/
@[expose] public section

namespace GMCExplicitDelta.Assembly

open Contract Real

/-- The matching divisor is positive and increasing on the nonnegative half-line. -/
theorem rMatch_pos {x : ℝ} (hx : 0 ≤ x) : 0 < rMatch x := by
  unfold rMatch
  positivity

theorem rMatch_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : rMatch x ≤ rMatch y := by
  unfold rMatch
  exact mul_le_mul (by linarith only [hxy]) (by linarith only [hxy])
    (by linarith only [hx]) (by linarith only [hx, hxy])

/-- On [0,1], the matching ratio decreases. -/
theorem qMatch_antitone {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) :
    qMatch y ≤ qMatch x := by
  have hy0 := hx.trans hxy
  unfold qMatch
  apply (div_le_div_iff₀ (rMatch_pos hy0) (rMatch_pos hx)).2
  have hprod : x * y ≤ 1 := by
    have h := mul_le_mul hxy hy hy0 hy0
    rw [mul_one] at h
    exact h.trans hy
  have heq : cMatch x * rMatch y - cMatch y * rMatch x = (y - x) * (2 - x * y) / 4 := by
    unfold cMatch rMatch
    ring
  have hp := mul_nonneg (sub_nonneg.mpr hxy) (show 0 ≤ 2 - x * y by linarith only [hprod])
  linarith only [heq, hp]

theorem qMatch_pos {x : ℝ} (hx : 0 ≤ x) : 0 < qMatch x := by
  unfold qMatch cMatch
  exact div_pos (by positivity) (rMatch_pos hx)

end GMCExplicitDelta.Assembly
