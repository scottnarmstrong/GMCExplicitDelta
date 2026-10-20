module

public import GMCExplicitDelta.Proofs.EnergyTest.C1Testing

/-! Compactly supported C¹ multipliers are admissible energy tests. -/

@[expose] public section

open Homogenization MeasureTheory Filter
open scoped Topology ENNReal

namespace GMCExplicitDelta.Localization.EnergyTest

variable {d : ℕ}

/-- Smooth approximation of the Sobolev factor removes any need to mollify
its compactly supported C¹ multiplier. -/
theorem compact_c1_test {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {F : Vec d → Vec d} (hF : IsSolenoidalOn U F) (hFL : ∀ i, MemL2On U (fun x => F x i))
    (w : H1Function U) {χ : Vec d → ℝ} (hχ : ContDiff ℝ 1 χ)
    (hs : HasCompactSupport χ) (hsub : tsupport χ ⊆ U) :
    (∫ x in U, vecDot (F x) (fun i => χ x * w.grad x i + w.toFun x * (fderiv ℝ χ x) (basisVec i))) = 0 := by
  by_cases hne : U.Nonempty
  · obtain ⟨x0, hx0⟩ := hne
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hU.isOpen.mem_nhds hx0)
    let r := δ / 2
    have hr : 0 < r := by dsimp only [r]; positivity
    have hbr : Metric.closedBall x0 r ⊆ U := by
      intro y hy
      apply hball
      rw [Metric.mem_ball]
      have hd : dist y x0 ≤ r := Metric.mem_closedBall.mp hy
      dsimp only [r] at hd
      linarith
    let wn := H1Function.convexApproxSmoothH1 hU w x0 hr
    have hwn (n : ℕ) : ContDiff ℝ 1 (wn n).toFun := by
      change ContDiff ℝ 1 ((H1Function.convexApproxSmoothH1 hU w x0 hr n : H1Function U).toFun)
      rw [show (H1Function.convexApproxSmoothH1 hU w x0 hr n).toFun =
          convexApproxSmoothRepresentative U (unitConvexApproxKernel (d := d)) w x0 r
            (unitConvexApproxScale n) from H1Function.convexApproxSmoothH1_toFun hU w x0 hr n]
      exact (contDiff_convexApproxSmoothRepresentative
        hU.isOpen.measurableSet (isConvexApproxKernel_unitConvexApproxKernel (d := d))
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) w.memL2 hr
        (H1Function.unitConvexApproxScale_pos_meanZero n)).of_le (by simp)
    apply compact_c1_test_of_smooth_approx hU hF hFL w wn hwn
      (fun n x i => ?_) (H1Function.tendsto_convexApproxSmoothH1_toScalarL2 hU w hbr hr)
      (fun i => H1Function.tendsto_convexApproxSmoothH1_gradCoordToScalarL2 hU w hbr hr i) hχ hs hsub
    dsimp only [wn]
    rw [H1Function.convexApproxSmoothH1_grad]
    congr 2
  · have he : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp only [he, Measure.restrict_empty, integral_zero_measure]

end GMCExplicitDelta.Localization.EnergyTest
