module

public import GMCExplicitDelta.Proofs.EnergyTest.TestSpace

/-! Continuity of compact C¹ testing in the Sobolev function. -/

@[expose] public section

open Homogenization MeasureTheory Filter
open scoped Topology ENNReal RealInnerProductSpace

namespace GMCExplicitDelta.Localization.EnergyTest

variable {d : ℕ}

/-- A continuous multiplier on the compact closure preserves spatial L². -/
theorem continuous_mul_memL2 {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {f g : Vec d → ℝ} (hf : MemL2On U f) (hg : Continuous g) :
    MemL2On U (fun x => g x * f x) := by
  obtain ⟨C, hC⟩ := hU.isBoundedDomain.isBounded.isCompact_closure.exists_bound_of_continuousOn hg.continuousOn
  refine MemLp.of_le (hf.const_mul (max C 0))
    (hg.aestronglyMeasurable.mul hf.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem hU.isOpen.measurableSet] with x hx
  simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (le_max_right C 0)]
  exact mul_le_mul_of_nonneg_right ((hC x (subset_closure hx)).trans (le_max_left C 0)) (abs_nonneg _)

theorem inner_toScalarL2_eq_integral {U : Set (Vec d)} {f g : Vec d → ℝ}
    (hf : MemL2On U f) (hg : MemL2On U g) :
    inner ℝ (toScalarL2 hf) (toScalarL2 hg) = ∫ x in U, f x * g x := by
  rw [scalarInner_eq_integral]
  apply integral_congr_ae
  filter_upwards [coeFn_toScalarL2 hf, coeFn_toScalarL2 hg] with x hx hy
  rw [hx, hy]

/-- Scalar L² inner products express the flux pairing with the product-rule gradient. -/
theorem product_test_eq_inner {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {F : Vec d → Vec d} (hF : ∀ i, MemL2On U (fun x => F x i))
    (w : H1Function U) {χ : Vec d → ℝ} (hχ : ContDiff ℝ 1 χ) :
    (∫ x in U, vecDot (F x) (fun i => χ x * w.grad x i + w.toFun x * (fderiv ℝ χ x) (basisVec i))) =
      ∑ i, (inner ℝ (toScalarL2 (continuous_mul_memL2 hU (hF i) hχ.continuous)) (w.gradCoordToScalarL2 i) +
        inner ℝ (toScalarL2 (continuous_mul_memL2 hU (hF i)
          ((hχ.continuous_fderiv (by norm_num)).clm_apply (continuous_const (y := basisVec i))))) w.toScalarL2) := by
  have hχF i := continuous_mul_memL2 hU (hF i) hχ.continuous
  have hDF i := continuous_mul_memL2 hU (hF i)
    ((hχ.continuous_fderiv (by norm_num)).clm_apply (continuous_const (y := basisVec i)))
  have hi i : Integrable (fun x => F x i *
      (χ x * w.grad x i + w.toFun x * (fderiv ℝ χ x) (basisVec i))) (volume.restrict U) := by
    convert ((hχF i).integrable_mul (w.gradMemL2 i)).add ((hDF i).integrable_mul w.memL2) using 1
    funext x
    simp only [Pi.add_apply, Pi.mul_apply]
    ring
  change (∫ x in U, ∑ i, F x i * (χ x * w.grad x i + w.toFun x * (fderiv ℝ χ x) (basisVec i))) = _
  rw [integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  change (∫ x in U, F x i * (χ x * w.grad x i + w.toFun x * (fderiv ℝ χ x) (basisVec i))) =
    inner ℝ (toScalarL2 (hχF i)) (toScalarL2 (w.gradMemL2 i)) +
      inner ℝ (toScalarL2 (hDF i)) (toScalarL2 w.memL2)
  rw [inner_toScalarL2_eq_integral, inner_toScalarL2_eq_integral]
  calc
    _ = ∫ x in U, (χ x * F x i * w.grad x i) + ((fderiv ℝ χ x) (basisVec i) * F x i * w.toFun x) := by
      apply integral_congr_ae
      filter_upwards with x
      ring
    _ = _ := integral_add ((hχF i).integrable_mul (w.gradMemL2 i)) ((hDF i).integrable_mul w.memL2)

/-- Compact C¹ testing is stable under convergence of the value and gradient in L². -/
theorem compact_c1_test_of_smooth_approx {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {F : Vec d → Vec d} (hF : IsSolenoidalOn U F)
    (hFL : ∀ i, MemL2On U (fun x => F x i)) (w : H1Function U)
    (wn : ℕ → H1Function U) (hwn : ∀ n, ContDiff ℝ 1 (wn n).toFun)
    (hDwn : ∀ n x i, (wn n).grad x i = (fderiv ℝ (wn n).toFun x) (basisVec i))
    (hval : Tendsto (fun n => (wn n).toScalarL2) atTop (𝓝 w.toScalarL2))
    (hgrad : ∀ i, Tendsto (fun n => (wn n).gradCoordToScalarL2 i) atTop (𝓝 (w.gradCoordToScalarL2 i)))
    {χ : Vec d → ℝ} (hχ : ContDiff ℝ 1 χ) (hs : HasCompactSupport χ) (hsub : tsupport χ ⊆ U) :
    (∫ x in U, vecDot (F x) (fun i => χ x * w.grad x i + w.toFun x * (fderiv ℝ χ x) (basisVec i))) = 0 := by
  have hzero (n : ℕ) :
      (∫ x in U, vecDot (F x) (fun i => χ x * (wn n).grad x i + (wn n).toFun x * (fderiv ℝ χ x) (basisVec i))) = 0 := by
    have hz := integral_flux_fderiv_eq_zero hU hF (hχ.mul (hwn n))
      (hs.mul_right (f' := (wn n).toFun))
      ((tsupport_mul_subset_left (f := χ) (g := (wn n).toFun)).trans hsub)
    convert hz using 1
    apply integral_congr_ae
    filter_upwards with x
    congr 1
    funext i
    rw [show (fun x => χ x * (wn n).toFun x) = χ * (wn n).toFun from rfl,
      fderiv_mul (hχ.differentiable (by norm_num)).differentiableAt
        ((hwn n).differentiable (by norm_num)).differentiableAt]
    simp only [add_apply, smul_apply, smul_eq_mul, hDwn]
  let A (i : Fin d) : ScalarL2 U := toScalarL2 (continuous_mul_memL2 hU (hFL i) hχ.continuous)
  let B (i : Fin d) : ScalarL2 U := toScalarL2 (continuous_mul_memL2 hU (hFL i)
    ((hχ.continuous_fderiv (by norm_num)).clm_apply (continuous_const (y := basisVec i))))
  let P (v : H1Function U) : ℝ := ∑ i,
    (inner ℝ (A i) (v.gradCoordToScalarL2 i) + inner ℝ (B i) v.toScalarL2)
  have hlim : Tendsto (fun n => P (wn n)) atTop (𝓝 (P w)) := by
    dsimp only [P]
    apply tendsto_finsetSum
    intro i _
    exact ((tendsto_const_nhds (x := A i)).inner (hgrad i)).add
      ((tendsto_const_nhds (x := B i)).inner hval)
  have heq (n : ℕ) : P (wn n) = 0 :=
    (product_test_eq_inner hU hFL (wn n) hχ).symm.trans (hzero n)
  simp_rw [heq] at hlim
  exact (product_test_eq_inner hU hFL w hχ).trans
    (tendsto_nhds_unique hlim tendsto_const_nhds)

end GMCExplicitDelta.Localization.EnergyTest
