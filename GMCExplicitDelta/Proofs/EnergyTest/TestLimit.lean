module

public import GMCExplicitDelta.Proofs.EnergyTest.CompactTest

/-! Dominated convergence for the weak energy tests. -/

@[expose] public section

open Homogenization MeasureTheory Filter
open scoped Topology ENNReal

namespace GMCExplicitDelta.Localization.EnergyTest

variable {d : ℕ}

/-- Uniformly bounded cutoff values and first derivatives allow the energy
pairing to pass to a pointwise limit against a fixed H¹ function and L² flux. -/
theorem product_test_limit {U : Set (Vec d)} (hU : MeasurableSet U)
    {F : Vec d → Vec d} (hF : ∀ i, MemL2On U (fun x => F x i)) (w : H1Function U)
    {χn : ℕ → Vec d → ℝ} {Gn : ℕ → Vec d → Vec d} {χ : Vec d → ℝ} {G : Vec d → Vec d}
    {C : ℝ} (_hC : 0 ≤ C)
    (hχm : ∀ n, AEStronglyMeasurable (χn n) (volume.restrict U))
    (hGm : ∀ n i, AEStronglyMeasurable (fun x => Gn n x i) (volume.restrict U))
    (hχb : ∀ n x, x ∈ U → |χn n x| ≤ C)
    (hGb : ∀ n x, x ∈ U → ∀ i, |Gn n x i| ≤ C)
    (hχlim : ∀ x ∈ U, Tendsto (fun n => χn n x) atTop (𝓝 (χ x)))
    (hGlim : ∀ x ∈ U, ∀ i, Tendsto (fun n => Gn n x i) atTop (𝓝 (G x i))) :
    Tendsto (fun n => ∫ x in U, vecDot (F x)
      (fun i => χn n x * w.grad x i + w.toFun x * Gn n x i)) atTop
      (𝓝 (∫ x in U, vecDot (F x) (fun i => χ x * w.grad x i + w.toFun x * G x i))) := by
  let bound : Vec d → ℝ := fun x => ∑ i, C * (|F x i * w.grad x i| + |F x i * w.toFun x|)
  have hb : Integrable bound (volume.restrict U) :=
    integrable_finsetSum _ (fun i _ =>
      (((hF i).integrable_mul (w.gradMemL2 i)).abs.add ((hF i).integrable_mul w.memL2).abs).const_mul C)
  refine tendsto_integral_of_dominated_convergence bound (fun n => ?_) hb (fun n => ?_) ?_
  · exact Finset.univ.aestronglyMeasurable_fun_sum (fun i _ =>
      (hF i).aestronglyMeasurable.mul
        (((hχm n).mul (w.gradMemL2 i).aestronglyMeasurable).add
          (w.memL2.aestronglyMeasurable.mul (hGm n i))))
  · filter_upwards [ae_restrict_mem hU] with x hx
    simp only [Real.norm_eq_abs]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    have h1 := abs_add_le (χn n x * w.grad x i) (w.toFun x * Gn n x i)
    have h2 := add_le_add
      (mul_le_mul_of_nonneg_right (hχb n x hx) (abs_nonneg (w.grad x i)))
      (mul_le_mul_of_nonneg_left (hGb n x hx i) (abs_nonneg (w.toFun x)))
    simp only [abs_mul] at h1
    have ht := mul_le_mul_of_nonneg_left (h1.trans h2) (abs_nonneg (F x i))
    calc
      _ = |F x i| * |χn n x * w.grad x i + w.toFun x * Gn n x i| := abs_mul _ _
      _ ≤ |F x i| * (C * |w.grad x i| + |w.toFun x| * C) := ht
      _ = _ := by simp only [abs_mul]; ring
  · filter_upwards [ae_restrict_mem hU] with x hx
    exact tendsto_finsetSum _ (fun i _ =>
      (((hχlim x hx).mul_const (w.grad x i)).add
        ((hGlim x hx i).const_mul (w.toFun x))).const_mul (F x i))

end GMCExplicitDelta.Localization.EnergyTest
