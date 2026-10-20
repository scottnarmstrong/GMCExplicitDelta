module

public import GMCExplicitDelta.Proofs.EnergyTest.CutoffBound
public import GMCExplicitDelta.Proofs.EnergyTest.TestLimit

/-! Harmonic testing with a C¹ cutoff that vanishes on the boundary. -/

@[expose] public section

open Homogenization MeasureTheory Filter
open scoped Topology ENNReal

namespace GMCExplicitDelta.Localization.EnergyTest

variable {d : ℕ}

/-- The harmonic energy identity for every boundary-vanishing positive C¹ cutoff. -/
theorem boundary_c1_test {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {F : Vec d → Vec d} (hF : IsSolenoidalOn U F) (hFL : ∀ i, MemL2On U (fun x => F x i))
    (w : H1Function U) {χ : Vec d → ℝ} (hχ : ContDiff ℝ 1 χ)
    (hpos : ∀ x ∈ U, 0 < χ x) (hb : ∀ x ∈ closure U, x ∉ U → χ x = 0) :
    (∫ x in U, vecDot (F x) (fun i => χ x * w.grad x i + w.toFun x * (fderiv ℝ χ x) (basisVec i))) = 0 := by
  let τ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hτ (n : ℕ) : 0 < τ n := by dsimp only [τ]; positivity
  have ht : Tendsto τ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose η hηC hηs hηU hηeq using fun n => exists_compact_boundaryRamp hU hχ hb (hτ n)
  have hD (n : ℕ) (x : Vec d) (hx : x ∈ U) (i : Fin d) :
      (fderiv ℝ (η n) x) (basisVec i) =
        boundaryRampDeriv (τ n) (χ x) * (fderiv ℝ χ x) (basisVec i) := by
    have he : η n =ᶠ[𝓝 x] fun y => boundaryRamp (τ n) (χ y) :=
      Filter.mem_of_superset (hU.isOpen.mem_nhds hx) (fun y hy => hηeq n hy)
    have hh := (boundaryRamp_hasDerivAt (hτ n) (χ x)).comp_hasFDerivAt x
      ((hχ.differentiable (by norm_num)).differentiableAt.hasFDerivAt)
    rw [he.fderiv_eq]
    change (fderiv ℝ (boundaryRamp (τ n) ∘ χ) x) (basisVec i) = _
    rw [hh.fderiv]
    rfl
  obtain ⟨C, hC, hχb, hDb⟩ := exists_c1_cutoff_bound hU hχ
  have hz (n : ℕ) := compact_c1_test hU hF hFL w (hηC n) (hηs n) (hηU n)
  have hlim := product_test_limit hU.isOpen.measurableSet hFL w hC
    (fun n => (hηC n).continuous.aestronglyMeasurable)
    (fun n i => (((hηC n).continuous_fderiv (by norm_num)).clm_apply
      (continuous_const (y := basisVec i))).aestronglyMeasurable)
    (fun n x hx => (by rw [hηeq n hx]; exact (abs_boundaryRamp_le (hτ n) (χ x)).trans (hχb x hx)))
    (fun n x hx i => (by
      rw [hD n x hx i, abs_mul]
      have hd := boundaryRampDeriv_bounds (hτ n) (χ x)
      rw [abs_of_nonneg hd.1]
      exact (mul_le_mul_of_nonneg_right hd.2 (abs_nonneg _)).trans (by simpa only [one_mul] using hDb x hx i)))
    (fun x hx => (by
      have hl := (boundaryRamp_limits ht (hpos x hx)).1
      exact hl.congr fun n => (hηeq n hx).symm))
    (fun x hx i => (by
      have hl := (boundaryRamp_limits ht (hpos x hx)).2.mul_const ((fderiv ℝ χ x) (basisVec i))
      simp only [one_mul] at hl
      exact hl.congr fun n => (hD n x hx i).symm))
  simp_rw [hz] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

end GMCExplicitDelta.Localization.EnergyTest
