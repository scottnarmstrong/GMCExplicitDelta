module

public import GMCExplicitDelta.Haar.MultiplierFactors
public import GMCExplicitDelta.Haar.MultiplierTensor

/-! Sobolev products with components of the scaled plateau gradient. -/
@[expose] public section

open Homogenization MeasureTheory Filter
open scoped Topology ENNReal BigOperators

namespace GMCExplicitDelta.Haar

variable {d : ℕ}

noncomputable def cutoffComponentFactors (ω S : ℝ) (i j : Fin d) : ℝ → ℝ :=
  multiplierFactor ω S (decide (j = i))

noncomputable def cutoffComponentFactorDerivs (ω S : ℝ) (i j : Fin d) : ℝ → ℝ :=
  multiplierFactorDeriv ω S (decide (j = i))

/-- The scaled cutoff-gradient component multiplies H¹ functions with the
explicit tensor product rule. -/
theorem exists_mul_cutoffComponent {U : Set (Vec d)} (u : H1Function U)
    {ω : ℝ} (hω : ω ≤ 1 / 2) (S : ℝ)
    (hU : ∀ᵐ x ∂(volume.restrict U), ∀ j, |x j / S| ≤ 1) (i : Fin d) :
    ∃ h : H1Function U,
      (h.toFun = fun x => tensorMultiplier (cutoffComponentFactors ω S i) x * u.toFun x) ∧
      h.grad = fun x j => tensorMultiplier (cutoffComponentFactors ω S i) x * u.grad x j +
        u.toFun x * tensorDerivative (cutoffComponentFactors ω S i)
          (cutoffComponentFactorDerivs ω S i) x j := by
  classical
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε : ∀ n, 0 < ε n := fun n => by dsimp only [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let fn (n : ℕ) (j : Fin d) := multiplierFactorApprox ω S (ε n) (decide (j = i))
  have hfn (n : ℕ) (j : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (fn n j) :=
    multiplierFactorApprox_contDiff _ _ _ _
  have hderiv (n : ℕ) (j : Fin d) (y : ℝ) :
      deriv (fn n j) y = multiplierFactorDerivApprox ω S (ε n) (decide (j = i)) y :=
    (multiplierFactorApprox_hasDerivAt _ _ _ _ _).deriv
  have hfb (j : Fin d) : ∀ᵐ x ∂(volume.restrict U),
      ‖cutoffComponentFactors ω S i j (x j)‖ ≤ multiplierFactorBound ω S := by
    filter_upwards [hU] with x hx
    exact (multiplierFactor_bounds hω S _ _ (hx j)).1
  have hdfb (j : Fin d) : ∀ᵐ x ∂(volume.restrict U),
      ‖cutoffComponentFactorDerivs ω S i j (x j)‖ ≤ multiplierFactorBound ω S := by
    filter_upwards [hU] with x hx
    exact (multiplierFactor_bounds hω S _ _ (hx j)).2
  have hfnb (n : ℕ) (j : Fin d) : ∀ᵐ x ∂(volume.restrict U),
      ‖fn n j (x j)‖ ≤ multiplierFactorBound ω S := by
    filter_upwards [hU] with x hx
    exact (multiplierFactorApprox_bounds _ _ _ _ _ (hx j)).1
  have hdfnb (n : ℕ) (j : Fin d) : ∀ᵐ x ∂(volume.restrict U),
      ‖deriv (fn n j) (x j)‖ ≤ multiplierFactorBound ω S := by
    filter_upwards [hU] with x hx
    rw [hderiv]
    exact (multiplierFactorApprox_bounds _ _ _ _ _ (hx j)).2
  have hflim (j : Fin d) : ∀ᵐ x ∂(volume.restrict U),
      Tendsto (fun n => fn n j (x j)) atTop (𝓝 (cutoffComponentFactors ω S i j (x j))) :=
    Filter.Eventually.of_forall (fun x => multiplierFactorApprox_tendsto hε hεlim hω S _ (x j))
  have hdflim (j : Fin d) : ∀ᵐ x ∂(volume.restrict U),
      Tendsto (fun n => deriv (fn n j) (x j)) atTop
        (𝓝 (cutoffComponentFactorDerivs ω S i j (x j))) := by
    filter_upwards with x
    simp_rw [hderiv]
    exact multiplierFactorDerivApprox_tendsto hε hεlim hω S _ (x j)
  let h := mulTensorSmoothLimit u (cutoffComponentFactors ω S i)
    (cutoffComponentFactorDerivs ω S i) fn
    (fun j => multiplierFactor_continuous hω S _)
    (fun j => ((multiplierFactorDeriv_measurable ω S _ hω).comp (measurable_pi_apply j)).aestronglyMeasurable)
    hfn (multiplierFactorBound ω S) (multiplierFactorBound_nonneg ω S)
    hfb hdfb hfnb hdfnb hflim hdflim
  exact ⟨h, rfl, rfl⟩

end GMCExplicitDelta.Haar
