module

public import GMCExplicitDelta.Haar.MultiplierProduct
public import Mathlib.Analysis.Calculus.FDeriv.Prod

/-! Tensor multipliers and their coordinate derivatives. -/
@[expose] public section

open Homogenization MeasureTheory Filter
open scoped Topology ENNReal
open scoped BigOperators

namespace GMCExplicitDelta.Haar

variable {d : ℕ}

noncomputable def tensorMultiplier (f : Fin d → ℝ → ℝ) (x : Vec d) : ℝ := ∏ j, f j (x j)

noncomputable def tensorDerivative (f df : Fin d → ℝ → ℝ) (x : Vec d) (i : Fin d) : ℝ :=
  df i (x i) * ∏ j ∈ Finset.univ.erase i, f j (x j)

theorem tensorMultiplier_contDiff (f : Fin d → ℝ → ℝ)
    (hf : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (f j)) :
    ContDiff ℝ (⊤ : ℕ∞) (tensorMultiplier f) := by
  unfold tensorMultiplier
  apply contDiff_prod
  intro j _
  exact (hf j).comp (contDiff_apply ℝ ℝ j)

/-- Only the factor in the chosen coordinate contributes to its partial derivative. -/
theorem tensorMultiplier_fderiv_basis (f : Fin d → ℝ → ℝ)
    (hf : ∀ j, Differentiable ℝ (f j)) (x : Vec d) (i : Fin d) :
    (fderiv ℝ (tensorMultiplier f) x) (basisVec i) =
      tensorDerivative f (fun j => deriv (f j)) x i := by
  classical
  have hj : ∀ j ∈ (Finset.univ : Finset (Fin d)),
      HasFDerivAt (fun y : Vec d => f j (y j))
        (deriv (f j) (x j) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j) x :=
    fun j _ => (hf j (x j)).hasDerivAt.comp_hasFDerivAt x (hasFDerivAt_apply j x)
  unfold tensorMultiplier tensorDerivative
  rw [(HasFDerivAt.finsetProd hj).fderiv]
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, basisVec_apply]
  rw [Finset.sum_eq_single i]
  · rw [ite_eq_left rfl, mul_one]
    ring
  · intro j _ hji
    simp only [ite_eq_right hji, mul_zero]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

theorem norm_tensorMultiplier_le (f : Fin d → ℝ → ℝ) (x : Vec d) {M : ℝ}
    (hf : ∀ j, ‖f j (x j)‖ ≤ M) :
    ‖tensorMultiplier f x‖ ≤ M ^ d := by
  unfold tensorMultiplier
  rw [norm_prod]
  calc
    (∏ j, ‖f j (x j)‖) ≤ ∏ _j : Fin d, M :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => hf j)
    _ = M ^ d := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem norm_tensorDerivative_le (f df : Fin d → ℝ → ℝ) (x : Vec d) (i : Fin d) {M : ℝ}
    (hM : 0 ≤ M) (hf : ∀ j, ‖f j (x j)‖ ≤ M) (hdf : ‖df i (x i)‖ ≤ M) :
    ‖tensorDerivative f df x i‖ ≤ M ^ d := by
  classical
  unfold tensorDerivative
  rw [norm_mul, norm_prod]
  calc
    ‖df i (x i)‖ * ∏ j ∈ Finset.univ.erase i, ‖f j (x j)‖ ≤
        M * ∏ _j ∈ Finset.univ.erase i, M :=
      mul_le_mul hdf
        (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => hf j))
        (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) hM
    _ = ∏ _j : Fin d, M := Finset.mul_prod_erase Finset.univ (fun _ : Fin d => M) (Finset.mem_univ i)
    _ = M ^ d := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Tensor factors with smooth bounded approximations act on H¹ with the
coordinatewise weak product rule. -/
noncomputable def mulTensorSmoothLimit {U : Set (Vec d)} (u : H1Function U)
    (f df : Fin d → ℝ → ℝ) (fn : ℕ → Fin d → ℝ → ℝ)
    (hf : ∀ j, Continuous (f j))
    (hdf : ∀ j, AEStronglyMeasurable (fun x : Vec d => df j (x j)) (volume.restrict U))
    (hfn : ∀ n j, ContDiff ℝ (⊤ : ℕ∞) (fn n j))
    (M : ℝ) (hM : 0 ≤ M)
    (hfb : ∀ j, ∀ᵐ x ∂(volume.restrict U), ‖f j (x j)‖ ≤ M)
    (hdfb : ∀ j, ∀ᵐ x ∂(volume.restrict U), ‖df j (x j)‖ ≤ M)
    (hfnb : ∀ n j, ∀ᵐ x ∂(volume.restrict U), ‖fn n j (x j)‖ ≤ M)
    (hdfnb : ∀ n j, ∀ᵐ x ∂(volume.restrict U), ‖deriv (fn n j) (x j)‖ ≤ M)
    (hflim : ∀ j, ∀ᵐ x ∂(volume.restrict U),
      Tendsto (fun n => fn n j (x j)) atTop (𝓝 (f j (x j))))
    (hdflim : ∀ j, ∀ᵐ x ∂(volume.restrict U),
      Tendsto (fun n => deriv (fn n j) (x j)) atTop (𝓝 (df j (x j)))) : H1Function U := by
  classical
  have hfc (j : Fin d) : Continuous (fun x : Vec d => f j (x j)) :=
    (hf j).comp (continuous_apply j)
  have hft : AEStronglyMeasurable (tensorMultiplier f) (volume.restrict U) :=
    (continuous_finsetProd _ (fun j _ => hfc j)).aestronglyMeasurable
  have hdt (i : Fin d) : AEStronglyMeasurable (fun x => tensorDerivative f df x i)
      (volume.restrict U) :=
    (hdf i).mul (continuous_finsetProd _ (fun j _ => hfc j)).aestronglyMeasurable
  apply mulSmoothLimit u (tensorMultiplier f) (tensorDerivative f df)
    (fun n => tensorMultiplier (fn n)) (fun n => tensorMultiplier_contDiff _ (hfn n))
    hft hdt (M ^ d) (M ^ d)
  · filter_upwards [ae_all_iff.2 hfb] with x hx
    exact norm_tensorMultiplier_le f x hx
  · intro i
    filter_upwards [ae_all_iff.2 hfb, hdfb i] with x hx hy
    exact norm_tensorDerivative_le f df x i hM hx hy
  · intro n
    filter_upwards [ae_all_iff.2 (hfnb n)] with x hx
    exact norm_tensorMultiplier_le (fn n) x hx
  · intro n i
    filter_upwards [ae_all_iff.2 (hfnb n), hdfnb n i] with x hx hy
    rw [tensorMultiplier_fderiv_basis _ (fun j => (hfn n j).differentiable (by simp))]
    exact norm_tensorDerivative_le (fn n) _ x i hM hx hy
  · filter_upwards [ae_all_iff.2 hflim] with x hx
    exact tendsto_finsetProd _ (fun j _ => hx j)
  · intro i
    filter_upwards [ae_all_iff.2 hflim, hdflim i] with x hx hy
    simp_rw [tensorMultiplier_fderiv_basis _ (fun j => (hfn _ j).differentiable (by simp))]
    exact hy.mul (tendsto_finsetProd _ (fun j _ => hx j))

end GMCExplicitDelta.Haar
