module

public import Homogenization.Sobolev.H1.Algebra.H1Function
public import Homogenization.Sobolev.Truncation.WeakGradientLimit

/-! Multiplication in H¹ by bounded multipliers obtained from smooth approximations. -/
@[expose] public section

open Homogenization MeasureTheory Filter
open scoped Topology ENNReal

namespace GMCExplicitDelta.Haar

variable {d : ℕ} {U : Set (Vec d)}

/-- A bounded smooth approximation, with uniformly bounded first derivatives and
almost-everywhere convergence of those derivatives, gives the weak product rule.
The approximations need not converge uniformly in their derivatives. -/
noncomputable def mulSmoothLimit (u : H1Function U)
    (φ : Vec d → ℝ) (Dφ : Vec d → Vec d) (φn : ℕ → Vec d → ℝ)
    (hφn : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (φn n))
    (hφ : AEStronglyMeasurable φ (volume.restrict U))
    (hDφ : ∀ i, AEStronglyMeasurable (fun x => Dφ x i) (volume.restrict U))
    (C B : ℝ)
    (hφ_bound : ∀ᵐ x ∂(volume.restrict U), ‖φ x‖ ≤ C)
    (hDφ_bound : ∀ i, ∀ᵐ x ∂(volume.restrict U), ‖Dφ x i‖ ≤ B)
    (hφn_bound : ∀ n, ∀ᵐ x ∂(volume.restrict U), ‖φn n x‖ ≤ C)
    (hDφn_bound : ∀ n i, ∀ᵐ x ∂(volume.restrict U),
      ‖(fderiv ℝ (φn n) x) (basisVec i)‖ ≤ B)
    (hφn_lim : ∀ᵐ x ∂(volume.restrict U),
      Tendsto (fun n => φn n x) atTop (𝓝 (φ x)))
    (hDφn_lim : ∀ i, ∀ᵐ x ∂(volume.restrict U),
      Tendsto (fun n => (fderiv ℝ (φn n) x) (basisVec i)) atTop (𝓝 (Dφ x i))) :
    H1Function U := by
  let μ := volume.restrict U
  have hφ_top : MemLp φ ⊤ μ := memLp_top_of_bound hφ C hφ_bound
  have hDφ_top (i : Fin d) : MemLp (fun x => Dφ x i) ⊤ μ :=
    memLp_top_of_bound (hDφ i) B (hDφ_bound i)
  have hφn_top (n : ℕ) : MemLp (φn n) ⊤ μ :=
    memLp_top_of_bound (hφn n).continuous.aestronglyMeasurable C (hφn_bound n)
  have hDφn_top (n : ℕ) (i : Fin d) :
      MemLp (fun x => (fderiv ℝ (φn n) x) (basisVec i)) ⊤ μ :=
    memLp_top_of_bound
      (((hφn n).continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable
      B (hDφn_bound n i)
  let v (n : ℕ) := u.mulContDiffMemLpTop (hφn n) (hφn_top n) (hDφn_top n)
  have hv (n : ℕ) : (v n).toFun = fun x => φn n x * u.toFun x := rfl
  have hDv (n : ℕ) : (v n).grad = fun x i =>
      φn n x * u.grad x i + u.toFun x * (fderiv ℝ (φn n) x) (basisVec i) := rfl
  have hmem : MemLp (fun x => φ x * u.toFun x) 2 μ := hφ_top.fun_mul u.memL2
  have hDmem (i : Fin d) : MemLp
      (fun x => φ x * u.grad x i + u.toFun x * Dφ x i) 2 μ :=
    (hφ_top.fun_mul (u.gradMemL2 i)).add (by
      simpa only [mul_comm] using (hDφ_top i).fun_mul (r := 2) u.memL2)
  have hlim : Tendsto (fun n => eLpNorm
      (fun x => (v n).toFun x - φ x * u.toFun x) 2 μ) atTop (𝓝 0) := by
    apply tendsto_eLpNorm_two_of_tendsto_ae_of_dominated
      (fun n => (v n).memL2.aestronglyMeasurable) hmem (u.memL2.norm.const_mul C)
    · intro n
      filter_upwards [hφn_bound n] with x hx
      change ‖φn n x * u.toFun x‖ ≤ C * ‖u.toFun x‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    · filter_upwards [hφn_lim] with x hx
      exact hx.mul_const _
  have hDlim (i : Fin d) : Tendsto (fun n => eLpNorm
      (fun x => (v n).grad x i - (φ x * u.grad x i + u.toFun x * Dφ x i)) 2 μ)
      atTop (𝓝 0) := by
    apply tendsto_eLpNorm_two_of_tendsto_ae_of_dominated
      (fun n => ((v n).gradMemL2 i).aestronglyMeasurable) (hDmem i)
      (((u.gradMemL2 i).norm.const_mul C).add (u.memL2.norm.const_mul B))
    · intro n
      filter_upwards [hφn_bound n, hDφn_bound n i] with x hx hy
      rw [hDv]
      calc
        ‖φn n x * u.grad x i + u.toFun x * (fderiv ℝ (φn n) x) (basisVec i)‖ ≤
            ‖φn n x * u.grad x i‖ + ‖u.toFun x * (fderiv ℝ (φn n) x) (basisVec i)‖ := norm_add_le _ _
        _ ≤ C * ‖u.grad x i‖ + B * ‖u.toFun x‖ := by
          rw [norm_mul, norm_mul, mul_comm ‖u.toFun x‖]
          exact add_le_add (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
            (mul_le_mul_of_nonneg_right hy (norm_nonneg _))
    · filter_upwards [hφn_lim, hDφn_lim i] with x hx hy
      exact (hx.mul_const _).add (hy.const_mul _)
  exact ⟨fun x => φ x * u.toFun x,
    fun x i => φ x * u.grad x i + u.toFun x * Dφ x i, hmem, hDmem,
    HasWeakGradientOn.of_tendsto_eLpNorm_two hmem hDmem
      (fun n => (v n).memL2) (fun n => (v n).gradMemL2)
      (fun n => (v n).hasWeakGradient) hlim hDlim⟩

end GMCExplicitDelta.Haar
