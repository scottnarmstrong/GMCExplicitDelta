module

public import GMCExplicitDelta.Proofs.HaarMode.Tensor
public import Homogenization.Sobolev.Truncation.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.Deriv.Support

/-! # Bounded products and trigonometric composition in H¹ -/

@[expose] public section

open MeasureTheory Homogenization Set Filter
open scoped ENNReal

namespace GMCExplicitDelta.Localization

variable {d : ℕ} {U : Set (Homogenization.Vec d)}

/-- Weak gradients depend only on the almost-everywhere representatives. -/
theorem haarMode_weak_congr {u v : Homogenization.Vec d → ℝ}
    {Du Dv : Homogenization.Vec d → Homogenization.Vec d}
    (hu : HasWeakGradientOn U u Du) (hf : u =ᵐ[volume.restrict U] v)
    (hg : Du =ᵐ[volume.restrict U] Dv) : HasWeakGradientOn U v Dv := by
  intro i φ hφ hc hs
  calc
    _ = ∫ x in U, u x * (fderiv ℝ φ x) (basisVec i) :=
      integral_congr_ae (hf.symm.mono fun x hx => by rw [hx])
    _ = -∫ x in U, Du x i * φ x := hu i φ hφ hc hs
    _ = _ := congrArg Neg.neg (integral_congr_ae (hg.mono fun x hx => congrArg (fun z : Homogenization.Vec d => z i * φ x) hx))

/-- A compactly supported smooth function agrees with the square on a prescribed bounded interval. -/
theorem haarMode_smooth_square {C : ℝ} (hC : 0 ≤ C) :
    ∃ G : ℝ → ℝ, ContDiff ℝ 1 G ∧
      (∃ M : ℝ, 0 ≤ M ∧ ∀ t, |deriv G t| ≤ M) ∧
      ∀ t, |t| ≤ C → G t = t ^ 2 ∧ deriv G t = 2 * t := by
  let b : ContDiffBump (0 : ℝ) := ⟨C + 1, 2 * (C + 1), by linarith, by linarith⟩
  let G : ℝ → ℝ := fun t => b t * t ^ 2
  have hG : ContDiff ℝ 1 G := b.contDiff.mul (contDiff_id.pow 2)
  have hcomp : HasCompactSupport G := b.hasCompactSupport.mul_right
  obtain ⟨M, hM⟩ := hG.continuous_deriv_one.bounded_above_of_compact_support hcomp.deriv
  refine ⟨G, hG, ⟨max M 0, le_max_right _ _, fun t => (hM t).trans (le_max_left _ _)⟩, ?_⟩
  intro t ht
  have hb : b =ᶠ[nhds t] 1 := b.eventuallyEq_one_of_mem_ball (by
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, b] using
      lt_of_le_of_lt ht (by linarith : C < C + 1))
  have heq : G =ᶠ[nhds t] fun y => y ^ 2 := hb.mono fun y hy => by dsimp [G]; simp only [hy, Pi.one_apply, one_mul]
  refine ⟨heq.eq_of_nhds, ?_⟩
  rw [heq.deriv_eq]
  simp

/-- Squaring a bounded H¹ function preserves H¹, with the expected weak gradient. -/
theorem haarMode_h1_square (hU : IsOpenBoundedConvexDomain U) (u : H1Function U)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ x ∂volume.restrict U, |u x| ≤ C) :
    ∃ w : H1Function U, w.toFun = (fun x => u x ^ 2) ∧
      w.grad = (fun x i => 2 * u x * u.grad x i) := by
  let : IsFiniteMeasure (volumeMeasureOn U) := hU.isBoundedDomain.isFiniteMeasure_restrict_volume
  obtain ⟨G, hG, ⟨M, hM, hder⟩, heq⟩ := haarMode_smooth_square hC
  have huTop : MemLp u.toFun ⊤ (volume.restrict U) :=
    memLp_top_of_bound u.memL2.aestronglyMeasurable C (by simpa only [Real.norm_eq_abs] using hb)
  have hw := hasWeakGradientOn_comp_of_deriv_bounded hU u hG hM hder
  have hf : (fun x => G (u x)) =ᵐ[volume.restrict U] (fun x => u x ^ 2) :=
    hb.mono fun x hx => (heq _ hx).1
  have hg : (fun x i => deriv G (u x) * u.grad x i) =ᵐ[volume.restrict U]
      (fun x i => 2 * u x * u.grad x i) := hb.mono fun x hx => by
    funext i
    exact congrArg (fun r : ℝ => r * u.grad x i) (heq _ hx).2
  refine ⟨{ toFun := fun x => u x ^ 2
            grad := fun x i => 2 * u x * u.grad x i
            memL2 := ?_
            gradMemL2 := ?_
            hasWeakGradient := haarMode_weak_congr hw hf hg }, rfl, rfl⟩
  · simpa only [pow_two] using huTop.fun_mul (r := 2) u.memL2
  · intro i
    exact (huTop.const_mul 2).fun_mul (r := 2) (u.gradMemL2 i)

/-- The bounded H¹ product rule, constructed by polarization of squares. -/
theorem haarMode_h1_mul (hU : IsOpenBoundedConvexDomain U) (u v : H1Function U)
    {C : ℝ} (hC : 0 ≤ C) (hu : ∀ᵐ x ∂volume.restrict U, |u x| ≤ C)
    (hv : ∀ᵐ x ∂volume.restrict U, |v x| ≤ C) :
    ∃ w : H1Function U, w.toFun = (fun x => u x * v x) ∧
      w.grad = (fun x i => u x * v.grad x i + v x * u.grad x i) := by
  have hplus : ∀ᵐ x ∂volume.restrict U, |(u + v) x| ≤ 2 * C := by
    filter_upwards [hu, hv] with x hx hy
    exact (abs_add_le (u x) (v x)).trans (by linarith)
  have hminus : ∀ᵐ x ∂volume.restrict U, |(u - v) x| ≤ 2 * C := by
    filter_upwards [hu, hv] with x hx hy
    simp only [H1Function.sub_toFun]
    have hab : |u x - v x| ≤ |u x| + |v x| := by
      simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (u x) 0 (v x)
    exact hab.trans (by linarith)
  obtain ⟨wp, hpf, hpg⟩ := haarMode_h1_square hU (u + v) (by positivity : 0 ≤ 2 * C) hplus
  obtain ⟨wm, hmf, hmg⟩ := haarMode_h1_square hU (u - v) (by positivity : 0 ≤ 2 * C) hminus
  refine ⟨(1 / 4 : ℝ) • (wp - wm), ?_, ?_⟩
  · funext x
    simp only [H1Function.smul_toFun, H1Function.sub_toFun, hpf, hmf, H1Function.add_toFun,
      H1Function.sub_toFun]
    ring
  · funext x i
    simp only [H1Function.smul_grad, H1Function.sub_grad, hpg, hmg,
      H1Function.add_toFun, H1Function.sub_toFun, H1Function.add_grad,
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- A bounded C¹ composition with bounded derivative preserves H¹. -/
theorem haarMode_h1_comp (hU : IsOpenBoundedConvexDomain U) (u : H1Function U)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) {B M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ t, |G t| ≤ B) (hd : ∀ t, |deriv G t| ≤ M) :
    ∃ w : H1Function U, w.toFun = (fun x => G (u x)) ∧
      w.grad = (fun x i => deriv G (u x) * u.grad x i) := by
  let : IsFiniteMeasure (volumeMeasureOn U) := hU.isBoundedDomain.isFiniteMeasure_restrict_volume
  have hderTop : MemLp (fun x => deriv G (u x)) ⊤ (volume.restrict U) :=
    memLp_top_of_bound (hG.continuous_deriv_one.comp_aestronglyMeasurable u.memL2.aestronglyMeasurable)
      M (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hd (u x))
  refine ⟨{ toFun := fun x => G (u x)
            grad := fun x i => deriv G (u x) * u.grad x i
            memL2 := ?_
            gradMemL2 := fun i => hderTop.fun_mul (r := 2) (u.gradMemL2 i)
            hasWeakGradient := hasWeakGradientOn_comp_of_deriv_bounded hU u hG hM hd }, rfl, rfl⟩
  exact MemLp.of_bound (hG.continuous.comp_aestronglyMeasurable u.memL2.aestronglyMeasurable) B
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb (u x))

/-- Sine composition, with its weak gradient written explicitly. -/
theorem haarMode_h1_sin (hU : IsOpenBoundedConvexDomain U) (u : H1Function U) :
    ∃ w : H1Function U, w.toFun = (fun x => Real.sin (u x)) ∧
      w.grad = (fun x i => Real.cos (u x) * u.grad x i) := by
  simpa only [Real.deriv_sin] using haarMode_h1_comp hU u Real.contDiff_sin (by norm_num : (0 : ℝ) ≤ 1)
    Real.abs_sin_le_one (fun t => by simpa only [Real.deriv_sin] using Real.abs_cos_le_one t)

end GMCExplicitDelta.Localization
