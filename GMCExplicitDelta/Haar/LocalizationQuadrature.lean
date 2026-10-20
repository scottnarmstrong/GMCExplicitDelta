module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! A sharp C¹ trapezoidal error bound for concave profiles (H13). -/
@[expose] public section

namespace GMCExplicitDelta.Haar

open Real Set intervalIntegral
open MeasureTheory (volume)

/-- The sharp error bound uses only a continuous antitone first derivative,
so it applies across the non-C² interfaces of a plateau-cosine profile. -/
theorem trapezoid_error_le_derivative_drop {f f' : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hdf : ∀ x, HasDerivAt f (f' x) x) (hcont : Continuous f')
    (hanti : AntitoneOn f' (Icc a b)) :
    (∫ x in a..b, f x) - (b - a) * (f a + f b) / 2 ≤
      (b - a) ^ 2 / 8 * (f' a - f' b) := by
  let m : ℝ := (a + b) / 2
  have ham : a ≤ m := by dsimp [m]; linarith only [hab]
  have hmb : m ≤ b := by dsimp [m]; linarith only [hab]
  have hf : Continuous f := continuous_iff_continuousAt.2 (fun x => (hdf x).continuousAt)
  have hkernel : Continuous (fun x : ℝ => m - x) := continuous_const.sub continuous_id
  have hparts := integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun x : ℝ => m - x) (u' := fun _ => (-1 : ℝ)) (v := f) (v' := f')
    (a := a) (b := b) hkernel.continuousOn hf.continuousOn
    (fun x _ => (hasDerivAt_id x).const_sub m) (fun x _ => hdf x)
    (continuous_const.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
  rw [integral_const_mul] at hparts
  have hleft := integral_mono_on (μ := volume) (f := fun x => (m - x) * f' x)
    (g := fun x => (m - x) * f' a) ham
    ((hkernel.mul hcont).intervalIntegrable _ _) ((hkernel.mul_const (f' a)).intervalIntegrable _ _)
    (fun x hx => mul_le_mul_of_nonneg_left
      (hanti ⟨le_rfl, hab⟩ ⟨hx.1, le_trans hx.2 hmb⟩ hx.1)
      (sub_nonneg.mpr hx.2))
  have hright := integral_mono_on (μ := volume) (f := fun x => (m - x) * f' x)
    (g := fun x => (m - x) * f' b) hmb
    ((hkernel.mul hcont).intervalIntegrable _ _) ((hkernel.mul_const (f' b)).intervalIntegrable _ _)
    (fun x hx => mul_le_mul_of_nonpos_left
      (hanti ⟨le_trans ham hx.1, hx.2⟩ ⟨hab, le_rfl⟩ hx.2)
      (sub_nonpos.mpr hx.1))
  have hk (l r : ℝ) : (∫ x in l..r, m - x) = m * (r - l) - (r ^ 2 - l ^ 2) / 2 := by
    rw [integral_sub (f := fun _ : ℝ => m) (g := fun x : ℝ => x) (continuous_const.intervalIntegrable _ _) (continuous_id.intervalIntegrable _ _),
      integral_const, integral_id]
    simp only [smul_eq_mul]
    ring
  rw [integral_mul_const, hk] at hleft hright
  have hadd := integral_add_adjacent_intervals (f := fun x => (m - x) * f' x)
    ((hkernel.mul hcont).intervalIntegrable (μ := volume) (a := a) (b := m))
    ((hkernel.mul hcont).intervalIntegrable (μ := volume) (a := m) (b := b))
  dsimp [m] at hparts hleft hright hadd
  nlinarith only [hparts, hleft, hright, hadd]

end GMCExplicitDelta.Haar
