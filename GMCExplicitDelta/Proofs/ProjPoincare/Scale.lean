module

public import GMCExplicitDelta.Proofs.ProjPoincare.OneDim

/-! Scaling the sharp one-dimensional estimate to an arbitrary interval. -/
@[expose] public section

open MeasureTheory

namespace GMCExplicitDelta.Localization.ProjPoincare

theorem thirds_projected_poincare_interval {v g : ℝ → ℝ} (hv : Continuous v) (hg : Continuous g)
    (hd : ∀ t, HasDerivAt v (g t) t) (a S : ℝ) (hS : 0 < S) :
    let m := S⁻¹ * ∫ t in a..(a + S), v t
    ((3 / S * (∫ t in a..(a + S / 3), v t) - m) ^ 2 +
      (3 / S * (∫ t in (a + S / 3)..(a + 2 * S / 3), v t) - m) ^ 2 +
      (3 / S * (∫ t in (a + 2 * S / 3)..(a + S), v t) - m) ^ 2) / 3 ≤
      (5 / 54 : ℝ) * S ^ 2 * (S⁻¹ * ∫ t in a..(a + S), g t ^ 2) := by
  have hvS : Continuous (fun t : ℝ => v (S * t + a)) := hv.comp (by fun_prop)
  have hgS : Continuous (fun t : ℝ => S * g (S * t + a)) := continuous_const.mul (hg.comp (by fun_prop))
  have hdS (t : ℝ) : HasDerivAt (fun t : ℝ => v (S * t + a)) (S * g (S * t + a)) t := by
    have h := (hd (S * t + a)).comp t (((hasDerivAt_id t).const_mul S).add_const a)
    simpa only [Function.comp_def, id_eq, mul_one, mul_comm] using h
  have h := thirds_projected_poincare hvS hgS hdS
  dsimp only at h ⊢
  have hgint : (∫ t in (0 : ℝ)..1, (S * g (S * t + a)) ^ 2) =
      S * ∫ t in a..(a + S), g t ^ 2 := by
    simp_rw [mul_pow, intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_comp_mul_add (fun t => g t ^ 2) hS.ne' a]
    simp only [mul_zero, zero_add, mul_one]
    rw [add_comm S a]
    simp only [smul_eq_mul]
    field_simp [hS.ne']
  rw [hgint] at h
  simp_rw [intervalIntegral.integral_comp_mul_add v hS.ne' a] at h
  have h0 : S * 0 + a = a := by ring
  have h1 : S * (1 / 3) + a = a + S / 3 := by ring
  have h2 : S * (2 / 3) + a = a + 2 * S / 3 := by ring
  have h3 : S * 1 + a = a + S := by ring
  rw [h0, h1, h2, h3] at h
  simp only [smul_eq_mul] at h
  convert h using 1 <;> field_simp [hS.ne']

end GMCExplicitDelta.Localization.ProjPoincare
