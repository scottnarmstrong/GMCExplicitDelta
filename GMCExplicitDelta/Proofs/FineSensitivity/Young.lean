module

public import GMCExplicitDelta.Coarse.CompetitorsMain

/-! # The pointwise Young inequality for the G3 competitor remainder -/

@[expose] public section

namespace GMCExplicitDelta.Assembly

/-- Young with the exact constants required by the weighted sensitivity estimate. -/
theorem fine_young_cross {η : ℝ} (hη : 0 < η) (x y : ℝ) :
    x * y / 2 ≤ η / 2 * x ^ 2 + y ^ 2 / (8 * η) := by
  apply (mul_le_mul_iff_right₀ (show 0 < 8 * η by positivity)).mp
  field_simp
  nlinarith only [sq_nonneg (2 * η * x - y)]

/-- Scalar density form of C12 followed by Young. The two remainder weights are
`(ρ-1)²` and `ρ+ρ⁻¹-2`, exactly the weights controlled by G4. -/
theorem fine_competitor_density_le {η ρ : ℝ} (hη : 0 < η)
    (v u : ℝ) :
    (ρ * v ^ 2 + ρ⁻¹ * u ^ 2) / 2 ≤
      (v ^ 2 + u ^ 2) / 2 + η / 2 * (v + u) ^ 2 +
        (ρ - 1) ^ 2 / (8 * η) * (v - u) ^ 2 +
        (ρ + ρ⁻¹ - 2) / 2 * u ^ 2 := by
  have hy := fine_young_cross hη (v + u) ((ρ - 1) * (v - u))
  have he : ((ρ - 1) * (v - u)) ^ 2 / (8 * η) =
      (ρ - 1) ^ 2 / (8 * η) * (v - u) ^ 2 := by ring
  rw [he] at hy
  nlinarith only [hy]

/-- The pointwise competitor estimate for vector gradients, before spatial integration. -/
theorem fine_competitor_vector_density_le {d : ℕ} {η : ℝ} (hη : 0 < η)
    (ρ : ℝ) (v u : Homogenization.Vec d) :
    (ρ * Homogenization.vecNormSq v + ρ⁻¹ * Homogenization.vecNormSq u) / 2 ≤
      (Homogenization.vecNormSq v + Homogenization.vecNormSq u) / 2 +
        η / 2 * Homogenization.vecNormSq (v + u) +
        (ρ - 1) ^ 2 / (8 * η) * Homogenization.vecNormSq (v - u) +
        (ρ + ρ⁻¹ - 2) / 2 * Homogenization.vecNormSq u := by
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => fine_competitor_density_le hη (ρ := ρ) (v i) (u i))
  simpa only [Homogenization.vecNormSq, Homogenization.vecDot, Pi.add_apply,
    Pi.sub_apply, dotProduct, ← pow_two, Finset.sum_add_distrib,
    div_eq_mul_inv, add_mul, Finset.sum_mul, Finset.mul_sum] using hsum

/-- The nonnegative ratio weight in the second G3 remainder. -/
theorem fine_ratio_weight_eq {ρ : ℝ} (hρ : 0 < ρ) :
    ρ + ρ⁻¹ - 2 = ρ⁻¹ * (ρ - 1) ^ 2 := by
  field_simp [hρ.ne']
  ring

end GMCExplicitDelta.Assembly
