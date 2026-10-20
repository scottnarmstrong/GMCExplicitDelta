module

public import GMCExplicitDelta.Averaging.MatrixAverageFinite

/-! # Quadratic probes of finite centered averages -/

@[expose] public section

open MeasureTheory Matrix
open GMCExplicitDelta.Insertion
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace GMCExplicitDelta.Averaging

variable {Ω κ ι : Type*} [MeasurableSpace Ω] [Fintype κ] [Fintype ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {d : ℕ}
  {M : κ → ι → Ω → Matrix (Fin d) (Fin d) ℝ}

theorem sphereQuadratic_finiteMatrixAverage (hm : ∀ c i, MemLp (M c i) 32 μ)
    (ω : Ω) (u : EuclideanSpace ℝ (Fin d)) :
    sphereQuadratic (finiteMatrixAverage μ M ω) u =
      ((Fintype.card κ * Fintype.card ι : ℕ) : ℝ)⁻¹ *
        ∑ c, ∑ i, (sphereQuadratic (M c i ω) u - ∫ ω', sphereQuadratic (M c i ω') u ∂μ) := by
  change matrixProbe u (((Fintype.card κ * Fintype.card ι : ℕ) : ℝ)⁻¹ •
    ∑ c, ∑ i, (M c i ω - ∫ ω', M c i ω' ∂μ)) = _
  rw [map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sub, ← (matrixProbe u).integral_comp_comm ((hm c i).integrable (by norm_num))]
  rfl

/-- A bound on all directional means suffices; an isotropic mean identity is unnecessary. -/
theorem finiteMatrixAverage_probe_upper [Nonempty κ] [Nonempty ι]
    (hm : ∀ c i, MemLp (M c i) 32 μ) {F : ℝ}
    (hmean : ∀ c i u, ‖u‖ = 1 → ∫ ω, sphereQuadratic (M c i ω) u ∂μ ≤ F)
    {A : Matrix (Fin d) (Fin d) ℝ} (ω : Ω) (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1)
    (hsub : sphereQuadratic A u ≤
      ((Fintype.card κ * Fintype.card ι : ℕ) : ℝ)⁻¹ * ∑ c, ∑ i, sphereQuadratic (M c i ω) u) :
    sphereQuadratic A u ≤ F + sphereQuadratic (finiteMatrixAverage μ M ω) u := by
  have hn : (0 : ℝ) < ((Fintype.card κ * Fintype.card ι : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Fintype.card_pos (α := κ)) (Fintype.card_pos (α := ι))
  have hsum : (∑ c, ∑ i, ∫ ω, sphereQuadratic (M c i ω) u ∂μ) ≤
      ((Fintype.card κ * Fintype.card ι : ℕ) : ℝ) * F := by
    calc _ ≤ ∑ _c : κ, ∑ _i : ι, F :=
      Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun i _ => hmean c i u hu
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_mul]; ring
  have hscaled := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hn.le)
  rw [← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul] at hscaled
  rw [sphereQuadratic_finiteMatrixAverage hm]
  simp only [Finset.sum_sub_distrib]
  linarith only [hsub, hscaled]

end GMCExplicitDelta.Averaging
