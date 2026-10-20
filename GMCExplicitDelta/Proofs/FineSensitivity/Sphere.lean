module

public import GMCExplicitDelta.Proofs.NativeCaps.Loewner
public import GMCExplicitDelta.Proofs.NativeCaps.MatrixLocal
public import GMCExplicitDelta.Insertion.SphereRandom
public import GMCExplicitDelta.Proofs.FineSensitivity.Holder

/-! # C13 for the fixed-old-sample remainder -/

@[expose] public section

open MeasureTheory Matrix GMCExplicitDelta.Insertion
open scoped ENNReal NNReal

open scoped Matrix.Norms.Elementwise

namespace GMCExplicitDelta.Assembly

noncomputable local instance fineSphereContinuousENorm {n : ℕ} : ContinuousENorm (Matrix (Fin n) (Fin n) ℝ) :=
  SeminormedAddGroup.toContinuousENorm

/-- Finite probe moments imply integrability of the matrix operator moment. -/
theorem fine_integrable_opNorm_pow {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {d : ℕ}
    {N : Ω → Matrix (Fin d) (Fin d) ℝ} (hH : ∀ ω, (N ω).IsHermitian)
    (hm : ∀ e : EuclideanSpace ℝ (Fin d), MemLp (fun ω => sphereQuadratic (N ω) e) 32 μ) :
    Integrable (fun ω => ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (N ω)‖ ^ (32 : ℕ)) μ := by
  have hq (e : Homogenization.Vec d) : MemLp (fun ω => Coarse.qf (N ω) e) 32 μ := by
    simpa only [← Averaging.matrixProbe_apply, matrixProbe_toLp] using hm (WithLp.toLp 2 e)
  have hentry (i j : Fin d) : MemLp (fun ω => N ω i j) 32 μ := by
    have h := (((hq (Pi.single i 1 + Pi.single j 1)).sub
      (hq (Pi.single i 1))).sub (hq (Pi.single j 1))).const_mul ((2 : ℝ)⁻¹)
    exact h.ae_eq (Filter.Eventually.of_forall fun ω => by
      change 2⁻¹ * ((Coarse.qf (N ω) (Pi.single i 1 + Pi.single j 1) -
        Coarse.qf (N ω) (Pi.single i 1)) - Coarse.qf (N ω) (Pi.single j 1)) = N ω i j
      rw [matrix_entry_polarization (hH ω) i j]
      ring)
  have hN : MemLp N 32 μ := memLp_pi_iff.mpr fun i => memLp_pi_iff.mpr fun j => hentry i j
  let t := (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)).toAlgEquiv.toLinearEquiv.toLinearMap.toContinuousLinearMap
  exact (t.comp_memLp' hN).integrable_norm_pow (by norm_num : (32 : ℕ) ≠ 0)

/-- The fixed-old-sample PSD remainder obeys C13's sharp moment factor. -/
theorem fine_psd_sphere_moment_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {d : ℕ} [NeZero d]
    {N : Ω → Matrix (Fin d) (Fin d) ℝ} (hN : Measurable N)
    (hP : ∀ ω, (N ω).PosSemidef)
    (hm : ∀ e : EuclideanSpace ℝ (Fin d), MemLp (fun ω => sphereQuadratic (N ω) e) 32 μ)
    {T : ℝ} (hT : ∀ e : EuclideanSpace ℝ (Fin d), ‖e‖ = 1 →
      ∫ ω, sphereQuadratic (N ω) e ^ (32 : ℕ) ∂μ ≤ T ^ 32) :
    ∫ ω, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (N ω)‖ ^ (32 : ℕ) ∂μ ≤
      sphereMomentRatio d 32 * T ^ 32 := by
  have hi := fine_integrable_opNorm_pow (fun ω => (hP ω).1) hm
  have hs := integral_sphereTop_pow_le_of_ne_zero hN
    (Filter.Eventually.of_forall hP) hi (by norm_num : 1 ≤ 32)
  have hratio : 0 ≤ sphereMomentRatio d 32 := by
    unfold sphereMomentRatio
    apply Finset.prod_nonneg
    intro j _
    positivity
  have hdir : sphereDirectionalMoment μ N 32 ≤ T ^ 32 := by
    apply csSup_le
    · obtain ⟨e, he⟩ := (NormedSpace.sphere_nonempty (E := EuclideanSpace ℝ (Fin d))).mpr
        (by norm_num : (0 : ℝ) ≤ 1)
      exact ⟨_, ⟨e, he, rfl⟩⟩
    · rintro _ ⟨e, he, rfl⟩
      exact hT e (by simpa only [Metric.mem_sphere, dist_zero_right] using he)
  have heq : (fun ω => sphereTop (N ω) ^ (32 : ℕ)) =
      (fun ω => ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (N ω)‖ ^ (32 : ℕ)) := by
    funext ω
    rw [sphereTop_eq_opNorm_of_posSemidef (hP ω)]
  rw [heq] at hs
  exact hs.trans (mul_le_mul_of_nonneg_left hdir hratio)

/-- The frozen row constants are the exact C13 moment factors in all three dimensions. -/
theorem fine_sphereMomentRatio_eq {d : ℕ} (hd : d ∈ ({2, 3, 4} : Finset ℕ)) :
    sphereMomentRatio d 32 = (Contract.sphereFactorPow d : ℝ) := by
  fin_cases hd
  · rw [sphereMomentRatio_two_32]
    norm_num [Contract.sphereFactorPow]
  · rw [sphereMomentRatio_three_32]
    norm_num [Contract.sphereFactorPow]
  · rw [sphereMomentRatio_four_32]
    norm_num [Contract.sphereFactorPow]

end GMCExplicitDelta.Assembly
