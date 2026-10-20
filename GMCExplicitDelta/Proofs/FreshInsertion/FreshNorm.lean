module

public import GMCExplicitDelta.Insertion.FreshSplicedResponse
public import GMCExplicitDelta.Insertion.FreshScaledMatrix
public import GMCExplicitDelta.Insertion.FreshSphereExtended
public import GMCExplicitDelta.Insertion.FreshSphereConstant

/-! # I6: fresh insertion returns the exact contracted norm -/

@[expose] public section

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

namespace GMCExplicitDelta.Assembly

open Contract Insertion

variable {d : ℕ}

/-- **I6**, with the literal hypotheses and conclusion of the insertion target. -/
theorem freshNorm_return_proof (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (M : SubdiffusiveProcess.Model.GMCModel d) {D F : ℝ} (L : ℕ)
    (hpos : 0 < row.Fnext F) (hle : row.Fnext F ≤ row.Dnext D F)
    (hf : fMean M L (L + row.h) ≤ row.Fnext F)
    (hnorm : ∀ z : Homogenization.Vec d,
      paperENNRealLpNorm M.P.toMeasure 32 (normalizedDefect M L (cubeAt z (L + row.h))) ≤
        ENNReal.ofReal (row.Dnext D F)) :
    ∀ z : Homogenization.Vec d,
      paperENNRealLpNorm M.P.toMeasure 32
          (scaledDefect M (L + row.h) (cubeAt z (L + row.h)) (freshNorm M L (L + row.h))) ≤
        ENNReal.ofReal (row.sym M.delta D F) := by
  clear hO
  let : NeZero d := ⟨by have := M.shellPrefix.dimension; omega⟩
  intro z
  have hs := freshNorm_pos M L (L + row.h)
  let N := scaledMatrix M (L + row.h) (cubeAt z (L + row.h)) (freshNorm M L (L + row.h))
  have hN : Measurable N := measurable_scaledMatrix M _ _ hs
  have hPSD : ∀ ω, (N ω).PosSemidef := scaledMatrix_posSemidef M _ _ hs
  have hdir (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) :
      (∫⁻ ω, ENNReal.ofReal (sphereQuadratic (N ω) u ^ (32 : ℕ)) ∂M.P.toMeasure) ≤
        ENNReal.ofReal (row.freshMoment M.delta D F) := by
    have he : vecNormSq (WithLp.ofLp u) = 1 := by rw [vecNormSq_ofLp, hu, one_pow]
    have hh := fresh_directional_moment_le row M L z (WithLp.ofLp u) he hpos hle hf (hnorm z)
    refine le_trans (le_of_eq (lintegral_congr fun ω => ?_)) hh
    rw [sphereQuadratic_eq_qf]
    change ENNReal.ofReal (Coarse.qf (scaledMatrix M _ _ _ ω) (WithLp.ofLp u) ^ (32 : ℕ)) = _
    rw [← scaled_response_eq_qf M _ _ hs, ENNReal.ofReal_pow (Ch02.responseJ_nonneg _ _ _ _)]
  have hC := lintegral_sphereTop_pow_le_of_directional hN hPSD (by norm_num : 1 ≤ (32 : ℕ)) hdir
  rw [sphereMomentRatio_eq_sphereFactorPow hd] at hC
  have hprof (r : Fin 33) : 0 ≤ row.profile D F r := by
    unfold Row.profile
    split
    · exact zero_le_one
    · exact mul_nonneg (Real.rpow_nonneg hpos.le _)
        (Real.rpow_nonneg (hpos.le.trans hle) _)
  have hM : 0 ≤ row.freshMoment M.delta D F :=
    Finset.sum_nonneg fun r _ => mul_nonneg (bandRow_nonneg _ _ _) (hprof r)
  have hS : 0 ≤ (sphereFactorPow d : ℝ) := by
    rw [← sphereMomentRatio_eq_sphereFactorPow hd]
    unfold sphereMomentRatio
    exact Finset.prod_nonneg fun i _ => div_nonneg (by positivity) (by positivity)
  apply paperENNRealLpNorm_le_of_moment M.P.toMeasure _ (mul_nonneg hS hM)
  refine (lintegral_mono fun ω => pow_le_pow_left' (scaledDefect_le_sphereTop M _ _ hs ω) 32).trans ?_
  rw [ENNReal.ofReal_mul hS]
  refine le_trans (le_of_eq (lintegral_congr fun ω => ?_)) hC
  exact (ENNReal.ofReal_pow (sphereTop_nonneg (hPSD ω)) 32).symm

end GMCExplicitDelta.Assembly
