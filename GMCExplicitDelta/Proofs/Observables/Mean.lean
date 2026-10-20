module

public import GMCExplicitDelta.Assembly.ModelFrozen
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.DualAnnealedMonotone
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepFiniteReadoutComparison

/-! C9 from the primal and dual annealed scalar readouts. -/
@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge

open scoped Matrix.Norms.Elementwise

namespace GMCExplicitDelta.Assembly

variable {d : ℕ}

theorem integral_trace_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {A : Ω → Homogenization.Mat d} (hA : Integrable A μ) :
    (∫ ω, Matrix.trace (A ω) ∂μ) = Matrix.trace (∫ ω, A ω ∂μ) := by
  unfold Matrix.trace
  rw [integral_finsetSum Finset.univ]
  · exact Finset.sum_congr rfl (fun i _ => (integral_matrix_apply hA i i).symm)
  · intro i _
    exact (hA.eval i).eval i

theorem cubeAt_zero (n : ℕ) : cubeAt (0 : Homogenization.Vec d) n = Ch02.cubeDomain (originCube d (n : ℤ)) := by
  simp only [cubeAt, SubdiffusiveProcess.LambdaStability.translatedDomain,
      Ch02.cubeDomain, translateSet_zero]

theorem alphaMean_eq_readout (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) :
    alphaMean M L n = (ahom M L)⁻¹ * abarScalarReadout M L n := by
  have heq : (fun ω => Matrix.trace (frozenX M L (cubeAt 0 n) ω)) =
      fun ω => (ahom M L)⁻¹ * Matrix.trace (randomAMatrix M L (cubeAt 0 n) ω) := by
    funext ω
    exact Matrix.trace_smul _ _
  rw [alphaMean, heq, integral_const_mul, integral_trace_eq (integrable_randomAMatrix M L _)]
  change _ = (ahom M L)⁻¹ * (Matrix.trace (abar M L _) / (d : ℝ))
  rw [cubeAt_zero]
  unfold abar
  ring

theorem betaMean_eq_readout (M : SubdiffusiveProcess.Model.GMCModel d) [NeZero d] (L n : ℕ) :
    betaMean M L n = ahom M L * oneStepAnnealedDualReadout M L n := by
  have heq : (fun ω => Matrix.trace (frozenY M L (cubeAt 0 n) ω)) =
      fun ω => ahom M L * Matrix.trace ((randomAStarMatrix M L (cubeAt 0 n) ω)⁻¹) := by
    funext ω
    exact Matrix.trace_smul _ _
  rw [betaMean, heq, integral_const_mul, integral_trace_eq (integrable_randomAStarMatrix_inv M L _)]
  rw [cubeAt_zero]
  change _ * (_ * Matrix.trace (abarStarInv M L _)) = _
  rw [abarStarInv_originCube_eq_oneStepAnnealedDualReadout_smul_one,
    Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin]
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  simp only [smul_eq_mul]
  field_simp

theorem fMean_nonneg_antitone_proof (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) :
    (∀ n, 0 ≤ fMean M L n) ∧ ∀ a b, a ≤ b → fMean M L b ≤ fMean M L a := by
  have hd : d ≠ 0 := by have := M.shellPrefix.dimension; omega
  let : NeZero d := ⟨hd⟩
  have ha : 0 < ahom M L := (Real.exp_pos _).trans_le
    (SubdiffusiveProcess.Section5.homogenized_coefficient_reciprocal_lower M L)
  have halower (n : ℕ) : ahom M L ≤ abarScalarReadout M L n := by
    rw [ahom_eq_iInf_abarScalarReadout]
    exact ciInf_le ⟨0, by rintro x ⟨k, rfl⟩; exact abarScalarReadout_nonneg M L k⟩ n
  constructor
  · intro n
    have h1 := mul_le_mul_of_nonneg_left (halower n) (inv_nonneg.mpr ha.le)
    have h2 := mul_le_mul_of_nonneg_left (ahom_inv_le_oneStepAnnealedDualReadout M L n) ha.le
    rw [inv_mul_cancel₀ ha.ne'] at h1
    rw [mul_inv_cancel₀ ha.ne'] at h2
    rw [fMean, alphaMean_eq_readout, betaMean_eq_readout]
    linarith only [h1, h2]
  · intro a b hab
    have h1 := mul_le_mul_of_nonneg_left (antitone_abarScalarReadout M L hab) (inv_nonneg.mpr ha.le)
    have h2 := mul_le_mul_of_nonneg_left (antitone_oneStepAnnealedDualReadout M L hab) ha.le
    rw [fMean, fMean, alphaMean_eq_readout, alphaMean_eq_readout, betaMean_eq_readout, betaMean_eq_readout]
    linarith only [h1, h2]

end GMCExplicitDelta.Assembly
