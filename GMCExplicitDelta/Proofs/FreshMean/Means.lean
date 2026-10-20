module

public import GMCExplicitDelta.Assembly.ModelFrozen
public import GMCExplicitDelta.Proofs.Normalization.Drift
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.AnnealedDualMeanDefect

/-! # Trace forms and lower bounds for the annealed normalized energies -/

@[expose] public section

open MeasureTheory Homogenization Homogenization.Book SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion
open scoped ENNReal Matrix.Norms.Elementwise

namespace GMCExplicitDelta.Assembly

variable {d : ℕ}

/-- The untranslated assembly cube is the standard Chapter 2 cube domain. -/
theorem freshRet_cubeAt_zero (n : ℕ) : cubeAt (0 : Homogenization.Vec d) n =
    Ch02.cubeDomain (originCube d (n : ℤ)) := by
  unfold cubeAt SubdiffusiveProcess.LambdaStability.translatedDomain Ch02.cubeDomain
  congr 1
  exact translateSet_zero _

/-- Trace commutes with the integrable matrix expectation. -/
theorem freshRet_integral_trace {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {A : Ω → Homogenization.Mat d} (hA : Integrable A μ) :
    ∫ ω, Matrix.trace (A ω) ∂μ = Matrix.trace (∫ ω, A ω ∂μ) := by
  simp only [Matrix.trace, Matrix.diag]
  rw [integral_finsetSum Finset.univ (fun i _ => (hA.eval i).eval i)]
  apply Finset.sum_congr rfl
  intro i _
  exact (integral_matrix_apply hA i i).symm

/-- The primal mean is its finite-volume trace readout divided by the homogenized scalar. -/
theorem freshRet_alpha_eq (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) :
    alphaMean M L n = abarScalarReadout M L n / ahom M L := by
  unfold alphaMean frozenX
  simp only [Matrix.trace_smul, smul_eq_mul]
  rw [integral_const_mul, freshRet_cubeAt_zero]
  change (d : ℝ)⁻¹ * ((ahom M L)⁻¹ * ∫ ω,
    Matrix.trace (randomAMatrix M L (Ch02.cubeDomain (originCube d (n : ℤ))) ω) ∂M.P.toMeasure) = _
  rw [freshRet_integral_trace (integrable_randomAMatrix M L _)]
  change (d : ℝ)⁻¹ * ((ahom M L)⁻¹ * Matrix.trace (abar M L _)) = _
  unfold abarScalarReadout
  ring

/-- The dual mean is the inverse-star trace times the homogenized scalar. -/
theorem freshRet_beta_eq (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) :
    betaMean M L n = ahom M L *
      Matrix.trace (abarStarInv M L (Ch02.cubeDomain (originCube d (n : ℤ)))) / d := by
  unfold betaMean frozenY
  simp only [Matrix.trace_smul, smul_eq_mul]
  rw [integral_const_mul, freshRet_cubeAt_zero]
  change (d : ℝ)⁻¹ * (ahom M L * ∫ ω,
    Matrix.trace ((randomAStarMatrix M L (Ch02.cubeDomain (originCube d (n : ℤ))) ω)⁻¹)
      ∂M.P.toMeasure) = _
  rw [freshRet_integral_trace (integrable_randomAStarMatrix_inv M L _)]
  change (d : ℝ)⁻¹ * (ahom M L * Matrix.trace (abarStarInv M L _)) = _
  ring

/-- C9's two lower bounds hold without an induction hypothesis. -/
theorem freshRet_alpha_beta_ge_one (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) :
    1 ≤ alphaMean M L n ∧ 1 ≤ betaMean M L n := by
  have hd : 0 < (d : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension
  have ha := driftSeed_ahom_pos M L
  let : NeZero d := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension)⟩
  constructor
  · rw [freshRet_alpha_eq]
    apply (le_div_iff₀ ha).2
    have hb : BddBelow (Set.range (abarScalarReadout M L)) :=
      ⟨0, by rintro _ ⟨k, rfl⟩; exact abarScalarReadout_nonneg M L k⟩
    exact (by simpa only [one_mul, ahom] using csInf_le hb (Set.mem_range_self n))
  · rw [freshRet_beta_eq]
    apply (le_div_iff₀ hd).2
    have hs : (d : ℝ) * (ahom M L)⁻¹ ≤
        Matrix.trace (abarStarInv M L (Ch02.cubeDomain (originCube d (n : ℤ)))) := by
      calc
        _ = ∑ _i : Fin d, (ahom M L)⁻¹ := by simp
        _ ≤ _ := Finset.sum_le_sum fun i _ => ahom_inv_le_abarStarInv_originCube_entry M L n i
    have hm := mul_le_mul_of_nonneg_left hs ha.le
    have hc : ahom M L * (ahom M L)⁻¹ = 1 := mul_inv_cancel₀ ha.ne'
    nlinarith only [hm, hc]

/-- A Loewner comparison bounds the trace. -/
theorem freshRet_trace_le {A B : Homogenization.Mat d} (h : MatLoewnerLE A B) :
    Matrix.trace A ≤ Matrix.trace B := by
  apply Finset.sum_le_sum
  intro i _
  have hi := h (Pi.single i 1)
  simp only [vecDot_single_left, matVecMul_single] at hi
  change A i i ≤ B i i
  linarith only [hi]

end GMCExplicitDelta.Assembly
