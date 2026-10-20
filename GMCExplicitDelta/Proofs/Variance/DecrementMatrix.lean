module

public import GMCExplicitDelta.Proofs.Variance.Cells
public import GMCExplicitDelta.Proofs.Variance.Cauchy

/-! # Positive frozen subadditivity decrements and their trace bound -/

@[expose] public section

open MeasureTheory Matrix Homogenization Homogenization.Book SubdiffusiveProcess.CoarseGrainingVocab

namespace GMCExplicitDelta.Assembly

variable {d : ℕ}

theorem frozenVar_posSemidef_sub_of_loewner {A B : Homogenization.Mat d}
    (hA : Aᵀ = A) (hB : Bᵀ = B) (h : MatLoewnerLE A B) : (B - A).PosSemidef := by
  have ha : A.IsHermitian := by simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hA
  have hb : B.IsHermitian := by simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hB
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hb.sub ha)
  intro x
  have hx := Coarse.matLoewnerLE_iff_qf.mp h x
  simpa only [Coarse.qf, star_trivial, Matrix.sub_mulVec, dotProduct_sub, sub_nonneg] using hx

theorem frozenVar_decrement_trace_bound {D M : Homogenization.Mat d}
    (hD : D.PosSemidef) (hupper : ((2 : ℝ) • M - D).PosSemidef) :
    frobSq D ≤ 2 * frozenVar_matrixPair D M := by
  have h := frozenVar_trace_mul_nonneg hD hupper
  have hs : Dᵀ = D := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hD.isHermitian.eq
  rw [frozenVar_frobSq_eq_trace, frozenVar_matrixPair_eq_trace, hs]
  simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul] at h
  linarith only [h]

theorem frozenVar_frozen_decrements_pos (M : SubdiffusiveProcess.Model.GMCModel d) (L n k : ℕ)
    (hkn : k ≤ n) (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    (cellAvg n k (fun U => frozenX M L U ω) - frozenX M L (cubeAt 0 n) ω).PosSemidef ∧
    (cellAvg n k (fun U => frozenY M L U ω) - frozenY M L (cubeAt 0 n) ω).PosSemidef := by
  have h := frozenVar_frozen_subadditive M L n k hkn ω
  exact ⟨frozenVar_posSemidef_sub_of_loewner
    (Coarse.posDef_symm (frozenVar_frozen_posDef M L (cubeAt 0 n) ω).1)
    (frozenVar_cellAvg_symm n k _ fun U => Coarse.posDef_symm (frozenVar_frozen_posDef M L U ω).1) h.1,
    frozenVar_posSemidef_sub_of_loewner
    (Coarse.posDef_symm (frozenVar_frozen_posDef M L (cubeAt 0 n) ω).2)
    (frozenVar_cellAvg_symm n k _ fun U => Coarse.posDef_symm (frozenVar_frozen_posDef M L U ω).2) h.2⟩

/-- Each decrement is bounded by twice the average defect. -/
theorem frozenVar_frozen_decrements_upper (M : SubdiffusiveProcess.Model.GMCModel d) (L n k : ℕ)
    (hkn : k ≤ n) (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    ((2 : ℝ) • cellAvg n k (fun U => frozenDefect M L U ω) -
      (cellAvg n k (fun U => frozenX M L U ω) - frozenX M L (cubeAt 0 n) ω)).PosSemidef ∧
    ((2 : ℝ) • cellAvg n k (fun U => frozenDefect M L U ω) -
      (cellAvg n k (fun U => frozenY M L U ω) - frozenY M L (cubeAt 0 n) ω)).PosSemidef := by
  have h := frozenVar_frozen_decrements_pos M L n k hkn ω
  have hm := (frozenVar_frozenDefect_posSemidef M L (cubeAt 0 n) ω).smul (by norm_num : (0 : ℝ) ≤ 2)
  constructor
  · convert h.2.add hm using 1
    rw [frozenVar_cellAvg_defect M L n k hkn ω]
    unfold frozenDefect
    module
  · convert h.1.add hm using 1
    rw [frozenVar_cellAvg_defect M L n k hkn ω]
    unfold frozenDefect
    module

end GMCExplicitDelta.Assembly
