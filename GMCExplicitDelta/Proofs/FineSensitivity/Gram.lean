module

public import GMCExplicitDelta.Proofs.FineSensitivity.MeasGradient
public import GMCExplicitDelta.Averaging.MatrixAverage
public import GMCExplicitDelta.Proofs.NativeCaps.Loewner

/-! # Positive Gram matrices of the fixed old gradients -/

@[expose] public section

open Homogenization Homogenization.Book.Ch02 MeasureTheory Matrix

open scoped Matrix.Norms.Elementwise

namespace GMCExplicitDelta.Assembly

noncomputable local instance fineGramContinuousENorm {n : ℕ} : ContinuousENorm (Matrix (Fin n) (Fin n) ℝ) :=
  SeminormedAddGroup.toContinuousENorm

variable {d : ℕ} {U : Domain d}

/-- Pointwise linear map whose columns are the chosen old gradient representatives. -/
noncomputable def fineGradientAt (a : CoeffOn U) (dual : Bool) (x : Vec d) : Vec d →ₗ[ℝ] Vec d where
  toFun e := fineMeasGradient a dual e x
  map_add' e f := congrFun (map_add (fineMeasGradient a dual) e f) x
  map_smul' c e := congrFun (map_smul (fineMeasGradient a dual) c e) x

/-- Matrix of the pointwise old-gradient map. -/
noncomputable def fineGradientMatrix (a : CoeffOn U) (dual : Bool) (x : Vec d) : Mat d :=
  LinearMap.toMatrix' (fineGradientAt a dual x)

theorem fineGradientMatrix_mulVec (a : CoeffOn U) (dual : Bool) (x e : Vec d) :
    fineGradientMatrix a dual x *ᵥ e = fineMeasGradient a dual e x :=
  LinearMap.toMatrix'_mulVec _ _

theorem measurable_fineGradientMatrix (a : CoeffOn U) (dual : Bool) :
    Measurable (fineGradientMatrix a dual) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  change Measurable (fun x => fineMeasGradient a dual (Pi.single j 1) x i)
  exact (measurable_pi_apply i).comp (measurable_fineMeasGradient a dual (Pi.single j 1))

/-- Weighted square of a gradient matrix, integrated over space. -/
noncomputable def fineWeightedGram {E : Type*} [MeasurableSpace E]
    (ν : Measure E) (w : E → ℝ) (G : E → Mat d) : Mat d :=
  ∫ x, w x • ((G x)ᵀ * G x) ∂ν

theorem fine_gram_qf (G : Mat d) (w : ℝ) (e : Vec d) :
    Coarse.qf (w • (Gᵀ * G)) e = w * vecNormSq (G *ᵥ e) := by
  unfold Coarse.qf vecNormSq vecDot
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  rfl

/-- The Gram integral has its intended quadratic probes. -/
theorem fineWeightedGram_qf {E : Type*} [MeasurableSpace E]
    (ν : Measure E) (w : E → ℝ) (G : E → Mat d)
    (hI : Integrable (fun x => w x • ((G x)ᵀ * G x)) ν) (e : Vec d) :
    Coarse.qf (fineWeightedGram ν w G) e =
      ∫ x, w x * vecNormSq (G x *ᵥ e) ∂ν := by
  let q := (Averaging.matrixProbe (WithLp.toLp 2 e)).toLinearMap.toContinuousLinearMap
  have h := (q.integral_comp_comm hI).symm
  change (GMCExplicitDelta.Averaging.matrixProbe (WithLp.toLp 2 e))
      (∫ x, w x • ((G x)ᵀ * G x) ∂ν) = _ at h
  change (Averaging.matrixProbe (WithLp.toLp 2 e))
      (∫ x, w x • ((G x)ᵀ * G x) ∂ν) =
        ∫ x, Averaging.matrixProbe (WithLp.toLp 2 e) (w x • ((G x)ᵀ * G x)) ∂ν at h
  simp only [matrixProbe_toLp] at h
  simpa only [fineWeightedGram, fine_gram_qf] using h

/-- Nonnegative weights make the Gram integral positive semidefinite. -/
theorem fineWeightedGram_posSemidef {E : Type*} [MeasurableSpace E]
    (ν : Measure E) (w : E → ℝ) (G : E → Mat d)
    (hI : Integrable (fun x => w x • ((G x)ᵀ * G x)) ν)
    (hw : ∀ x, 0 ≤ w x) : (fineWeightedGram ν w G).PosSemidef := by
  have hP (x : E) : (w x • ((G x)ᵀ * G x)).PosSemidef := by
    have hG : ((G x)ᵀ * G x).PosSemidef := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        Matrix.posSemidef_conjTranspose_mul_self (G x)
    exact hG.smul (hw x)
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · let t := (Matrix.transposeLinearEquiv (Fin d) (Fin d) ℝ ℝ).toLinearMap.toContinuousLinearMap
    change t (∫ x, w x • ((G x)ᵀ * G x) ∂ν) = ∫ x, w x • ((G x)ᵀ * G x) ∂ν
    calc
      t (∫ x, w x • ((G x)ᵀ * G x) ∂ν) =
          ∫ x, t (w x • ((G x)ᵀ * G x)) ∂ν := (t.integral_comp_comm hI).symm
      _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun x =>
      Matrix.isHermitian_iff_isSymm.mp (hP x).1)
  · intro e
    change 0 ≤ Coarse.qf (fineWeightedGram ν w G) e
    rw [fineWeightedGram_qf ν w G hI e]
    exact integral_nonneg fun x => mul_nonneg (hw x) (vecNormSq_nonneg _)

end GMCExplicitDelta.Assembly
