module

public import GMCExplicitDelta.Proofs.FineSensitivity.Ratio
public import GMCExplicitDelta.Coarse.Scaling

/-! # Scalar normalization of the coefficient in the weighted sensitivity estimate -/

@[expose] public section

open MeasureTheory Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab

namespace GMCExplicitDelta.Assembly

variable {d : ℕ}

/-- Positive scalar multiplication preserves the certified scalar coefficient data. -/
noncomputable def fineScaledScalarData {U : Ch02.Domain d} {a : Homogenization.Vec d → ℝ}
    (h : ScalarCoeffOnData U a) {c : ℝ} (hc : 0 < c) :
    ScalarCoeffOnData U (fun x => c * a x) where
  lam := c * h.lam
  Lam := c * h.Lam
  lam_pos := mul_pos hc h.lam_pos
  lam_le_Lam := mul_le_mul_of_nonneg_left h.lam_le_Lam hc.le
  aeBounds := h.aeBounds.mono fun _ hx =>
    ⟨mul_le_mul_of_nonneg_left hx.1 hc.le, mul_le_mul_of_nonneg_left hx.2 hc.le⟩
  aeStronglyMeasurable := by
    intro i j
    convert (h.aeStronglyMeasurable i j).const_mul c using 1
    funext x
    by_cases hx : x ∈ (U : Set (Homogenization.Vec d))
    all_goals simp [Homogenization.restrictCoeffField, scalarCoeffField,
      Homogenization.scalarMatrix, hx, smul_eq_mul, mul_assoc]

/-- The coefficient data for the normalized old or new coefficient `b_m`. -/
noncomputable def fineNormalizedCoeffData (M : SubdiffusiveProcess.Model.GMCModel d)
    (m : ℕ) (ω : SubdiffusiveProcess.Model.PotentialSample d) (U : Ch02.Domain d) :
    ScalarCoeffOnData U (fun x => (ahom M m)⁻¹ * SubdiffusiveProcess.Model.aCutoff M m ω x) :=
  fineScaledScalarData (aCutoffCoeffOnData M m ω U) (inv_pos.mpr (driftSeed_ahom_pos M m))

/-- Frozen probes agree with response probes for the explicitly normalized coefficient. -/
theorem frozenJ_eq_response_normalized (M : SubdiffusiveProcess.Model.GMCModel d)
    (m : ℕ) (ω : SubdiffusiveProcess.Model.PotentialSample d) (U : Ch02.Domain d)
    (p q : Homogenization.Vec d) :
    frozenJ M m U p q ω = Ch02.responseJ U (fineNormalizedCoeffData M m ω U).toCoeffOn p q := by
  symm
  apply Coarse.responseJ_scale (driftSeed_ahom_pos M m)
  filter_upwards [] with x
  change Homogenization.scalarMatrix (SubdiffusiveProcess.Model.aCutoff M m ω x) =
    ahom M m • Homogenization.scalarMatrix
      ((ahom M m)⁻¹ * SubdiffusiveProcess.Model.aCutoff M m ω x)
  simp [Homogenization.scalarMatrix, smul_smul, (driftSeed_ahom_pos M m).ne']

/-- The new normalized coefficient is the old one multiplied by `cutoffRatio`. -/
theorem fineNormalizedCoeff_ratio (M : SubdiffusiveProcess.Model.GMCModel d)
    (k L : ℕ) (ω : SubdiffusiveProcess.Model.PotentialSample d) (x : Homogenization.Vec d) :
    (ahom M L)⁻¹ * SubdiffusiveProcess.Model.aCutoff M L ω x =
      ((ahom M k)⁻¹ * SubdiffusiveProcess.Model.aCutoff M k ω x) * cutoffRatio M k L ω x := by
  unfold cutoffRatio
  field_simp [(driftSeed_ahom_pos M L).ne', (driftSeed_ahom_pos M k).ne',
    (SubdiffusiveProcess.Model.aCutoff_pos M k ω x).ne']

end GMCExplicitDelta.Assembly
