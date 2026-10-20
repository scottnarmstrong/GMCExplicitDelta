module

public import GMCExplicitDelta.Proofs.FineSensitivity.ConditionalRemainder
public import GMCExplicitDelta.Proofs.FineSensitivity.Gap
public import GMCExplicitDelta.Proofs.FineSensitivity.OuterMoment
public import GMCExplicitDelta.Proofs.FineSensitivity.Constants

/-! # G3: weighted fine-scale sensitivity -/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open MeasureTheory SubdiffusiveProcess.Model
open scoped ENNReal

namespace GMCExplicitDelta.Assembly

open Contract

variable {d : ℕ}

theorem fineSensitivity_proof (hd : d ∈ ({2, 3, 4} : Finset ℕ))
    (M : SubdiffusiveProcess.Model.GMCModel d) {k L : ℕ} (hkL : k < L) (z : Homogenization.Vec d)
    {η Fr Gr : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hFr : 0 ≤ Fr) (hGr : 0 ≤ Gr)
    (hF : ∀ x : Homogenization.Vec d,
      paperENNRealLpNorm M.P.toMeasure 32
          (fun ω => ENNReal.ofReal ((cutoffRatio M k L ω x - 1) ^ 2)) ≤ ENNReal.ofReal Fr)
    (hG : ∀ x : Homogenization.Vec d,
      paperENNRealLpNorm M.P.toMeasure 32
          (fun ω => ENNReal.ofReal (cutoffRatio M k L ω x + (cutoffRatio M k L ω x)⁻¹ - 2)) ≤
        ENNReal.ofReal Gr) :
    paperENNRealLpNorm M.P.toMeasure 32 (normalizedDefect M L (cubeAt z k)) ≤
      (1 + ENNReal.ofReal η) *
          paperENNRealLpNorm M.P.toMeasure 32 (normalizedDefect M k (cubeAt z k)) +
        ENNReal.ofReal (sphereFactor d) *
          (1 + paperENNRealLpNorm M.P.toMeasure 32 (normalizedDefect M k (cubeAt z k))) *
          ENNReal.ofReal (Fr / (2 * η) + Gr) := by
  -- The frozen upper bound on η is retained; positivity suffices for this proof.
  have hd0 : d ≠ 0 := by fin_cases hd <;> norm_num
  let : NeZero d := ⟨hd0⟩
  let U := cubeAt z k
  let W := Fr/(2*η)+Gr
  have hW : 0 ≤ W := add_nonneg (div_nonneg hFr (by positivity)) hGr
  have hB : Measurable (normalizedDefect M k U) := by
    have heq : normalizedDefect M k U = fun ω => ENNReal.ofReal (fineTop M k U ω) :=
      funext (normalizedDefect_eq_ofReal_fineTop M k U)
    rw [heq]
    exact (measurable_fineTop M k U).ennreal_ofReal
  have hgap := (measurable_fineGap M k L U η).ennreal_ofReal
  have hinner (old : PotentialSample d) :
      (∫⁻ fresh, ENNReal.ofReal (fineGap M k L U η (fineSpliceSample k (old,fresh))) ^ (32 : ℝ)
        ∂M.P.toMeasure) ≤
      (ENNReal.ofReal (sphereFactor d) * ENNReal.ofReal W) ^ (32 : ℝ) *
        (1+normalizedDefect M k U old) ^ (32 : ℝ) := by
    let h := fineNormalizedCoeffData M k old U
    have ha : Measurable (fun x => (ahom M k)⁻¹ * aCutoff M k old x) :=
      (continuous_const.mul (continuous_aCutoff M k old)).measurable
    have ha0 (x : Homogenization.Vec d) : 0 ≤ (ahom M k)⁻¹ * aCutoff M k old x :=
      mul_nonneg (inv_nonneg.mpr (driftSeed_ahom_pos M k).le) (aCutoff_pos M k old x).le
    have hb := fine_remainder_conditional_moment h ha ha0 M hkL.le hη hFr hGr
      (fineTop_nonneg M k U old)
      (fun e he => by
        rw [← frozenJ_eq_response_normalized M k old U]
        exact frozenJ_le_fineTop M k U old he) hF hG
    have hc := fine_conditional_constant_eq hd (fineTop_nonneg M k U old) hW
    rw [normalizedDefect_eq_ofReal_fineTop]
    refine (lintegral_mono fun fresh => ENNReal.rpow_le_rpow
      (ENNReal.ofReal_le_ofReal (fineGap_splice_le M hkL.le U hη old fresh))
      (by norm_num : (0 : ℝ) ≤ 32)).trans (hb.trans_eq ?_)
    exact hc
  have hgapnorm := fine_spliced_norm_le M k hgap hB
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hinner
  have hpoint (ω : PotentialSample d) : normalizedDefect M L U ω ≤
      ENNReal.ofReal (1+η) * normalizedDefect M k U ω +
        ENNReal.ofReal (fineGap M k L U η ω) := by
    rw [normalizedDefect_eq_ofReal_fineTop, normalizedDefect_eq_ofReal_fineTop,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1+η),
      ← ENNReal.ofReal_add (mul_nonneg (by positivity) (fineTop_nonneg _ _ _ _))
        (fineGap_nonneg _ _ _ _ _ _)]
    exact ENNReal.ofReal_le_ofReal (fineTop_le_scaled_add_gap M k L U η ω)
  have hb := (HistoryLane.lnorm_mono (μ := M.P.toMeasure) (by norm_num : (0 : ℝ) ≤ 32) hpoint).trans
    (HistoryLane.lnorm_add_le (by norm_num : (1 : ℝ) ≤ 32)
      (measurable_const.mul hB).aemeasurable hgap.aemeasurable)
  rw [HistoryLane.lnorm_const_mul (by norm_num : (0 : ℝ) < 32) ENNReal.ofReal_ne_top] at hb
  have hb := hb.trans (add_le_add le_rfl hgapnorm)
  rw [ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1) hη.le, ENNReal.ofReal_one] at hb
  change paperENNRealLpNorm M.P.toMeasure 32 (normalizedDefect M L U) ≤ _
  dsimp only [W, U] at hb ⊢
  convert hb using 1
  ac_rfl

end GMCExplicitDelta.Assembly
