module

public import GMCExplicitDelta.Insertion.FreshNormMoments
public import GMCExplicitDelta.Insertion.FreshMomentProfile
public import GMCExplicitDelta.Proofs.Variance.Isotropy
public import GMCExplicitDelta.Proofs.FreshInsertion.BandSeries
public import GMCExplicitDelta.Proofs.Scaling.Band

/-! # The old directional moment profile from the exact model hypotheses -/

@[expose] public section

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab (normalizedDefect paperENNRealLpNorm
  aCutoffCoeffOnData measurable_cutoff_responseJ)
open scoped ENNReal

namespace GMCExplicitDelta.Assembly

open Contract

/-- The old maximum norm controls each literal directional 32nd moment. -/
theorem frozenJ_pow32_of_norm {d : ℕ} (M : GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (e : Homogenization.Vec d) (he : vecNormSq e = 1) {B : ℝ} (hB : 0 ≤ B)
    (hnorm : paperENNRealLpNorm M.P.toMeasure 32 (normalizedDefect M L U) ≤ ENNReal.ofReal B) :
    Integrable (fun ω => frozenJ M L U e e ω ^ (32 : ℕ)) M.P.toMeasure ∧
      (∫ ω, frozenJ M L U e e ω ^ (32 : ℕ) ∂M.P.toMeasure) ≤ B ^ (32 : ℕ) := by
  let : NeZero d := ⟨by have := M.shellPrefix.dimension; omega⟩
  have hm : Measurable (frozenJ M L U e e) := measurable_cutoff_responseJ M L U _ _
  have h0 (ω : PotentialSample d) : 0 ≤ frozenJ M L U e e ω := Ch02.responseJ_nonneg _ _ _ _
  have hd (ω : PotentialSample d) : ENNReal.ofReal (frozenJ M L U e e ω) ≤ normalizedDefect M L U ω :=
    le_iSup_of_le ⟨e, he⟩ le_rfl
  have hM := Insertion.lintegral_pow_le_of_paperNorm M.P.toMeasure _ hB hnorm
  have hdir := (lintegral_mono fun ω => pow_le_pow_left' (hd ω) 32).trans hM
  exact Insertion.integrable_pow_and_integral_le_of_lintegral hm h0 (pow_nonneg hB _) hdir

/-- The I5 mean bound is the frozen mean, by step C8. -/
theorem integral_frozenJ_le_Fnext {d : ℕ} (row : Row d) (M : GMCModel d) (L n : ℕ)
    (z e : Homogenization.Vec d) (he : vecNormSq e = 1) {F : ℝ} (hpos : 0 < row.Fnext F)
    (hf : fMean M L n ≤ row.Fnext F) :
    (∫ ω, frozenJ M L (cubeAt z n) e e ω ∂M.P.toMeasure) ≤ row.Fnext F := by
  have hi : Integrable (frozenJ M L (cubeAt z n) e e) M.P.toMeasure :=
    SubdiffusiveProcess.CoarseGrainingVocab.integrable_cutoffResponseJ M L _ _ _
  have hm := lintegral_frozenJ_eq_fMean_proof M L n z e he
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun ω => Ch02.responseJ_nonneg _ _ _ _)] at hm
  exact (ENNReal.ofReal_le_ofReal_iff hpos.le).mp (hm.le.trans (ENNReal.ofReal_le_ofReal hf))

/-- The old profile controls the exact band polynomial averaged over the old sample. -/
theorem lintegral_bandSeriesEval_frozenJ_le_freshMoment {d : ℕ} (row : Row d) (M : GMCModel d)
    {D F : ℝ} (L n : ℕ) (z e : Homogenization.Vec d) (he : vecNormSq e = 1)
    (hpos : 0 < row.Fnext F) (hle : row.Fnext F ≤ row.Dnext D F)
    (hf : fMean M L n ≤ row.Fnext F)
    (hnorm : paperENNRealLpNorm M.P.toMeasure 32 (normalizedDefect M L (cubeAt z n)) ≤
      ENNReal.ofReal (row.Dnext D F)) :
    (∫⁻ ω, ENNReal.ofReal (bandSeriesEval M.delta row.h (frozenJ M L (cubeAt z n) e e ω))
      ∂M.P.toMeasure) ≤ ENNReal.ofReal (row.freshMoment M.delta D F) := by
  let : NeZero d := ⟨by have := M.shellPrefix.dimension; omega⟩
  let X := frozenJ M L (cubeAt z n) e e
  have hm : Measurable X := measurable_cutoff_responseJ M L (cubeAt z n) _ _
  have h0 (ω : PotentialSample d) : 0 ≤ X ω := Ch02.responseJ_nonneg _ _ _ _
  have hD : 0 ≤ row.Dnext D F := (lt_of_lt_of_le hpos hle).le
  have h32 := frozenJ_pow32_of_norm M L (cubeAt z n) e he hD hnorm
  have hmean := integral_frozenJ_le_Fnext row M L n z e he hpos hf
  have hr (r : Fin 33) : Integrable (fun ω => X ω ^ (r : ℕ)) M.P.toMeasure :=
    Averaging.integrable_pow_of_le (by omega) h0 hm h32.1
  have hi : Integrable (fun ω => bandSeriesEval M.delta row.h (X ω)) M.P.toMeasure := by
    have hs := integrable_finsetSum Finset.univ (fun r _ => (hr r).const_mul (bandRow M.delta row.h r))
    refine hs.congr (Filter.Eventually.of_forall fun ω => ?_)
    exact (bandSeriesEval_eq_sum_proof M.delta row.h (X ω)).symm
  have hnn (ω : PotentialSample d) : 0 ≤ bandSeriesEval M.delta row.h (X ω) := by
    rw [bandSeriesEval_eq_sum_proof]
    exact Finset.sum_nonneg fun r _ => mul_nonneg (bandRow_nonneg _ _ _) (pow_nonneg (h0 ω) _)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hnn)]
  apply ENNReal.ofReal_le_ofReal
  have hb := Insertion.integral_band_polynomial_le_freshMoment row hpos hle h0 hm
    h32.1 hmean h32.2 M.delta (fun r => bandRow_nonneg _ _ r)
  exact (integral_congr_ae (Filter.Eventually.of_forall fun ω =>
    bandSeriesEval_eq_sum_proof M.delta row.h (X ω))).le.trans hb

end GMCExplicitDelta.Assembly
