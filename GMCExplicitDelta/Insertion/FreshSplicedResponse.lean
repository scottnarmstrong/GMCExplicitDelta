module

public import GMCExplicitDelta.Insertion.FreshSpliceCoefficient
public import GMCExplicitDelta.Insertion.FreshResponseTransfer
public import GMCExplicitDelta.Insertion.FreshOldProfile

/-! # Conditional and annealed directional bounds for the fresh insertion -/

@[expose] public section

open MeasureTheory Homogenization Homogenization.Book SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab (aCutoffCoeffOnData ScalarCoeffOnData ahom
  measurable_cutoff_responseJ paperENNRealLpNorm normalizedDefect)
open scoped ENNReal

namespace GMCExplicitDelta.Insertion

/-- The conditional coefficient representation agrees with the actual scaled probe. -/
theorem spliced_response_eq {d : ℕ} (M : GMCModel d) {L m : ℕ} (hLm : L ≤ m)
    (old fresh : PotentialSample d) (U : Ch02.Domain d) (e : Homogenization.Vec d) :
    Ch02.responseJ U (splicedFreshCoeffData M hLm old fresh U).toCoeffOn e e =
      Ch02.responseJ U (aCutoffCoeffOnData M m (spliceSample L (old, fresh)) U).toCoeffOn
        ((Real.sqrt (Assembly.freshNorm M L m))⁻¹ • e)
        (Real.sqrt (Assembly.freshNorm M L m) • e) := by
  apply Coarse.responseJ_scale (Assembly.freshNorm_pos M L m)
  filter_upwards [] with x
  change scalarMatrix (aCutoff M m (spliceSample L (old, fresh)) x) =
    Assembly.freshNorm M L m • scalarMatrix
      (((ahom M L)⁻¹ * aCutoff M L old x) * Real.exp (∑ k ∈ Finset.Ioc L m, fresh k x))
  rw [← splice_unshifted_coefficient M hLm old fresh x]
  simp [scalarMatrix, smul_smul, (Assembly.freshNorm_pos M L m).ne']

/-- I3 on the actual independent splice, with no conditional moment premise. -/
theorem spliced_response_moment_le {d : ℕ} (M : GMCModel d) {L m : ℕ} (hLm : L ≤ m)
    (old : PotentialSample d) (U : Ch02.Domain d) (e : Homogenization.Vec d)
    (he : vecNormSq e = 1) :
    (∫⁻ fresh, ENNReal.ofReal (Ch02.responseJ U
      (aCutoffCoeffOnData M m (spliceSample L (old, fresh)) U).toCoeffOn
      ((Real.sqrt (Assembly.freshNorm M L m))⁻¹ • e)
      (Real.sqrt (Assembly.freshNorm M L m) • e)) ^ (32 : ℕ) ∂M.P.toMeasure) ≤
      ENNReal.ofReal (Contract.bandSeriesEval M.delta (m - L) (Assembly.frozenJ M L U e e old)) := by
  have h := responseJ_exp_moment_le_band M (Finset.Ioc L m)
    (Assembly.fineNormalizedCoeffData M L old U)
    (fun fresh => splicedFreshCoeffData M hLm old fresh U) he
  simpa only [spliced_response_eq, Nat.card_Ioc, ← Assembly.frozenJ_eq_response_normalized] using h

/-- Averaging the conditional estimate uses precisely the I5 old profile. -/
theorem fresh_directional_moment_le {d : ℕ} (row : Contract.Row d) (M : GMCModel d)
    {D F : ℝ} (L : ℕ) (z e : Homogenization.Vec d) (he : vecNormSq e = 1)
    (hpos : 0 < row.Fnext F) (hle : row.Fnext F ≤ row.Dnext D F)
    (hf : Assembly.fMean M L (L + row.h) ≤ row.Fnext F)
    (hnorm : paperENNRealLpNorm M.P.toMeasure 32
      (normalizedDefect M L (Assembly.cubeAt z (L + row.h))) ≤ ENNReal.ofReal (row.Dnext D F)) :
    (∫⁻ ω, ENNReal.ofReal (Ch02.responseJ (Assembly.cubeAt z (L + row.h))
      (aCutoffCoeffOnData M (L + row.h) ω (Assembly.cubeAt z (L + row.h))).toCoeffOn
      ((Real.sqrt (Assembly.freshNorm M L (L + row.h)))⁻¹ • e)
      (Real.sqrt (Assembly.freshNorm M L (L + row.h)) • e)) ^ (32 : ℕ) ∂M.P.toMeasure) ≤
      ENNReal.ofReal (row.freshMoment M.delta D F) := by
  let : NeZero d := ⟨by have := M.shellPrefix.dimension; omega⟩
  rw [lintegral_eq_spliced_iterated M L
    (((measurable_cutoff_responseJ M (L + row.h) (Assembly.cubeAt z (L + row.h)) _ _).ennreal_ofReal).pow_const 32)]
  refine (lintegral_mono fun old => ?_).trans
    (Assembly.lintegral_bandSeriesEval_frozenJ_le_freshMoment row M L (L + row.h) z e he
      hpos hle hf hnorm)
  simpa only [Nat.add_sub_cancel_left] using
    spliced_response_moment_le M (Nat.le_add_right L row.h) old (Assembly.cubeAt z (L + row.h)) e he

end GMCExplicitDelta.Insertion
