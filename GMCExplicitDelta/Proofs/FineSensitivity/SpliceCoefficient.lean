module

public import GMCExplicitDelta.Proofs.FineSensitivity.Splice
public import GMCExplicitDelta.Proofs.FineSensitivity.Scaled

/-! # The normalized coefficients on the independent splice -/

@[expose] public section

open MeasureTheory Homogenization Homogenization.Book.Ch02 SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab

namespace GMCExplicitDelta.Assembly

variable {d : ℕ}

theorem fine_aCutoff_splice_prefix (M : GMCModel d) (k : ℕ)
    (old fresh : PotentialSample d) (x : Homogenization.Vec d) :
    aCutoff M k (fineSpliceSample k (old, fresh)) x = aCutoff M k old x := by
  unfold aCutoff
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ k := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
  simp only [fineSpliceSample, ite_eq_left hik]

theorem fineBand_splice (k L : ℕ) (old fresh : PotentialSample d) (x : Homogenization.Vec d) :
    fineBand k L (fineSpliceSample k (old, fresh)) x = fineBand k L fresh x := by
  apply Finset.sum_congr rfl
  intro i hi
  have hik : ¬i ≤ k := by have := (Finset.mem_Ioc.mp hi).1; omega
  simp only [fineSpliceSample, ite_eq_right hik]

theorem cutoffRatio_splice (M : GMCModel d) {k L : ℕ} (hkL : k ≤ L)
    (old fresh : PotentialSample d) (x : Homogenization.Vec d) :
    cutoffRatio M k L (fineSpliceSample k (old, fresh)) x = cutoffRatio M k L fresh x := by
  rw [cutoffRatio_eq_exp M hkL, cutoffRatio_eq_exp M hkL, fineBand_splice]

theorem fine_normalized_splice_coefficient (M : GMCModel d) {k L : ℕ} (hkL : k ≤ L)
    (old fresh : PotentialSample d) (x : Homogenization.Vec d) :
    (ahom M L)⁻¹ * aCutoff M L (fineSpliceSample k (old, fresh)) x =
      ((ahom M k)⁻¹ * aCutoff M k old x) * cutoffRatio M k L fresh x := by
  rw [fineNormalizedCoeff_ratio M k L, fine_aCutoff_splice_prefix, cutoffRatio_splice M hkL]

theorem frozenJ_splice_prefix (M : GMCModel d) (k : ℕ) (U : Domain d)
    (old fresh : PotentialSample d) (p q : Homogenization.Vec d) :
    frozenJ M k U p q (fineSpliceSample k (old, fresh)) = frozenJ M k U p q old := by
  unfold frozenJ J
  apply responseJ_eq_ofAEEq
  filter_upwards [] with x
  change scalarCoeffField (aCutoff M k (fineSpliceSample k (old, fresh))) x =
    scalarCoeffField (aCutoff M k old) x
  rw [scalarCoeffField, scalarCoeffField, fine_aCutoff_splice_prefix]

theorem normalizedDefect_splice_prefix (M : GMCModel d) (k : ℕ) (U : Domain d)
    (old fresh : PotentialSample d) :
    normalizedDefect M k U (fineSpliceSample k (old, fresh)) = normalizedDefect M k U old := by
  unfold normalizedDefect paperScalarProbeMaxOn
  apply iSup_congr
  intro e
  exact congrArg ENNReal.ofReal (frozenJ_splice_prefix M k U old fresh e.val e.val)

end GMCExplicitDelta.Assembly
