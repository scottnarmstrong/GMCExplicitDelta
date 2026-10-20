module

public import GMCExplicitDelta.Proofs.Observables.Mean
public import GMCExplicitDelta.Proofs.Observables.Measurable
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.LargeCubePartitionResponse
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepFiniteReadoutComparison

/-! Translation transport for the observables on arbitrary translated cubes. -/
@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
open scoped ENNReal

namespace GMCExplicitDelta.Assembly

variable {d : ℕ}

theorem cutoffJ_cubeAt_translate (M : SubdiffusiveProcess.Model.GMCModel d) (m n : ℕ)
    (z p q : Homogenization.Vec d) (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    J (cubeAt z n) (aCutoffCoeffOnData M m ω (cubeAt z n)).toCoeffOn p q =
      J (Ch02.cubeDomain (originCube d (n : ℤ)))
        (aCutoffCoeffOnData M m (translatePotentialSequence z ω)
          (Ch02.cubeDomain (originCube d (n : ℤ)))).toCoeffOn p q := by
  simp only [J]
  rw [Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ,
    Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ]
  change ResponseJ (translateSet z (openCubeSet (originCube d (n : ℤ)))) p q _ = _
  rw [ResponseJ_translateSet_eq_translateCoeffField]
  apply congrArg (ResponseJ (openCubeSet (originCube d (n : ℤ))) p q)
  funext x
  change scalarMatrix (SubdiffusiveProcess.Model.aCutoff M m ω (x + z)) =
    scalarMatrix (SubdiffusiveProcess.Model.aCutoff M m (translatePotentialSequence z ω) x)
  exact congrArg scalarMatrix (aCutoff_translatePotentialSequence M m z ω x).symm

theorem normalizedDefect_cubeAt_translate (M : SubdiffusiveProcess.Model.GMCModel d) (m n : ℕ)
    (z : Homogenization.Vec d) (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    normalizedDefect M m (cubeAt z n) ω =
      normalizedDefect M m (Ch02.cubeDomain (originCube d (n : ℤ)))
        (translatePotentialSequence z ω) := by
  unfold normalizedDefect paperScalarProbeMaxOn
  exact iSup_congr (fun _ => congrArg ENNReal.ofReal (cutoffJ_cubeAt_translate M m n z _ _ ω))

theorem frozenJ_lintegral_eq_fMean (M : SubdiffusiveProcess.Model.GMCModel d) (m n : ℕ)
    (z e : Homogenization.Vec d) (he : vecNormSq e = 1) :
    (∫⁻ ω, ENNReal.ofReal (frozenJ M m (cubeAt z n) e e ω) ∂M.P.toMeasure) =
      ENNReal.ofReal (fMean M m n) := by
  have hd : d ≠ 0 := by have := M.shellPrefix.dimension; omega
  let : NeZero d := ⟨hd⟩
  let p := (Real.sqrt (ahom M m))⁻¹ • e
  let q := Real.sqrt (ahom M m) • e
  have htrans : (fun ω => ENNReal.ofReal (frozenJ M m (cubeAt z n) e e ω)) =
      fun ω => ENNReal.ofReal (J (Ch02.cubeDomain (originCube d (n : ℤ)))
        (aCutoffCoeffOnData M m (translatePotentialSequence z ω)
          (Ch02.cubeDomain (originCube d (n : ℤ)))).toCoeffOn p q) := by
    funext ω
    exact congrArg ENNReal.ofReal (cutoffJ_cubeAt_translate M m n z p q ω)
  rw [htrans, ← lintegral_map (measurable_cutoff_responseJ M m _ p q).ennreal_ofReal
    (measurable_translatePotentialSequence z), potentialSequenceLaw_stationary M z]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_cutoffResponseJ M m _ p q)
    (Filter.Eventually.of_forall (fun ω => Ch02.responseJ_nonneg _ _ _ _))]
  change ENNReal.ofReal (expectedJ M m n p q) = _
  rw [expectedJ_eq_scalar_readouts M m n e he, fMean, alphaMean_eq_readout, betaMean_eq_readout]
  congr 1
  ring

theorem normalizedDefect_cubeAt_moment_eq_origin (M : SubdiffusiveProcess.Model.GMCModel d)
    (m n : ℕ) (z : Homogenization.Vec d) :
    paperENNRealLpNorm M.P.toMeasure 32 (normalizedDefect M m (cubeAt z n)) =
      paperENNRealLpNorm M.P.toMeasure 32
        (normalizedDefect M m (Ch02.cubeDomain (originCube d (n : ℤ)))) := by
  have heq : normalizedDefect M m (cubeAt z n) = fun ω =>
      normalizedDefect M m (Ch02.cubeDomain (originCube d (n : ℤ))) (translatePotentialSequence z ω) :=
    funext (normalizedDefect_cubeAt_translate M m n z)
  rw [heq]
  exact paperENNRealLpNorm_comp_translatePotentialSample_eq M z _
    ((measurable_cascadeObservables_proof M m _).1 (ahom M m))

end GMCExplicitDelta.Assembly
