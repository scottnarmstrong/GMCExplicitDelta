module

public import GMCExplicitDelta.Steps.CascadeOfObligations
public import GMCExplicitDelta.Steps.RowObligations
public import GMCExplicitDelta.Contract.Rows

/-!
# Proof of `ExplicitCascadeFour`

Proof of the theorem stated in `GMCExplicitDelta/Statements/ExplicitCascadeFour.lean`.

Proof: the analytic half `cascade_of_obligations` (step R5) applied to the certified row
`rowFour` and its numeric obligations `rowFour_obligations` (§18), with the row's threshold
and constants rewritten to the literals of the main theorem (`rowFour_deltaStar`, `rowFour_C32`, `rowFour_Cmean`) and
the conclusion unfolded by `cascadeConclusion_four_iff`.
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta.StatementProofs

/-- Proof of `GMCExplicitDelta.explicit_cascade_four` (step T0): the binders of the statement, with the data
implicit and the two hypotheses as `by assumption` auto-parameters, so that the statement is proved by `exact`. -/
theorem explicit_cascade_four {M : SubdiffusiveProcess.Model.GMCModel 4} {m n : ℕ}
    {z : Homogenization.Vec 4} (hδ : M.delta ≤ 15698 / 100000 := by assumption)
    (hmn : m ≤ n := by assumption) :
    Measurable (normalizedDefect M m
        (SubdiffusiveProcess.LambdaStability.translatedDomain z (originCube 4 (n : ℤ)))) ∧
    paperENNRealLpNorm M.P.toMeasure 32
        (normalizedDefect M m
          (SubdiffusiveProcess.LambdaStability.translatedDomain z (originCube 4 (n : ℤ)))) ≤
      ENNReal.ofReal (5918767600 / 61606801 * M.delta ^ 2) ∧
    ∀ e : Homogenization.Vec 4, vecNormSq e = 1 →
      Measurable (fun ω => J (SubdiffusiveProcess.LambdaStability.translatedDomain z (originCube 4 (n : ℤ)))
          (aCutoffCoeffOnData M m ω
            (SubdiffusiveProcess.LambdaStability.translatedDomain z (originCube 4 (n : ℤ)))).toCoeffOn
          ((Real.sqrt (ahom M m))⁻¹ • e) (Real.sqrt (ahom M m) • e)) ∧
      ∫⁻ ω, ENNReal.ofReal
          (J (SubdiffusiveProcess.LambdaStability.translatedDomain z (originCube 4 (n : ℤ)))
            (aCutoffCoeffOnData M m ω
              (SubdiffusiveProcess.LambdaStability.translatedDomain z
                (originCube 4 (n : ℤ)))).toCoeffOn
            ((Real.sqrt (ahom M m))⁻¹ • e) (Real.sqrt (ahom M m) • e)) ∂M.P.toMeasure ≤
        ENNReal.ofReal (423596800 / 61606801 * M.delta ^ 2) := by
  have h := Contract.cascade_of_obligations Contract.rowFour (by decide)
      Contract.rowFour_obligations M (by rw [Contract.rowFour_deltaStar]; exact hδ)
  rw [Contract.rowFour_C32, Contract.rowFour_Cmean] at h
  exact (Contract.cascadeConclusion_four_iff M).1 h m n hmn z

end GMCExplicitDelta.StatementProofs
