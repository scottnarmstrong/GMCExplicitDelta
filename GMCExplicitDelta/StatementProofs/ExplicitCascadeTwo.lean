module

public import GMCExplicitDelta.Steps.CascadeOfObligations
public import GMCExplicitDelta.Steps.RowObligations
public import GMCExplicitDelta.Contract.Rows

/-!
# Proof of `ExplicitCascadeTwo`

Proof of the theorem stated in `GMCExplicitDelta/Statements/ExplicitCascadeTwo.lean`.

Proof: the analytic half `cascade_of_obligations` (step R5) applied to the certified row
`rowTwo` and its numeric obligations `rowTwo_obligations` (§18), with the row's threshold
and constants rewritten to the literals of the main theorem (`rowTwo_deltaStar`, `rowTwo_C32`, `rowTwo_Cmean`) and
the conclusion unfolded by `cascadeConclusion_two_iff`.
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta.StatementProofs

/-- Proof of `GMCExplicitDelta.explicit_cascade_two` (step T0): the binders of the statement, with the data
implicit and the two hypotheses as `by assumption` auto-parameters, so that the statement is proved by `exact`. -/
theorem explicit_cascade_two {M : SubdiffusiveProcess.Model.GMCModel 2} {m n : ℕ}
    {z : Homogenization.Vec 2} (hδ : M.delta ≤ 36665 / 100000 := by assumption)
    (hmn : m ≤ n := by assumption) :
    Measurable (normalizedDefect M m
        (SubdiffusiveProcess.LambdaStability.translatedDomain z (originCube 2 (n : ℤ)))) ∧
    paperENNRealLpNorm M.P.toMeasure 32
        (normalizedDefect M m
          (SubdiffusiveProcess.LambdaStability.translatedDomain z (originCube 2 (n : ℤ)))) ≤
      ENNReal.ofReal (23138371504 / 53772889 * M.delta ^ 2) ∧
    ∀ e : Homogenization.Vec 2, vecNormSq e = 1 →
      Measurable (fun ω => J (SubdiffusiveProcess.LambdaStability.translatedDomain z (originCube 2 (n : ℤ)))
          (aCutoffCoeffOnData M m ω
            (SubdiffusiveProcess.LambdaStability.translatedDomain z (originCube 2 (n : ℤ)))).toCoeffOn
          ((Real.sqrt (ahom M m))⁻¹ • e) (Real.sqrt (ahom M m) • e)) ∧
      ∫⁻ ω, ENNReal.ofReal
          (J (SubdiffusiveProcess.LambdaStability.translatedDomain z (originCube 2 (n : ℤ)))
            (aCutoffCoeffOnData M m ω
              (SubdiffusiveProcess.LambdaStability.translatedDomain z
                (originCube 2 (n : ℤ)))).toCoeffOn
            ((Real.sqrt (ahom M m))⁻¹ • e) (Real.sqrt (ahom M m) • e)) ∂M.P.toMeasure ≤
        ENNReal.ofReal (230590996 / 53772889 * M.delta ^ 2) := by
  have h := Contract.cascade_of_obligations Contract.rowTwo (by decide)
      Contract.rowTwo_obligations M (by rw [Contract.rowTwo_deltaStar]; exact hδ)
  rw [Contract.rowTwo_C32, Contract.rowTwo_Cmean] at h
  exact (Contract.cascadeConclusion_two_iff M).1 h m n hmn z

end GMCExplicitDelta.StatementProofs
