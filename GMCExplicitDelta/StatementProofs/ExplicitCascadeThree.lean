module

public import GMCExplicitDelta.Steps.CascadeOfObligations
public import GMCExplicitDelta.Steps.RowObligations
public import GMCExplicitDelta.Contract.Rows

/-!
# Proof of `ExplicitCascadeThree`

Proof of the theorem stated in `GMCExplicitDelta/Statements/ExplicitCascadeThree.lean`.

Proof: the analytic half `cascade_of_obligations` (step R5) applied to the certified row
`rowThree` and its numeric obligations `rowThree_obligations` (§18), with the row's threshold
and constants rewritten to the literals of the main theorem (`rowThree_deltaStar`, `rowThree_C32`, `rowThree_Cmean`) and
the conclusion unfolded by `cascadeConclusion_three_iff`.
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta.StatementProofs

/-- Proof of `GMCExplicitDelta.explicit_cascade_three` (step T0): the binders of the statement, with the data
implicit and the two hypotheses as `by assumption` auto-parameters, so that the statement is proved by `exact`. -/
theorem explicit_cascade_three {M : SubdiffusiveProcess.Model.GMCModel 3} {m n : ℕ}
    {z : Homogenization.Vec 3} (hδ : M.delta ≤ 18870 / 100000 := by assumption)
    (hmn : m ≤ n := by assumption) :
    Measurable (normalizedDefect M m
        (SubdiffusiveProcess.LambdaStability.translatedDomain z (originCube 3 (n : ℤ)))) ∧
    paperENNRealLpNorm M.P.toMeasure 32
        (normalizedDefect M m
          (SubdiffusiveProcess.LambdaStability.translatedDomain z (originCube 3 (n : ℤ)))) ≤
      ENNReal.ofReal (89475125 / 1186923 * M.delta ^ 2) ∧
    ∀ e : Homogenization.Vec 3, vecNormSq e = 1 →
      Measurable (fun ω => J (SubdiffusiveProcess.LambdaStability.translatedDomain z (originCube 3 (n : ℤ)))
          (aCutoffCoeffOnData M m ω
            (SubdiffusiveProcess.LambdaStability.translatedDomain z (originCube 3 (n : ℤ)))).toCoeffOn
          ((Real.sqrt (ahom M m))⁻¹ • e) (Real.sqrt (ahom M m) • e)) ∧
      ∫⁻ ω, ENNReal.ofReal
          (J (SubdiffusiveProcess.LambdaStability.translatedDomain z (originCube 3 (n : ℤ)))
            (aCutoffCoeffOnData M m ω
              (SubdiffusiveProcess.LambdaStability.translatedDomain z
                (originCube 3 (n : ℤ)))).toCoeffOn
            ((Real.sqrt (ahom M m))⁻¹ • e) (Real.sqrt (ahom M m) • e)) ∂M.P.toMeasure ≤
        ENNReal.ofReal (17849411 / 3560769 * M.delta ^ 2) := by
  have h := Contract.cascade_of_obligations Contract.rowThree (by decide)
      Contract.rowThree_obligations M (by rw [Contract.rowThree_deltaStar]; exact hδ)
  rw [Contract.rowThree_C32, Contract.rowThree_Cmean] at h
  exact (Contract.cascadeConclusion_three_iff M).1 h m n hmn z

end GMCExplicitDelta.StatementProofs
