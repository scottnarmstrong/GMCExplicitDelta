module

public import GMCExplicitDelta.Source.Variance

/-!
# Proof of `SourceVariance`

Proof of the theorem stated in `GMCExplicitDelta/Statements/SourceVariance.lean`.
-/

@[expose] public section

open MeasureTheory

namespace GMCExplicitDelta.StatementProofs

/-- Proof of `GMCExplicitDelta.source_variance` (step S6), with implicit binders so that the statement is proved by `exact`.
Proof: `GMCExplicitDelta/Source/Variance*.lean`. -/
theorem source_variance {d : ℕ} {M : SubdiffusiveProcess.Model.GMCModel d}
    {x : Homogenization.Vec d} :
    Integrable (fun ω : SubdiffusiveProcess.Model.PotentialSample d => (ω 0 x) ^ 2)
        M.P.toMeasure ∧
    ∫ ω, (ω 0 x) ^ 2 ∂M.P.toMeasure ≤
      Real.log 2 * M.delta ^ 2 / (35 + (13 + 2 * Real.sqrt 2) * Real.pi ^ 2) :=
  GMCExplicitDelta.Source.source_variance M x

end GMCExplicitDelta.StatementProofs
