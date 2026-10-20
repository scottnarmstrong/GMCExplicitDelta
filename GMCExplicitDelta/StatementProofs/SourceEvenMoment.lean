module

public import GMCExplicitDelta.Source.EndpointStripSource

/-!
# Proof of `SourceEvenMoment`

Proof of the theorem stated in `GMCExplicitDelta/Statements/SourceEvenMoment.lean`.
-/

@[expose] public section

open MeasureTheory

namespace GMCExplicitDelta.StatementProofs

/-- Proof of `GMCExplicitDelta.source_even_moment` (step S3), with implicit binders so that the
statement is proved by `exact`. Proof: the endpoint-strip argument
(`GMCExplicitDelta/Source/EndpointStrip*.lean`). -/
theorem source_even_moment {d : ℕ} {M : SubdiffusiveProcess.Model.GMCModel d}
    {x : Homogenization.Vec d} {k : ℕ} :
    Integrable (fun ω : SubdiffusiveProcess.Model.PotentialSample d => (ω 0 x) ^ (2 * k))
        M.P.toMeasure ∧
    ∫ ω, (ω 0 x) ^ (2 * k) ∂M.P.toMeasure ≤
      ((2 * k - 1).doubleFactorial : ℝ) * ((3 - 2 * Real.sqrt 2) / 16 * M.delta ^ 2) ^ k :=
  GMCExplicitDelta.Source.source_even_moment M x k

end GMCExplicitDelta.StatementProofs
