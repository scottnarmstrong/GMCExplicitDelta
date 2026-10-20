module

public import GMCExplicitDelta.StatementProofs.SourceVariance
public import SubdiffusiveProcess.Model.GMCModel
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

open MeasureTheory

namespace GMCExplicitDelta

/-- Variance of the source field at a point (step S6):
`E g₀(x)² ≤ log 2 · δ² / (35 + (13 + 2√2) π²)`. -/
theorem source_variance {d : ℕ} (M : SubdiffusiveProcess.Model.GMCModel d)
    (x : Homogenization.Vec d) :
    Integrable (fun ω : SubdiffusiveProcess.Model.PotentialSample d => (ω 0 x) ^ 2)
        M.P.toMeasure ∧
    ∫ ω, (ω 0 x) ^ 2 ∂M.P.toMeasure ≤
      Real.log 2 * M.delta ^ 2 / (35 + (13 + 2 * Real.sqrt 2) * Real.pi ^ 2) :=
  by exact GMCExplicitDelta.StatementProofs.source_variance

end GMCExplicitDelta
