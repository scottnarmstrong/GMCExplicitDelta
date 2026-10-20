module

public import GMCExplicitDelta.StatementProofs.SourceEvenMoment
public import SubdiffusiveProcess.Model.GMCModel
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Factorial.DoubleFactorial

@[expose] public section

open MeasureTheory

namespace GMCExplicitDelta

/-- All even moments of the source field at a point (step S3): for every `x` and `k`,
`E g₀(x)^{2k} ≤ (2k-1)!! (a_* δ²)^k` with `a_* = (3 - 2√2)/16`, and these moments are finite. -/
theorem source_even_moment {d : ℕ} (M : SubdiffusiveProcess.Model.GMCModel d)
    (x : Homogenization.Vec d) (k : ℕ) :
    Integrable (fun ω : SubdiffusiveProcess.Model.PotentialSample d => (ω 0 x) ^ (2 * k))
        M.P.toMeasure ∧
    ∫ ω, (ω 0 x) ^ (2 * k) ∂M.P.toMeasure ≤
      ((2 * k - 1).doubleFactorial : ℝ) * ((3 - 2 * Real.sqrt 2) / 16 * M.delta ^ 2) ^ k :=
  by exact GMCExplicitDelta.StatementProofs.source_even_moment

end GMCExplicitDelta
