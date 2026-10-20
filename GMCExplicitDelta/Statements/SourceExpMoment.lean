module

public import GMCExplicitDelta.StatementProofs.SourceExpMoment
public import SubdiffusiveProcess.Model.GMCModel
public import Mathlib.Analysis.SpecialFunctions.Exp

@[expose] public section

open MeasureTheory

namespace GMCExplicitDelta

/-- First exponential moments of the source field and the per-scale strength (step S7):
`E exp(± g₀(x)) ≤ 1 + κ δ²` and `τ² ≤ κ δ²` with `κ = 1816027/10⁹`. -/
theorem source_exp_moment {d : ℕ} (M : SubdiffusiveProcess.Model.GMCModel d)
    (x : Homogenization.Vec d) :
    Integrable (fun ω : SubdiffusiveProcess.Model.PotentialSample d => Real.exp (ω 0 x))
        M.P.toMeasure ∧
    Integrable (fun ω : SubdiffusiveProcess.Model.PotentialSample d => Real.exp (-(ω 0 x)))
        M.P.toMeasure ∧
    ∫ ω, Real.exp (ω 0 x) ∂M.P.toMeasure ≤ 1 + 1816027 / 1000000000 * M.delta ^ 2 ∧
    ∫ ω, Real.exp (-(ω 0 x)) ∂M.P.toMeasure ≤ 1 + 1816027 / 1000000000 * M.delta ^ 2 ∧
    SubdiffusiveProcess.Model.tauSq M.P ≤ 1816027 / 1000000000 * M.delta ^ 2 :=
  by exact GMCExplicitDelta.StatementProofs.source_exp_moment

end GMCExplicitDelta
