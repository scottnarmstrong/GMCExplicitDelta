module

public import GMCExplicitDelta.Source.ExpMomentModel
public import GMCExplicitDelta.Source.Variance

/-!
# Proof of `SourceExpMoment`

Proof of the theorem stated in `GMCExplicitDelta/Statements/SourceExpMoment.lean`.
-/

@[expose] public section

open MeasureTheory

namespace GMCExplicitDelta.StatementProofs

/-- Proof of `GMCExplicitDelta.source_exp_moment` (step S7), with implicit binders so that the statement is proved by `exact`.
Proof: the exponential-moment series (`Source/ExpMoment*.lean`) applied to the
proved variance bound (`Source/Variance*.lean`). -/
theorem source_exp_moment {d : ℕ} {M : SubdiffusiveProcess.Model.GMCModel d}
    {x : Homogenization.Vec d} :
    Integrable (fun ω : SubdiffusiveProcess.Model.PotentialSample d => Real.exp (ω 0 x))
        M.P.toMeasure ∧
    Integrable (fun ω : SubdiffusiveProcess.Model.PotentialSample d => Real.exp (-(ω 0 x)))
        M.P.toMeasure ∧
    ∫ ω, Real.exp (ω 0 x) ∂M.P.toMeasure ≤ 1 + 1816027 / 1000000000 * M.delta ^ 2 ∧
    ∫ ω, Real.exp (-(ω 0 x)) ∂M.P.toMeasure ≤ 1 + 1816027 / 1000000000 * M.delta ^ 2 ∧
    SubdiffusiveProcess.Model.tauSq M.P ≤ 1816027 / 1000000000 * M.delta ^ 2 := by
  refine GMCExplicitDelta.Source.exp_moment_of_variance M x ?_
  have h := (GMCExplicitDelta.Source.source_variance M x).2
  have hpos : (0 : ℝ) < 35 + (13 + 2 * Real.sqrt 2) * Real.pi ^ 2 := by positivity
  calc ∫ ω, (ω 0 x) ^ 2 ∂M.P.toMeasure
      ≤ Real.log 2 * M.delta ^ 2 / (35 + (13 + 2 * Real.sqrt 2) * Real.pi ^ 2) := h
    _ = GMCExplicitDelta.Source.sourceVarianceTrue * M.delta ^ 2 := by
        unfold GMCExplicitDelta.Source.sourceVarianceTrue; field_simp

end GMCExplicitDelta.StatementProofs
