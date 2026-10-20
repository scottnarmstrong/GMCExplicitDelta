module

public import GMCExplicitDelta.Contract.Obligations
public import GMCExplicitDelta.Contract.Conclusion
public import GMCExplicitDelta.Assembly.Induction

/-!
# Intermediate statements: the analytic half of the contract

`cascade_of_obligations`: for a row in dimension `d ∈ {2, 3, 4}` whose numeric obligations hold, every
model with `δ ≤ δ_*` satisfies the cascade conclusion with `C₃₂ = D/δ_*²`, `C_mean = F/δ_*²`
(R5, with R1–R4, K2, K3 and everything they use; the λ-scaling of R4 is internal:
`λ = (δ/δ_*)²`, and the derived constants are evaluated at `(δ, λD, λF)`).

The proof is
`GMCExplicitDelta.Assembly.cascade_assembled` (`Assembly/Induction.lean`), which depends only on the
intermediate statements `GMCExplicitDelta/Steps/Assembly*.lean`.
-/

@[expose] public section

namespace GMCExplicitDelta.Contract

/-- **Analytic target (R5).** If a row in dimension `d ∈ {2, 3, 4}` satisfies its numeric
obligations, then every model with disorder `δ ≤ δ_*` satisfies the cascade conclusion with
`C₃₂ = D/δ_*²` and `C_mean = F/δ_*²`. -/
theorem cascade_of_obligations {d : ℕ} (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ))
    (hO : row.Obligations) (M : SubdiffusiveProcess.Model.GMCModel d)
    (hδ : M.delta ≤ (row.deltaStar : ℝ)) :
    CascadeConclusion M ((row.D : ℝ) / (row.deltaStar : ℝ) ^ 2)
      ((row.F : ℝ) / (row.deltaStar : ℝ) ^ 2) :=
  Assembly.cascade_assembled row hd hO M hδ

end GMCExplicitDelta.Contract
