module

public import GMCExplicitDelta.Assembly.ModelInduction
public import GMCExplicitDelta.Proofs.Scaling.Bad
public import GMCExplicitDelta.Proofs.Scaling.Barrier

/-!
# Intermediate statements: every smaller disorder (R4), as pure statements about contract constants

Intermediate statements of the assembly of `cascade_of_obligations`. Each is proved in
`GMCExplicitDelta/Proofs/`. No model objects occur: these are inequalities
between the exact derived constants of `Contract/Derived*.lean`, at the row's point `(δ_*, D, F)` and at
the scaled point `(δ, λD, λF)` with `λ = lamOf row δ = (δ/δ_*)²`, `0 < δ ≤ δ_*` (so `δ² = λδ_*²`).

* `badCharge_scale_le` — R4(b)–(d): `bad_λ ≤ bad`.
* `barrier_scale_pos` — R4(e)–(f): `𝔰_λ > 0` (for `d = 2` through T4 and O.bar.2).
* `freshReturns_scale_le` — R4(g) and I10: `post_λ ≤ λ post`, `meanpost_λ ≤ λ meanpost`,
  `seed_λ ≤ λ seed`, `meanseed_λ ≤ λ meanseed`.
-/

@[expose] public section

namespace GMCExplicitDelta.Assembly

open Contract

variable {d : ℕ}

/-- **R4(b)–(d) (bad charge at smaller disorder).** For `0 < δ ≤ δ_*` and `λ = (δ/δ_*)²`:
`bad(δ, λD, λF) ≤ bad(δ_*, D, F)` (`H_λ ≤ λH`, `e_{⋆,λ} ≤ λe_⋆`, the prefactor
`Φ_{log(1+2F)}(U_{g-ν})/F` is nondecreasing in `λ`, `θ_R - λF ≥ θ_R - F > 0`). -/
theorem badCharge_scale_le (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ))
    (hO : row.Obligations) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ (row.deltaStar : ℝ)) :
    row.badCharge δ (lamOf row δ * row.D) (lamOf row δ * row.F) ≤
      row.badCharge row.deltaStar row.D row.F :=
  badCharge_scale_le_proof row hd hO hδ0 hδ

/-- **R4(e)–(f) (barrier at smaller disorder).** For `0 < λ ≤ 1`: `𝔰(λD, λF) > 0` (for `d ≥ 3`
because `𝔰_λ ≥ 𝔰`; for `d = 2` by the derivative test T4 with obligation O.bar.2). -/
theorem barrier_scale_pos (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) :
    0 < row.barrier (lam * row.D) (lam * row.F) :=
  barrier_scale_pos_proof row hd hO h0 h1

/-- **R4(g) and I10 (fresh returns and seeds at smaller disorder).** For `0 < δ ≤ δ_*` and
`λ = (δ/δ_*)²`: `post(δ, λD, λF) ≤ λ post(δ_*, D, F)`, `meanpost(δ, λF) ≤ λ meanpost(δ_*, F)`,
`seed(δ) ≤ λ seed(δ_*)` and `meanseed(δ) ≤ λ meanseed(δ_*)`. -/
theorem freshReturns_scale_le (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ))
    (hO : row.Obligations) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ (row.deltaStar : ℝ)) :
    row.post δ (lamOf row δ * row.D) (lamOf row δ * row.F) ≤
        lamOf row δ * row.post row.deltaStar row.D row.F ∧
      row.meanpost δ (lamOf row δ * row.F) ≤ lamOf row δ * row.meanpost row.deltaStar row.F ∧
      row.seed δ ≤ lamOf row δ * row.seed row.deltaStar ∧
      row.meanseed δ ≤ lamOf row δ * row.meanseed row.deltaStar :=
  freshReturns_scale_le_proof row hd hO hδ0 hδ

end GMCExplicitDelta.Assembly
