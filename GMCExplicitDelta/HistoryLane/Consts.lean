module

public import GMCExplicitDelta.Contract.DerivedAveraging

/-!
# History lane: closed forms of the fine and grid bounds (G4, G6)

* `fineF d δ r`, `fineG d δ r`: the bounds of G4 for `F_r = ‖(ρ-1)²‖_{32}` and
  `G_r = ‖ρ + ρ⁻¹ - 2‖_{32}` at `r = L - k`.
* `fineCap row δ D r = (1+η)D + β_d(1+D)(F_r/(2η) + G_r)`: the per-cell bound of G3 with G4 inserted.
* `gridBound row δ L = B_L`: the bound of G6 for `‖sup_{V ⊆ U'} J^max(V; b_L)‖_{32}`.
-/

@[expose] public section

namespace GMCExplicitDelta.Assembly

open GMCExplicitDelta.Contract

variable {d : ℕ}

/-- G4: `F_r ≤ e^{(128𝖺+2κ_h)rδ²}[C_h rδ² + A_F r²]`. -/
noncomputable def fineF (d : ℕ) (δ r : ℝ) : ℝ :=
  Real.exp ((128 * (proxyA : ℝ) + 2 * kappaH d) * r * δ ^ 2) * (Ch * r * δ ^ 2 + AF d δ * r ^ 2)

/-- G4: `G_r ≤ e^{(32𝖺+κ_h)rδ²}[C_h rδ² + A_G r²]`. -/
noncomputable def fineG (d : ℕ) (δ r : ℝ) : ℝ :=
  Real.exp ((32 * (proxyA : ℝ) + kappaH d) * r * δ ^ 2) * (Ch * r * δ ^ 2 + AG d δ * r ^ 2)

/-- The per-cell bound of G3 with G4 inserted, for a cell of scale `L - r`. -/
noncomputable def fineCap (row : Row d) (δ D r : ℝ) : ℝ :=
  (1 + (row.eta : ℝ)) * D +
    sphereFactor d * (1 + D) * (fineF d δ r / (2 * (row.eta : ℝ)) + fineG d δ r)

/-- `B_L` of G6. -/
noncomputable def gridBound (row : Row d) (δ : ℝ) (L : ℕ) : ℝ :=
  varsigma * row.hbar / 2 *
      (δ * √P32 * (row.cg * √((L : ℝ) + 1) + row.Ag) + kappaH d * ((L : ℝ) + 1) * δ ^ 2) ^ 2 *
    Real.exp ((64 * (proxyA : ℝ) * ((L : ℝ) + 1) + 32 * row.Ag ^ 2 + kappaH d * ((L : ℝ) + 1)) *
      δ ^ 2)

end GMCExplicitDelta.Assembly
