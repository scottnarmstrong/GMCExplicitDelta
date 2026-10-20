module

public import GMCExplicitDelta.Contract.DerivedGeometry

/-!
# Contract layer: source history constants

§3.3 items 4–6 (G4–G6): the physical source history `F̄, Ḡ`, the subunit grid bound
`U_grid` and the history constant `H`. They depend on the disorder `δ` (and `H` on the cap `D`),
which are explicit arguments so that R4 evaluates the same definitions at `(δ_λ, λD)`.
-/

@[expose] public section

open Real

namespace GMCExplicitDelta.Contract

/-! ### Item 4: one-point norms (S8, G4) -/

/-- `P₃₂ = (2·64!)^{1/64}` (§5, S8). -/
noncomputable def P32 : ℝ := (2 * (Nat.factorial 64 : ℝ)) ^ ((1 : ℝ) / 64)

/-- `ς = 2^{1/64}` (§5, S8). -/
noncomputable def varsigma : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 64)

/-- `C_h = 2𝖺P₃₂ς`. -/
noncomputable def Ch : ℝ := 2 * (proxyA : ℝ) * P32 * varsigma

/-- `κ_h`: `0` for `d = 2` (no normalization drift, C10), `κ` for `d ≥ 3`. -/
noncomputable def kappaH (d : ℕ) : ℝ := if d = 2 then 0 else (kappaQ1 : ℝ)

/-- The PSD sphere factor `β_d = (β_d^{32})^{1/32}` (C13, §1.7). -/
noncomputable def sphereFactor (d : ℕ) : ℝ := (sphereFactorPow d : ℝ) ^ ((1 : ℝ) / 32)

/-- `A_F = 2κ_h√C_h δ³ + κ_h²δ⁴` (G4). -/
noncomputable def AF (d : ℕ) (δ : ℝ) : ℝ := 2 * kappaH d * √Ch * δ ^ 3 + kappaH d ^ 2 * δ ^ 4

/-- `A_G = 2κ_h√C_h ς δ³ + κ_h²ς²δ⁴` (G4). -/
noncomputable def AG (d : ℕ) (δ : ℝ) : ℝ :=
  2 * kappaH d * √Ch * varsigma * δ ^ 3 + kappaH d ^ 2 * varsigma ^ 2 * δ ^ 4

namespace Row

variable {d : ℕ} (row : Row d)

/-- `z_F = x e^{(128𝖺+2κ_h)δ²}` (O.hist.1). -/
noncomputable def zF (δ : ℝ) : ℝ :=
  row.xHist * Real.exp ((128 * (proxyA : ℝ) + 2 * kappaH d) * δ ^ 2)

/-- `z_G = x e^{(32𝖺+κ_h)δ²}` (O.hist.1). -/
noncomputable def zG (δ : ℝ) : ℝ :=
  row.xHist * Real.exp ((32 * (proxyA : ℝ) + kappaH d) * δ ^ 2)

/-- `F̄ = (1-w)[C_hδ² z_F/(1-z_F)² + A_F z_F(1+z_F)/(1-z_F)³]` (G5,
). Meaningful for `z_F < 1` (O.hist.1). -/
noncomputable def Fbar (δ : ℝ) : ℝ :=
  (1 - row.wHaar) *
    (Ch * δ ^ 2 * row.zF δ / (1 - row.zF δ) ^ 2 +
      AF d δ * row.zF δ * (1 + row.zF δ) / (1 - row.zF δ) ^ 3)

/-- `Ḡ = (1-w)[C_hδ² z_G/(1-z_G)² + A_G z_G(1+z_G)/(1-z_G)³]` (G5,
). -/
noncomputable def Gbar (δ : ℝ) : ℝ :=
  (1 - row.wHaar) *
    (Ch * δ ^ 2 * row.zG δ / (1 - row.zG δ) ^ 2 +
      AG d δ * row.zG δ * (1 + row.zG δ) / (1 - row.zG δ) ^ 3)

/-! ### Item 5: the subunit grid bound (G6) -/

/-- `N_g = n_g^d`, the number of grid points per unit cell. -/
def gridCount : ℕ := row.gridN ^ d

/-- `ħ = N_g^{1/128}`. -/
noncomputable def hbar : ℝ := (row.gridCount : ℝ) ^ ((1 : ℝ) / 128)

/-- `A_g = 3/(4n_g)`. -/
noncomputable def Ag : ℝ := 3 / (4 * (row.gridN : ℝ))

/-- `c_g = ħ√(2𝖺)`. -/
noncomputable def cg : ℝ := row.hbar * √(2 * (proxyA : ℝ))

/-- `b_g = -log x - (64𝖺+κ_h)δ² = (2s - d/32)log 3 - (64𝖺+κ_h)δ²` (O.hist.2). -/
noncomputable def bg (δ : ℝ) : ℝ :=
  -Real.log row.xHist - (64 * (proxyA : ℝ) + kappaH d) * δ ^ 2

/-- `M₁ = sup_{t≥1} (c_g√t + A_g)² e^{-b_g t}` (G6). The supremum is over a bounded
set when `b_g > 0` (O.hist.2); G6 identifies it as `(A_g+ζ_*)²e^{-b_gζ_*²/c_g²}`. -/
noncomputable def M1 (δ : ℝ) : ℝ :=
  ⨆ t : Set.Ici (1 : ℝ), (row.cg * √(t : ℝ) + row.Ag) ^ 2 * Real.exp (-(row.bg δ * t))

/-- `M₂ = sup_{t≥1} t² e^{-b_g t}` (G6); `M₂ ≤ 4/(b_g²e²)` for `b_g > 0`. -/
noncomputable def M2 (δ : ℝ) : ℝ :=
  ⨆ t : Set.Ici (1 : ℝ), (t : ℝ) ^ 2 * Real.exp (-(row.bg δ * t))

/-- `U_grid = (wςħ/(2x)) e^{32A_g²δ²} [(1+ε_sub)P₃₂δ²M₁ + (1+ε_sub⁻¹)κ_h²δ⁴M₂]`, with the bracket
replaced by `P₃₂δ²M₁` when `κ_h = 0`, i.e. `d = 2` (G6). -/
noncomputable def Ugrid (δ : ℝ) : ℝ :=
  row.wHaar * varsigma * row.hbar / (2 * row.xHist) * Real.exp (32 * row.Ag ^ 2 * δ ^ 2) *
    (if d = 2 then P32 * δ ^ 2 * row.M1 δ
     else (1 + (row.epsSub : ℝ)) * P32 * δ ^ 2 * row.M1 δ +
       (1 + (row.epsSub : ℝ)⁻¹) * kappaH d ^ 2 * δ ^ 4 * row.M2 δ)

/-! ### Item 6: the history constant -/

/-- `H = (1+η)C₁D + β_d(1+D)[F̄/(2η) + Ḡ] + U_grid` (G5–G7). -/
noncomputable def Hhist (δ D : ℝ) : ℝ :=
  (1 + (row.eta : ℝ)) * row.C1 * D +
    sphereFactor d * (1 + D) * (row.Fbar δ / (2 * (row.eta : ℝ)) + row.Gbar δ) + row.Ugrid δ

end Row

end GMCExplicitDelta.Contract
