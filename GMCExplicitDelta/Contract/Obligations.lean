module

public import GMCExplicitDelta.Contract.DerivedFresh
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Contract layer: the numeric obligations of a row

`Row.Obligations row` is the conjunction of the numeric obligations of §18.2–18.3, each an
inequality (or identity) between the exact derived constants of `Contract/Derived*.lean`, evaluated at
the row's own point `(δ_*, D, F)`. It is the only interface between the analytic proof
(`cascade_of_obligations`, which assumes it) and the numerics layer (`rowTwo_obligations` etc.,
which prove it). It is a `structure` of propositions (a conjunction with named projections, e.g.
`hO.bad2`); each field carries its obligation ID.

Choices:
* The common obligations O.src.1–7, O.avg.1, O.avg.2, O.sph are included: the analytic proof uses
  them as numeric inputs (S3, S4, S6, S7, S9, A4, A2, C13). For O.avg.1, O.sph only the row's
  dimension `d` is asked.
* O.elem (elementary constants inside proofs: `e^{3/4} > 2`, `π⁴ ≤ 486`, …) is not included: these
  are row-independent facts proved once inside the analytic layer.
* O.hist.3, O.avg.3, O.geo.3 have no exact content: they certify that the producer's rationals
  (`M̂₁, M̂₂, Ĥ`, `T_+`, `Ŝ_b, Ŝ_d, K̂_s, ĉ_ν`) bound the exact quantities, which the contract uses
  directly (`M₁, M₂` as suprema, `T_ϖ = ϖ^{32/31}`, `S_b, S_d` as `tsum`s). The numerics layer
  proves those bounds on the way to O.bad.2, O.bar.1, O.bar.2.
* Positivity and summability side conditions that follow analytically from the listed obligations
  (`x < 1`, summability of `b_k`, `𝔲_ℓ x^{-ℓ}`, `minSeries`, boundedness of the suprema in `M₁, M₂`)
  are not repeated.
-/

@[expose] public section

open Real

namespace GMCExplicitDelta.Contract

namespace Row

variable {d : ℕ}

/-- The numeric obligations of §18.2–18.3 for the row, at `δ = δ_*` and the row's
`D, F`. -/
structure Obligations (row : Row d) : Prop where
  /-- **O.src.1** (S3): `𝖺 > (3 - 2√2)/16`. -/
  src1 : (3 - 2 * √2) / 16 < (proxyA : ℝ)
  /-- **O.src.2** (S6): `𝗎 > log 2/(35 + (13 + 2√2)π²)`. -/
  src2 : Real.log 2 / (35 + (13 + 2 * √2) * π ^ 2) < (varU : ℝ)
  /-- **O.src.3** (S7): `𝗎 < 𝖺`, `κ < 𝖺/2`, `𝗎/2 + 4(e^{𝖺/8} - 1 - 𝖺/8) < κ`. -/
  src3 : (varU : ℝ) < proxyA ∧ (kappaQ1 : ℝ) < (proxyA : ℝ) / 2 ∧
    (varU : ℝ) / 2 + 4 * (Real.exp ((proxyA : ℝ) / 8) - 1 - (proxyA : ℝ) / 8) < kappaQ1
  /-- **O.src.4** (S4): `c₂ ≥ (4/3)(√3 - 1)`. -/
  src4 : 4 / 3 * (√3 - 1) ≤ (ratioC2 : ℝ)
  /-- **O.src.5** (S4): `c₃ ≥ 72(√3 - 1)/(5(e³ - e))`. -/
  src5 : 72 * (√3 - 1) / (5 * (Real.exp 3 - Real.exp 1)) ≤ (ratioC3 : ℝ)
  /-- **O.src.6** (S9, I4): `0 < c₃ < c₂ < 1` and `0 ≤ 𝗎 ≤ 𝖺`. -/
  src6 : 0 < ratioC3 ∧ ratioC3 < ratioC2 ∧ ratioC2 < 1 ∧ 0 ≤ varU ∧ varU ≤ proxyA
  /-- **O.src.7**: `δ_* ≤ 1/2`. -/
  src7 : row.deltaStar ≤ 1 / 2
  /-- **O.avg.1** (A4), for the row's dimension: `𝓛_d > 0` and `σ_d^{32}𝓛_d > 1`. -/
  avg1 : 0 < sphereLower d ∧ 1 < sigmaNorm d ^ 32 * sphereLower d
  /-- **O.avg.2** (A2): the values `𝒜(32, k)`, `k = 1, …, 16`. -/
  avg2 : ∀ k < 16, assocStirling 32 (k + 1) = assocStirling32Table.getD k 0
  /-- **O.sph** (C13), for the row's dimension:
  `β_d^{32} = √π Γ(32 + d/2)/(Γ(d/2) Γ(32 + 1/2))`. -/
  sph : (sphereFactorPow d : ℝ) =
    √π * Real.Gamma (32 + (d : ℝ) / 2) / (Real.Gamma ((d : ℝ) / 2) * Real.Gamma (32 + 1 / 2))
  /-- **O.par.1**: `D > 0`, `0 < F ≤ min(D, 1)`, `h ≥ g ≥ max(ν, 2)`, `0 < s < 1/2`, `2s > d/32`. -/
  par1 : 0 < row.D ∧ 0 < row.F ∧ row.F ≤ min row.D 1 ∧ max row.nu 2 ≤ row.g ∧ row.g ≤ row.h ∧
    0 < row.s ∧ row.s < 1 / 2 ∧ (d : ℚ) / 32 < 2 * row.s
  /-- **O.par.2**: `R > 1`, `ε > 0`, `g - ν ≥ 1`, `n_g ≥ 1`, `b_bad > 0`; for `d ≥ 3`:
  `η_v > 0`, `0 < ω ≤ 1/2`. -/
  par2 : 1 < row.R ∧ 0 < row.epsilon ∧ row.nu + 1 ≤ row.g ∧ 1 ≤ row.gridN ∧ 0 < row.badBudget ∧
    (d ≠ 2 → 0 < row.young ∧ 0 < row.width ∧ row.width ≤ 1 / 2)
  /-- **O.par.3**: `0 < η ≤ 1`. -/
  par3 : 0 < row.eta ∧ row.eta ≤ 1
  /-- **O.par.4**: `ε_sub > 0` (the Young split `(X+Y)² ≤ (1+ε_sub)X² + (1+ε_sub⁻¹)Y²` of `U_grid`, G6;
  added 2026-10-19 after the G9 finding: without it `e_⋆` can be negative for `d ≥ 3`). -/
  par4 : 0 < row.epsSub
  /-- **O.hist.1** (G5): `z_G < z_F < 1` at `δ_*`. -/
  hist1 : row.zG row.deltaStar < row.zF row.deltaStar ∧ row.zF row.deltaStar < 1
  /-- **O.hist.2** (G6): `b_g = (2s - d/32)log 3 - (64𝖺 + κ_h)δ_*² > 0`. -/
  hist2 : 0 < row.bg row.deltaStar
  /-- **O.avg.4** (G7): `3^{-d/2} < x`. -/
  avg4 : (3 : ℝ) ^ (-((d : ℝ) / 2)) < row.xHist
  /-- **O.avg.5** (G7): `𝔲₁₂ = min{1, σ_d B̄₃₂(3^{11d}, ϖ)} < 1` (index = coarse-history truncation). -/
  avg5 : frakU d row.historyCutoff row.D row.F < 1
  /-- **O.bad.1** (G8): `θ_R > F`. -/
  bad1 : (row.F : ℝ) < row.thetaR
  /-- **O.bad.2** (G9, T3): `bad = Φ_{log(1+2F)}(U_{g-ν})/F · (e_⋆/(θ_R - F))^{31} < b_bad`. -/
  bad2 : row.badCharge row.deltaStar row.D row.F < row.badBudget
  /-- **O.geo.1** (H13, H10): the `c_ν` bracket is positive; for `d ≥ 3`, `𝖫_∘, 𝖱_∘, 𝖧_∘ > 0`. -/
  geo1 : 0 < row.locBracket ∧ (d ≠ 2 → 0 < row.Lcirc ∧ 0 < row.Rcirc ∧ 0 < row.Hcirc)
  /-- **O.geo.2** (H12): for `d = 2`, `1 < q_s < 3`, `u_s < 3`, `𝖫_k ≤ 9^{1-k}` and `1 + 2𝖫_k ≤ 3`
  for `k ≥ 1`; for every `d`, `ρ_s < 1`. -/
  geo2 : (d = 2 → 1 < row.qs ∧ row.qs < 3 ∧ row.us < 3 ∧
      ∀ k : ℕ, 1 ≤ k → row.haarL k ≤ 9 / 9 ^ k ∧ 1 + 2 * row.haarL k ≤ 3) ∧ row.rhoS < 1
  /-- **O.var.1** (V3): `0 < ρ_v < 1`. -/
  var1 : 0 < row.rhoV ∧ row.rhoV < 1
  /-- **O.geo.4** (L4): `0 < τ_abs = (1+ε)RK_sρ_s^{g+1}/(c_ν(1-ρ_s)) < 1`. -/
  geo4 : 0 < row.tauAbs ∧ row.tauAbs < 1
  /-- **O.bar.1** (T3): `0 < Z < M` and
  `𝔰 = (1-τ_abs)Z - C(t_⋆)√Z - νB(1-t_⋆)𝗊_⋆ - M b_bad > 0`. -/
  bar1 : 0 < row.Z ∧ (row.Z : ℝ) < (row.Mwin : ℝ) ∧ 0 < row.barrier row.D row.F
  /-- **O.bar.2** (T4, `d = 2`): `n_t ≥ 0`, `n_f ≥ 0`, the derivative test (S)
  `b m_t + c m_f ≥ (1-u_⋆²/2)/𝗋(u_⋆)² [a u_⋆/(4√𝗊(u_⋆)) + 𝓛u_⋆/2]`, and the normalized margin
  `(1-τ_abs)√Z - 𝓡(1) - M b_bad/√Z > 0`. -/
  bar2 : d = 2 →
    0 ≤ nMatch row.vT0 (row.vT1 row.D row.F) (row.uStar row.F) ∧
    0 ≤ nMatch row.vF0 (row.vF1 row.D row.F) (row.uStar row.F) ∧
    row.t4Loss row.F ≤
      row.t4b * mMatch row.vT0 (row.vT1 row.D row.F) (row.uStar row.F) +
        row.t4c * mMatch row.vF0 (row.vF1 row.D row.F) (row.uStar row.F) ∧
    0 < (1 - row.tauAbs) * √(row.Z : ℝ) - row.t4R row.D row.F 1 -
      (row.Mwin : ℝ) * (row.badBudget : ℝ) / √(row.Z : ℝ)
  /-- **O.fin.1** (R3, I9): `t_⋆F ≤ U_h`. -/
  fin1 : row.Fnext row.F ≤ row.Dnext row.D row.F
  /-- **O.band.1** (I4(b)): `z_b = 1520𝖺δ_*² < N_b + 2`. -/
  band1 : bandNormBound row.deltaStar < (row.bandTerms : ℝ) + 2
  /-- **O.ret.1** (I9, R3): `post < D`. -/
  ret1 : row.post row.deltaStar row.D row.F < row.D
  /-- **O.ret.2** (I9, R3): `meanpost < F`. -/
  ret2 : row.meanpost row.deltaStar row.F < row.F
  /-- **O.ret.3** (K2, R5): `seed < D`. -/
  ret3 : row.seed row.deltaStar < row.D
  /-- **O.ret.4** (K3, R5): `meanseed < F`. -/
  ret4 : row.meanseed row.deltaStar < row.F

end Row

end GMCExplicitDelta.Contract
