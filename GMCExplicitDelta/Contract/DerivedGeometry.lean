module

public import GMCExplicitDelta.Contract.Row
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Contract layer: Haar exponents, cutoff geometry and localization (row-only constants)

§3.3 items 1, 2, 9 and the constants of H9–H13. Every quantity here depends on the row
only (not on `δ, D, F`), so it is the same at every disorder `δ_λ` (R4(e)).

Conventions. `π` is `Real.pi`; `3^r` with real `r` is `Real.rpow`; infinite series are exact
`tsum`s (the truncation `K_H` and the geometric tails of H12 are the numerics layer's job).
A `tsum` of a non-summable family is `0` in Lean; every series below is summable on the carrier
of the obligations (`0 < s < 1/2` gives `q_s < 3`, `u_s < 3`, and H12 bounds `b_k`), which the
analytic layer proves.

The formulas are the explicit constants of the descendant geometry (sharp version for `d ≥ 3`) and
of the localization estimate.
-/

@[expose] public section

open Real

namespace GMCExplicitDelta.Contract

namespace Row

variable {d : ℕ} (row : Row d)

/-! ### Item 1: Haar exponents and the history ratio -/

/-- `q_s = 3^{2s}`. -/
noncomputable def qs : ℝ := (3 : ℝ) ^ (2 * (row.s : ℝ))

/-- `u_s = 3^s`. -/
noncomputable def us : ℝ := (3 : ℝ) ^ (row.s : ℝ)

/-- `ρ_s = 3^{2s-1} = q_s/3`. -/
noncomputable def rhoS : ℝ := (3 : ℝ) ^ (2 * (row.s : ℝ) - 1)

/-- `w = 3^{-2s} = q_s^{-1}`. -/
noncomputable def wHaar : ℝ := (3 : ℝ) ^ (-(2 * (row.s : ℝ)))

/-- The history ratio `x = 3^{-2s+d/32}` (§1.7, §3.3 item 1). -/
noncomputable def xHist : ℝ := (3 : ℝ) ^ (-(2 * (row.s : ℝ)) + (d : ℝ) / 32)

/-- `C₀ = (1-w)/(1-x)`. Meaningful for `x < 1`, i.e. `2s > d/32` (O.par.1). -/
noncomputable def C0 : ℝ := (1 - row.wHaar) / (1 - row.xHist)

/-- `C₁ = C₀ x = (1-w)∑_{r≥1} x^r` (G5). -/
noncomputable def C1 : ℝ := row.C0 * row.xHist

/-! ### Item 2: good-event radius and descendant ellipticity -/

/-- `θ_R = (R + R⁻¹ - 2)/2` (§1.7). -/
noncomputable def thetaR : ℝ := ((row.R : ℝ) + (row.R : ℝ)⁻¹ - 2) / 2

end Row

/-- `𝗑(θ) = 1 + θ + √(θ(θ+2))`, the larger root of `y + y⁻¹ = 2 + 2θ` (C6). -/
noncomputable def ellipX (θ : ℝ) : ℝ := 1 + θ + √(θ * (θ + 2))

namespace Row

variable {d : ℕ} (row : Row d)

/-- `y_k = 𝗑(θ_R q_s^k)`, the depth-`k` ellipticity bound on the good event (G1). -/
noncomputable def yk (k : ℕ) : ℝ := ellipX (row.thetaR * row.qs ^ k)

/-! ### H7, H10: the cutoff and its constant mode -/

/-- The plateau width actually used: `ω` for `d ≥ 3`, and `1/2` (the full cosine) for `d = 2`
(§1.7, H7, H9). The row field `width` is ignored in `d = 2`. -/
noncomputable def omegaEff : ℝ := if d = 2 then 1 / 2 else (row.width : ℝ)

/-- `κ_ω = π/(2ω)` (H7); `κ = π` for `d = 2`. -/
noncomputable def kappaOmega : ℝ := π / (2 * row.omegaEff)

/-- `η_ω = κ_ω²/π² = 1/(4ω²)` (H7); `η = 1` for `d = 2`. -/
noncomputable def etaOmega : ℝ := 1 / (4 * row.omegaEff ^ 2)

/-- `𝒜 = 1 - ω = ∫ f_ω²` (H10). -/
noncomputable def cosA : ℝ := 1 - row.omegaEff

/-- `ℬ = π²/(4ω) = ∫ f_ω'²` (H10). -/
noncomputable def cosB : ℝ := π ^ 2 / (4 * row.omegaEff)

/-- `m_ω = 1 - 2ω + 4ω/π = ∫ f_ω` (H10, H13). -/
noncomputable def cosMean : ℝ := 1 - 2 * row.omegaEff + 4 * row.omegaEff / π

/-- `𝒫 = ω/4 - ω²/2 + ω³/3` (H10). -/
noncomputable def cosP : ℝ := row.omegaEff / 4 - row.omegaEff ^ 2 / 2 + row.omegaEff ^ 3 / 3

/-- `𝒞_* = 𝒫 - 2ω²(1-ω)/π² = ∫_layer y² f_ω²` (H10). -/
noncomputable def cosCstar : ℝ := row.cosP - 2 * row.omegaEff ^ 2 * (1 - row.omegaEff) / π ^ 2

/-- `𝒞 = 𝒞_* + (2/3)(1/2 - ω)³ = ∫ y² f_ω²` (H10). -/
noncomputable def cosC : ℝ := row.cosCstar + 2 / 3 * (1 / 2 - row.omegaEff) ^ 3

/-- `ℰ = κ_ω²𝒫 + (1-ω)/2 = ∫ y² f_ω'²` (H10). -/
noncomputable def cosE : ℝ := row.kappaOmega ^ 2 * row.cosP + (1 - row.omegaEff) / 2

/-- `𝖫_∘ = ℰ𝒜^{d-1} + (d-1)ℬ𝒞𝒜^{d-2}` (H10). For `d = 2` this is `π²/24`. -/
noncomputable def Lcirc : ℝ :=
  row.cosE * row.cosA ^ (d - 1) + ((d : ℝ) - 1) * row.cosB * row.cosC * row.cosA ^ (d - 2)

/-- `𝖶_∘ = 𝖫_∘ + (d-1)[ℰω𝒜^{d-2} + ℬ𝒞_*𝒜^{d-2} + (d-2)ℬ𝒞ω𝒜^{d-3}]` (H10).
For `d = 2` the last term has coefficient `d - 2 = 0` (the natural exponent `d - 3` truncates). -/
noncomputable def Wcirc : ℝ :=
  row.Lcirc + ((d : ℝ) - 1) *
    (row.cosE * row.omegaEff * row.cosA ^ (d - 2) + row.cosB * row.cosCstar * row.cosA ^ (d - 2)
      + ((d : ℝ) - 2) * row.cosB * row.cosC * row.omegaEff * row.cosA ^ (d - 3))

/-- `𝖧_∘ = d𝒜^{d-1}/(4ω) + 𝖶_∘/(4ω²)` (H10).
For `d = 2` this is `1/2 + π²/12`. -/
noncomputable def Hcirc : ℝ :=
  (d : ℝ) * row.cosA ^ (d - 1) / (4 * row.omegaEff) + row.Wcirc / (4 * row.omegaEff ^ 2)

/-- `𝖱_∘ = 𝖫_∘ - m_ω^{2d}` (H10). For `d = 2` this is `π²/24 - 16/π⁴`. -/
noncomputable def Rcirc : ℝ := row.Lcirc - row.cosMean ^ (2 * d)

end Row

/-! ### H9, H14: the geometric minimum series -/

/-- `∑_{j≥0} q^j min{Λ, 9^{-j}H}` (H9, H14). Summable for `q < 9`. -/
noncomputable def minSeries (q Λ H : ℝ) : ℝ := ∑' j : ℕ, q ^ j * min Λ (H / 9 ^ j)

namespace Row

variable {d : ℕ} (row : Row d)

/-! ### H9: multiplier coefficients of the Haar blocks -/

/-- `𝖫_k` for `k ≥ 1` (H9): `η_ω(5π²/54)9^{1-k}` for `d ≥ 3` (H5); for `d = 2`,
`𝖫₁ = 1/5 + 243/(10π⁴)` (H6) and `𝖫_k = (5π²/54)9^{1-k}` for `k ≥ 2` (H5, `η = 1`).
The value at `k = 0` is not used (the constant mode is `b₀`, H10). -/
noncomputable def haarL (k : ℕ) : ℝ :=
  if d = 2 ∧ k = 1 then 1 / 5 + 243 / (10 * π ^ 4)
  else row.etaOmega * (5 * π ^ 2 / 54) * (9 / 9 ^ k)

/-- `𝖧_k = η_ω(1 + d𝖫_k)` (H9); for `d = 2` this is `1 + 2𝖫_k`. -/
noncomputable def haarH (k : ℕ) : ℝ := row.etaOmega * (1 + (d : ℝ) * row.haarL k)

/-- The Haar multiplier coefficients `b_k` (H9, H10):
`b₀² = 𝖫_∘ + (q_s-1)∑_j q_s^j min{𝖱_∘, 9^{-j}𝖧_∘}` and, for `k ≥ 1`,
`b_k² = 𝖫_k + (q_s-1)∑_j q_s^j min{𝖫_k, 9^{-j}𝖧_k}`. -/
noncomputable def haarB (k : ℕ) : ℝ :=
  if k = 0 then √(row.Lcirc + (row.qs - 1) * minSeries row.qs row.Rcirc row.Hcirc)
  else √(row.haarL k + (row.qs - 1) * minSeries row.qs (row.haarL k) (row.haarH k))

/-! ### H12: Haar sums and geometric tails -/

/-- `S_b = ∑_{k≥0} b_k` (H12, §3.3 item 9). -/
noncomputable def Sb : ℝ := ∑' k : ℕ, row.haarB k

/-- `S_d = ∑_{k≥1} b_k √(k y_k / R)` (H12, §3.3 item 9). -/
noncomputable def Sd : ℝ :=
  ∑' k : ℕ, row.haarB (k + 1) * √(((k : ℝ) + 1) * row.yk (k + 1) / (row.R : ℝ))

/-- `𝖫₁^♯` of H12: `1` for `d = 2` (O.geo.2), `𝖫₁` for `d ≥ 3`. -/
noncomputable def L1sharp : ℝ := if d = 2 then 1 else row.haarL 1

/-- `𝖧^♯` of H12: `3` for `d = 2` (O.geo.2), `η_ω(1 + d𝖫₁)` for `d ≥ 3`. -/
noncomputable def Hsharp : ℝ := if d = 2 then 3 else row.etaOmega * (1 + (d : ℝ) * row.haarL 1)

/-- `K_s = √(9𝖫₁^♯ + 𝖧^♯(q_s-1)/(1-q_s/9))`, so that `b_k ≤ K_s(u_s/3)^k` for `k ≥ 1` (H12;
producer `tail_constant` / `tail`). -/
noncomputable def Ks : ℝ :=
  √(9 * row.L1sharp + row.Hsharp * (row.qs - 1) / (1 - row.qs / 9))

/-- `T_g = ∑_{k>g} b_k u_s^k` (H12, L4). The analytic bound is `T_g ≤ K_s ρ_s^{g+1}/(1-ρ_s)`. -/
noncomputable def Tg : ℝ := ∑' k : ℕ, row.haarB (row.g + 1 + k) * row.us ^ (row.g + 1 + k)

/-! ### H13: localization weights -/

/-- The bracket `m_ω - 1/N - π/(8ωN²)` with `N = 3^ν` (H13; obligation O.geo.1 asks it to be
positive). For `d = 2`: `2/π - 1/N - π/(4N²)`. -/
noncomputable def locBracket : ℝ :=
  row.cosMean - 1 / (3 : ℝ) ^ row.nu - π / (8 * row.omegaEff * ((3 : ℝ) ^ row.nu) ^ 2)

/-- `c_ν = [m_ω - 1/N - π/(8ωN²)]^d`, the lower bound of the localization weight (H13). -/
noncomputable def cNu : ℝ := row.locBracket ^ d

end Row

end GMCExplicitDelta.Contract
