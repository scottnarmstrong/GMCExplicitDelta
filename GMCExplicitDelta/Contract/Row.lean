module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.Order.Field.Rat

/-!
# Contract layer: row inputs and fixed source constants

A `Row d` collects the exact inputs of one certified row in dimension `d` (§3.1–3.2):
the decimals of the certified table as exact rationals, the integers as naturals, and the
rationals fixed by the producer and recorded in the certified exact data
(`Z`, `η`, `ε_sub`, the truncation orders).

Design: the dimension is a *parameter* of `Row`, not a field. The model `GMCModel d`, the vectors
`Vec d` and the cubes `originCube d` are indexed by `d`, so with `row : Row d` the analytic target
can take `M : GMCModel d` with no transport along `row.d = d`; the concrete rows have types
`Row 2`, `Row 3`, `Row 4` and the main theorems use them directly.

The source constants `𝖺, 𝗎, κ, c₂, c₃` (§1.7, §3.1 "Common") and the per-dimension constants
`σ_d` (A4) and `β_d^{32}` (C13) are global definitions, not row fields: the certified data assert that
the row fields `proxy`, `kappa` equal these literals, and `σ_d`, `c₂`, `c₃` are imported
literals.

Flags `terminal`, `exact_matching`, and the fields `r = 0`, `split = 0` are not stored: the
route (and every formula of §3.3) is the terminal route with `r = split = 0`, with exact matching
exactly in `d = 2`.
-/

@[expose] public section

namespace GMCExplicitDelta.Contract

/-- The exact inputs of one certified row in dimension `d` (§3.1–3.2). -/
structure Row (d : ℕ) where
  /-- `δ_*` (`delta`): the disorder threshold of the row. -/
  deltaStar : ℚ
  /-- `h`: block length of the frozen step (number of fresh bands inserted). -/
  h : ℕ
  /-- `g`: burn-in gap. -/
  g : ℕ
  /-- `ν` (`depth`): localization depth. -/
  nu : ℕ
  /-- `n_g` (`grid_n`): grid cells per axis in the subunit grid bound (G6). -/
  gridN : ℕ
  /-- `D`: native `L^32` cap at `δ_*`. -/
  D : ℚ
  /-- `F`: native directional-mean cap at `δ_*`. -/
  F : ℚ
  /-- `s`: Haar exponent. -/
  s : ℚ
  /-- `R`: good-event radius. -/
  R : ℚ
  /-- `ε` (`epsilon`): localization Young parameter. -/
  epsilon : ℚ
  /-- `η_v` (`young`): variance Young parameter (used only for `d ≥ 3`). -/
  young : ℚ
  /-- `ω` (`width`): plateau width (used only for `d ≥ 3`; `d = 2` uses the full cosine). -/
  width : ℚ
  /-- `b_bad` (`bad_budget`): normalized bad budget. -/
  badBudget : ℚ
  /-- `Z`: terminal barrier (§3.2, rounded up by the producer). -/
  Z : ℚ
  /-- `η`: history Young parameter (§3.2, rational from the output JSON). -/
  eta : ℚ
  /-- `ε_sub`: subunit Young parameter (§3.2; used only for `d ≥ 3`, where `κ_h ≠ 0`). -/
  epsSub : ℚ
  /-- `K_H`: Haar truncation order of the certified majorants (numerics only). -/
  haarCutoff : ℕ
  /-- Coarse-history truncation (`Bcut = 12`): the index of `𝔲` in O.avg.5. -/
  historyCutoff : ℕ
  /-- `N_b` (`band_terms`): band-operator truncation order, used in O.band.1. -/
  bandTerms : ℕ

/-- `𝖺 = 1072331/10^8`, the all-even one-point proxy (§1.7, S3). -/
def proxyA : ℚ := 1072331 / 100000000

/-- `𝗎 = 1812431/(5·10^8)`, the one-point variance proxy (§1.7, S6). -/
def varU : ℚ := 1812431 / 500000000

/-- `κ = 1816027/10^9`, the `q = 1` MGF / drift constant (§1.7, S7). -/
def kappaQ1 : ℚ := 1816027 / 1000000000

/-- `c₂ = 244017/250000`, the fourth-moment ratio (§1.7, S4). -/
def ratioC2 : ℚ := 244017 / 250000

/-- `c₃ = 303489/500000`, the higher-moment ratio (§1.7, S4). -/
def ratioC3 : ℚ := 303489 / 500000

/-- The signed-matrix norming constant `σ_d` (A4):
`σ₂ = 1085173/10^6`, `σ₃ = 290099/250000`, `σ₄ = 615471/500000`.
Meaningful for `d ∈ {2,3,4}` only (other `d` get the `d = 4` value). -/
def sigmaNorm (d : ℕ) : ℚ :=
  if d = 2 then 1085173 / 1000000 else if d = 3 then 290099 / 250000 else 615471 / 500000

/-- The fresh PSD sphere factor to the 32nd power, `β_d^{32}` (C13;
`sphere_power`):
`β₂^{32} = 4^{32}/binom(64,32)`, `β₃^{32} = 65`, `β₄^{32} = 33·4^{32}/binom(64,32)`.
Meaningful for `d ∈ {2,3,4}` only. -/
def sphereFactorPow (d : ℕ) : ℚ :=
  if d = 2 then 4 ^ 32 / (Nat.choose 64 32 : ℚ)
  else if d = 3 then 65 else 33 * 4 ^ 32 / (Nat.choose 64 32 : ℚ)

end GMCExplicitDelta.Contract
