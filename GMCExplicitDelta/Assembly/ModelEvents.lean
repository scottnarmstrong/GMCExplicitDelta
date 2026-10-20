module

public import GMCExplicitDelta.Assembly.ModelFrozen

/-!
# Assembly: good event, bad response and the per-scale inequality

§10 (preamble, G9) and L6.

* `depthMax M L z n j = e_j(z + Q_n)`: the maximum of `J^max(U; b_L)` over the depth-`j` cells `U` of
  `z + Q_n` (a finite supremum in `ℝ≥0∞`; cells of negative scale are included).
* `haarStat row M L z n = T_{2s}(z + Q_n) = (1-w)∑_{j≥0} w^j e_j(z + Q_n)` (an `ℝ≥0∞`-valued series),
  `goodEvent row M L z n = 𝒢(z + Q_n) = {T_{2s} ≤ θ_R}`.
* `BadResponseBound row M L D F`: the conclusion of G9 for every target `z + Q_{m'}` with
  `m' ≥ L + g`, every depth-`ν` cell `U`, unit `e`, and both matched pairs (planar `((1+μ)e, e)`,
  `μ ∈ [0,F]`, with divisor `𝗋(μ) = (1+μ)(1+μ/2)`; reciprocal `(√β e, e/√β)`, `β ∈ [1, 1+2F]`, with
  divisor `1`): `𝔼[J(U,p_⋆,q_⋆;b_L) 1_{𝒢ᶜ}] ≤ r_⋆ F bad`, `bad = row.badCharge δ D F`.
* `qPair d μ`, `rPair d μ`: the matching ratio `𝗊(μ)` and divisor `𝗋(μ)` of L6 (`d = 2`), both `1`
  for `d ≥ 3`; `row.qStar F = qPair d (row.uStar F)`, `row.rStar F = rPair d (row.uStar F)`.
* `PerScaleIneq row f V L F bd m'`: the normalized per-scale inequality of L6 at the observation
  scale `m'`, for abstract sequences `f, V` (in L6, `f = fMean M L`, `V = varV M L`) and bad term
  `bd` (in L6, `bd = row.badCharge δ D F`).
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta.Assembly

open Contract

variable {d : ℕ}

/-- `e_j(z + Q_n) = max{J^max(U; b_L) : U a depth-`j` cell of z + Q_n}` (§10 preamble). -/
noncomputable def depthMax (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (z : Homogenization.Vec d) (n j : ℕ) (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    ℝ≥0∞ :=
  (descendantsAtDepth (originCube d (n : ℤ)) j).sup fun R => normalizedDefect M L (cellAt z R) ω

/-- The all-descendant statistic `T_{2s}(z + Q_n) = (1-w)∑_{j≥0} w^j e_j(z + Q_n)`, `w = 3^{-2s}`
(§10 preamble). -/
noncomputable def haarStat (row : Row d) (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (z : Homogenization.Vec d) (n : ℕ) (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    ℝ≥0∞ :=
  ∑' j : ℕ, ENNReal.ofReal ((1 - row.wHaar) * row.wHaar ^ j) * depthMax M L z n j ω

/-- The good event `𝒢(z + Q_n) = {T_{2s}(z + Q_n) ≤ θ_R}` (§10 preamble). -/
def goodEvent (row : Row d) (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (z : Homogenization.Vec d) (n : ℕ) : Set (SubdiffusiveProcess.Model.PotentialSample d) :=
  {ω | haarStat row M L z n ω ≤ ENNReal.ofReal row.thetaR}

/-- The matching ratio `𝗊(μ) = 𝖢(μ)/𝗋(μ)` for `d = 2`, `1` for `d ≥ 3` (L6). -/
noncomputable def qPair (d : ℕ) (μ : ℝ) : ℝ := if d = 2 then qMatch μ else 1

/-- The matching divisor `𝗋(μ) = (1+μ)(1+μ/2)` for `d = 2`, `1` for `d ≥ 3` (L6). -/
noncomputable def rPair (d : ℕ) (μ : ℝ) : ℝ := if d = 2 then rMatch μ else 1

/-- **Bad response of the matched pairs** (the conclusion of G9): for every target `z + Q_{m'}` with
`m' ≥ L + g`, every depth-`ν` cell `U = z + R` of it, and every unit `e`,
`𝔼[J(U,(1+μ)e,e;b_L) 1_{𝒢ᶜ}] ≤ 𝗋(μ) F bad` for `μ ∈ [0, F]` (planar pair) and
`𝔼[J(U,√β e,e/√β;b_L) 1_{𝒢ᶜ}] ≤ F bad` for `β ∈ [1, 1+2F]` (reciprocal pair, divisor `1`), where
`𝒢 = 𝒢(z + Q_{m'})` and `bad = row.badCharge δ D F`. -/
def BadResponseBound (row : Row d) (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (D F : ℝ) : Prop :=
  ∀ m' : ℕ, L + row.g ≤ m' → ∀ z : Homogenization.Vec d,
    ∀ R ∈ descendantsAtDepth (originCube d (m' : ℤ)) row.nu,
    ∀ e : Homogenization.Vec d, vecNormSq e = 1 →
      (∀ μ ∈ Set.Icc (0 : ℝ) F,
        ∫⁻ ω in (goodEvent row M L z m')ᶜ,
            ENNReal.ofReal (frozenJ M L (cellAt z R) ((1 + μ) • e) e ω) ∂M.P.toMeasure ≤
          ENNReal.ofReal (rMatch μ * F * row.badCharge M.delta D F)) ∧
      (∀ β ∈ Set.Icc (1 : ℝ) (1 + 2 * F),
        ∫⁻ ω in (goodEvent row M L z m')ᶜ,
            ENNReal.ofReal (frozenJ M L (cellAt z R) (Real.sqrt β • e) ((Real.sqrt β)⁻¹ • e) ω)
              ∂M.P.toMeasure ≤
          ENNReal.ofReal (F * row.badCharge M.delta D F))

/-- **The normalized per-scale inequality** (L6) at the observation scale `m'`:
`(1-τ_abs)f_{m'} ≤ A√(𝗊(f_{m'})f_{m'}) ∑_{k=1}^{m'-L} b_k√(y_k/R)√(f_{m'-k}-f_{m'})
 + (A_v√f_{m'}/√𝗋(f_{m'})) ∑_{k=0}^{m'-L} b_k√V_{m'-k} + B𝗊(f_{m'})(f_{m'-ν}-f_{m'}) + F·bd`,
with `A = row.coefA F`, `A_v = row.coefAv`, `B = row.coefB F`, `b_k = row.haarB k`, `y_k = row.yk k`. -/
def PerScaleIneq (row : Row d) (f V : ℕ → ℝ) (L : ℕ) (F bd : ℝ) (m' : ℕ) : Prop :=
  (1 - row.tauAbs) * f m' ≤
    row.coefA F * Real.sqrt (qPair d (f m') * f m') *
        ∑ k ∈ Finset.Icc 1 (m' - L),
          row.haarB k * Real.sqrt (row.yk k / (row.R : ℝ)) * Real.sqrt (f (m' - k) - f m') +
      row.coefAv * Real.sqrt (f m') / Real.sqrt (rPair d (f m')) *
        ∑ k ∈ Finset.range (m' - L + 1), row.haarB k * Real.sqrt (V (m' - k)) +
      row.coefB F * qPair d (f m') * (f (m' - row.nu) - f m') + F * bd

end GMCExplicitDelta.Assembly
