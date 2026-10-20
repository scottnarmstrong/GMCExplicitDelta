module

public import GMCExplicitDelta.Assembly.ModelEvents
public import Homogenization.Besov.Basic

/-!
# Localization lane: vocabulary of L4–L6

§12. Fix the cutoff `L`, the frozen coefficient `b_L`, an observation scale `n` (called
`m'` in the proof map) and the target cube `Q_n = cubeAt 0 n` (the per-scale inequality only involves
cubes centred at the origin; the depth-`k` cells of `Q_n` are `cellAt 0 R`,
`R ∈ descendantsAtDepth (originCube d n) k`).

Pointwise (per sample `ω`) quantities, all expressed through the model objects `frozenJ`, `frozenY`
of `Assembly/ModelFrozen.lean` (no maximizer, no cutoff):

* `cellJ M L n k p q ω = avg_{R depth k} J(R, p, q; b_L)` (for `k = 0` this is `J(Q_n, p, q; b_L)`);
* `cellRes M L n k p q c ω = avg_{R depth k} |-p + Y_R q - c|²` (the squared norm of the step field
  `𝖦_k` of L2, centred at the constant `c`);
* `cellJw M L n k w p q ω = avg_{R depth k} w_R J(R, p, q; b_L)` (the localized energy `𝒮/2` of L3,
  with deterministic weights `w`);
* `haarSum row M L n K p q c ω = ∑_{k ≤ K} b_k (√(2y_k(J_k - J_0)) + √(cellRes k (c k)))`, the
  Haar-weighted gradient pieces of L2 (the `k = 0` summand is `b_0|-p + Y_{Q_n}q|` when `c 0 = 0`);
* `locBound row J₀ J_ν X = (1+ε)/2 · (√(2RJ₀) X + 2R T_g J₀) + (1+ε⁻¹)(J_ν - J₀)`, the right side of
  the pointwise localized inequality (L1 + L3 + H11 + L2 + the tail of H12).

Annealed quantities: `meanJ M L n p q = ½α_n|p|² + ½β_n|q|² - p·q` (C8: `𝔼J(Q_n,p,q;b_L)`),
`varFactor d` (`1` for `d = 2`, `2` for `d ≥ 3`: `𝔼|(Y_n - β_n)q|² ≤ varFactor d · |q|² · V_n`, C8).
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta.Localization

open Assembly Contract

variable {d : ℕ}

/-- `𝔼J(Q_n, p, q; b_L) = ½α_n|p|² + ½β_n|q|² - p·q` (C8, C1). -/
noncomputable def meanJ (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    (p q : Homogenization.Vec d) : ℝ :=
  (1 / 2) * alphaMean M L n * vecNormSq p + (1 / 2) * betaMean M L n * vecNormSq q - vecDot p q

/-- The variance factor of L5: `𝔼|(Y_n - β_n)q|² ≤ varFactor d · |q|² · V_n`, with `varFactor 2 = 1`
(`V_n = ½𝔼‖Y_n - β_n‖_F²`) and `varFactor d = 2` for `d ≥ 3` (`V_n ≥ (2d)⁻¹𝔼‖Y_n - β_n‖_F²`). -/
noncomputable def varFactor (d : ℕ) : ℝ := if d = 2 then 1 else 2

/-- `J_k(ω) = avg_{R depth k of Q_n} J(R, p, q; b_L)`. -/
noncomputable def cellJ (M : SubdiffusiveProcess.Model.GMCModel d) (L n k : ℕ)
    (p q : Homogenization.Vec d) (ω : SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  descendantsAverage (originCube d (n : ℤ)) k fun R => frozenJ M L (cellAt 0 R) p q ω

/-- `avg_{R depth k of Q_n} |-p + Y_R q - c|²` (the step field `𝖦_k` of L2, centred at `c`). -/
noncomputable def cellRes (M : SubdiffusiveProcess.Model.GMCModel d) (L n k : ℕ)
    (p q c : Homogenization.Vec d) (ω : SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  descendantsAverage (originCube d (n : ℤ)) k fun R =>
    vecNormSq (-p + (frozenY M L (cellAt 0 R) ω).mulVec q - c)

/-- `avg_{R depth k of Q_n} w_R J(R, p, q; b_L)` (L3, `𝒮 = 2·cellJw`). -/
noncomputable def cellJw (M : SubdiffusiveProcess.Model.GMCModel d) (L n k : ℕ)
    (w : Homogenization.TriadicCube d → ℝ) (p q : Homogenization.Vec d)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  descendantsAverage (originCube d (n : ℤ)) k fun R => w R * frozenJ M L (cellAt 0 R) p q ω

/-- The Haar-weighted gradient pieces of L2 up to depth `K`:
`∑_{k ≤ K} b_k (√(2y_k(J_k - J_0)) + √(avg_R |-p + Y_R q - c_k|²))`. -/
noncomputable def haarSum (row : Row d) (M : SubdiffusiveProcess.Model.GMCModel d) (L n K : ℕ)
    (p q : Homogenization.Vec d) (c : ℕ → Homogenization.Vec d)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  ∑ k ∈ Finset.range (K + 1), row.haarB k *
    (Real.sqrt (2 * row.yk k * (cellJ M L n k p q ω - frozenJ M L (cubeAt 0 n) p q ω)) +
      Real.sqrt (cellRes M L n k p q (c k) ω))

/-- The right side of the pointwise localized inequality:
`(1+ε)/2 · (√(2RJ₀) X + 2R T_g J₀) + (1+ε⁻¹)(J_ν - J₀)`. -/
noncomputable def locBound (row : Row d) (J₀ Jν X : ℝ) : ℝ :=
  (1 + (row.epsilon : ℝ)) / 2 *
      (Real.sqrt (2 * (row.R : ℝ) * J₀) * X + 2 * (row.R : ℝ) * row.Tg * J₀) +
    (1 + (row.epsilon : ℝ)⁻¹) * (Jν - J₀)

/-- `A₀ = (1+ε)R/c_ν` (L4). -/
noncomputable def coefA0 (row : Row d) : ℝ := (1 + (row.epsilon : ℝ)) * (row.R : ℝ) / row.cNu

/-- `A_{v0} = (1+ε)√(2R)/(2c_ν)` (L4). -/
noncomputable def coefAv0 (row : Row d) : ℝ :=
  (1 + (row.epsilon : ℝ)) * Real.sqrt (2 * (row.R : ℝ)) / (2 * row.cNu)

/-- `B₀ = (1+ε⁻¹)/c_ν` (L4). -/
noncomputable def coefB0 (row : Row d) : ℝ := (1 + (row.epsilon : ℝ)⁻¹) / row.cNu

end GMCExplicitDelta.Localization
