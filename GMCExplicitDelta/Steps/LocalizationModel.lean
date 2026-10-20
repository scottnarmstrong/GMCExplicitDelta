module

public import GMCExplicitDelta.Localization.Subadd
public import GMCExplicitDelta.Proofs.AnnealedMeans.All
public import GMCExplicitDelta.Proofs.CellMoments.All

/-!
# Intermediate statements: model facts used by the localization lane (C2, C4, C8, C9, C10, integrability)

Intermediate statements of the proof, each proved in `GMCExplicitDelta/Proofs/`. All statements are
about the frozen coefficient `b_L` of `Assembly/ModelFrozen.lean` on the cube `Q_n = cubeAt 0 n` and
its triadic cells `cellAt 0 R`.

* `frozenJ_nonneg` — C4: `J(U, p, q; b_L) ≥ 0`.
* `frozenJ_le_cellJ` — C2: `J(Q_n, p, q; b_L) ≤ avg_{R depth k} J(R, p, q; b_L)`.
* `integrable_cell` — integrability of `J(R, p, q; b_L)` and of `|-p + Y_R q - c|²` for cells of scale
  `≥ L`, from `𝖯(L)`.
* `integral_frozenJ_cell` — C8 with stationarity: `𝔼J(R, p, q; b_L) = ½α_n|p|² + ½β_n|q|² - p·q` for a
  cell of scale `n ≥ L`.
* `integral_cellRes_le` — C8 for second moments: `𝔼|(Y_R - β_n)q|² ≤ varFactor d · |q|² · V_n`.
* `alphaBeta_ge_one_antitone` — C9: `α_n, β_n ≥ 1` and nonincreasing on `n ≥ L`.
* `alpha_eq_beta_planar` — C10: `α_n = β_n` in `d = 2`.
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta.Localization

open Assembly Contract

variable {d : ℕ}

/-- **C4.** `J(U, p, q; b_L) ≥ 0` for every domain, pair and sample. -/
theorem frozenJ_nonneg (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (p q : Homogenization.Vec d) (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    0 ≤ frozenJ M L U p q ω :=
  Ch02.responseJ_nonneg _ _ _ _

/-- **C2 (subadditivity).** `J(Q_n, p, q; b_L) ≤ avg_{R depth k of Q_n} J(R, p, q; b_L)`, pointwise. -/
theorem frozenJ_le_cellJ (M : SubdiffusiveProcess.Model.GMCModel d) (L n k : ℕ)
    (p q : Homogenization.Vec d) (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    frozenJ M L (cubeAt 0 n) p q ω ≤ cellJ M L n k p q ω :=
  frozenJ_le_descAvg M L (originCube d (n : ℤ)) k p q ω

/-- **Integrability on cells of scale `≥ L`.** Under `𝖯(L; D, F)`, for every triadic cube `R` of scale
`≥ L`, `ω ↦ J(R, p, q; b_L)` and `ω ↦ |-p + Y_R q - c|²` are integrable. -/
theorem integrable_cell (M : SubdiffusiveProcess.Model.GMCModel d) {D F : ℝ} (L : ℕ)
    (hP : InductionP M L D F) (R : Homogenization.TriadicCube d) (hR : (L : ℤ) ≤ R.scale)
    (p q c : Homogenization.Vec d) :
    MeasureTheory.Integrable (frozenJ M L (cellAt 0 R) p q) M.P.toMeasure ∧
      MeasureTheory.Integrable
        (fun ω => vecNormSq (-p + (frozenY M L (cellAt 0 R) ω).mulVec q - c)) M.P.toMeasure :=
  integrable_cell_proof M L hP R hR p q c

/-- **C8 with stationarity.** For a triadic cube `R` of scale `n ≥ L` (under `𝖯(L; D, F)`),
`𝔼J(R, p, q; b_L) = ½α_n|p|² + ½β_n|q|² - p·q`. -/
theorem integral_frozenJ_cell (M : SubdiffusiveProcess.Model.GMCModel d) {D F : ℝ} (L : ℕ)
    (hP : InductionP M L D F) (n : ℕ) (hn : L ≤ n) (R : Homogenization.TriadicCube d)
    (hR : R.scale = (n : ℤ)) (p q : Homogenization.Vec d) :
    ∫ ω, frozenJ M L (cellAt 0 R) p q ω ∂M.P.toMeasure = meanJ M L n p q :=
  integral_frozenJ_cell_proof M L hP n hn R hR p q

/-- **C8 for second moments.** For a triadic cube `R` of scale `n ≥ L` (under `𝖯(L; D, F)`),
`𝔼|Y_R q - β_n q|² ≤ varFactor d · |q|² · V_n` (equality `𝔼|(Y_R - β_n)q|² = |q|²d⁻¹𝔼‖Y_n - β_n‖_F²`
by isotropy, then the definition of `V_n`). -/
theorem integral_cellRes_le (M : SubdiffusiveProcess.Model.GMCModel d) {D F : ℝ} (L : ℕ)
    (hP : InductionP M L D F) (n : ℕ) (hn : L ≤ n) (R : Homogenization.TriadicCube d)
    (hR : R.scale = (n : ℤ)) (q : Homogenization.Vec d) :
    ∫ ω, vecNormSq ((frozenY M L (cellAt 0 R) ω).mulVec q - betaMean M L n • q) ∂M.P.toMeasure ≤
      varFactor d * vecNormSq q * varV M L n :=
  integral_cellRes_le_proof M L hP n hn R hR q

/-- **C9.** Under `𝖯(L; D, F)`: `α_n ≥ 1`, `β_n ≥ 1` for `n ≥ L`, and both are nonincreasing on
`[L, ∞)`. -/
theorem alphaBeta_ge_one_antitone (M : SubdiffusiveProcess.Model.GMCModel d) {D F : ℝ} (L : ℕ)
    (hP : InductionP M L D F) :
    (∀ n, L ≤ n → 1 ≤ alphaMean M L n ∧ 1 ≤ betaMean M L n) ∧
      ∀ a b, L ≤ a → a ≤ b → alphaMean M L b ≤ alphaMean M L a ∧ betaMean M L b ≤ betaMean M L a :=
  alphaBeta_ge_one_antitone_proof M L hP

/-- **C10 (planar duality).** In `d = 2`, under `𝖯(L; D, F)`, `α_n = β_n` for `n ≥ L`. -/
theorem alpha_eq_beta_planar (M : SubdiffusiveProcess.Model.GMCModel d) (hd : d = 2) {D F : ℝ}
    (L : ℕ) (hP : InductionP M L D F) (n : ℕ) (hn : L ≤ n) :
    alphaMean M L n = betaMean M L n :=
  alpha_eq_beta_planar_proof M hd L hP n hn

end GMCExplicitDelta.Localization
