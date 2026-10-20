module

public import GMCExplicitDelta.Assembly.ModelEvents
public import GMCExplicitDelta.Proofs.Observables.Good
public import GMCExplicitDelta.Proofs.BadResponse.BadResponse
public import GMCExplicitDelta.HistoryLane.Excess

/-!
# Intermediate statements: complete excess, bad probability and bad response (G7, G8, G9)

Intermediate statements of the assembly of `cascade_of_obligations`. Each is proved in
`GMCExplicitDelta/Proofs/`. Model vocabulary: `GMCExplicitDelta.Assembly`
(`Assembly/ModelEvents.lean`). All constants are the contract's, evaluated at the model's disorder
`δ = M.delta` and at the caps `(D, F)` of the induction hypothesis (in the assembly
`(D, F) = (λD_row, λF_row)`, R4).

* `excess_bound` — G7: `‖(T_{2s}(z + Q_{L+t}) - F)_+‖_{32} ≤ e_⋆` for `t ≥ g`.
* `badEvent_prob_le` — G8: `ℙ(𝒢(z + Q_{m'})ᶜ) ≤ (e_⋆/(θ_R - F))^{32}` for `m' ≥ L + g`, from G7.
* `badResponseBound_holds` — G9: `BadResponseBound`, from G8.
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta.Assembly

open Contract

variable {d : ℕ}

/-- **G7 (complete excess, uniform over later targets).** Assume `𝖯(k; D, F)` for all `k ≤ L`
(`0 < F ≤ D`), `z_F < 1` and `𝔲_{12} < 1` at `(δ, D, F)` (the remaining hypothesis `3^{-d/2} < x` of
G7 is the row fact O.avg.4). Then for every `t ≥ g` and `z`,
`‖(T_{2s}(z + Q_{L+t}) - F)_+‖_{32} ≤ e_⋆ = (1-w)Dx^gS_∞ + x^gH`. -/
theorem excess_bound (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (M : SubdiffusiveProcess.Model.GMCModel d) {D F : ℝ} (hD : 0 < D) (hF : 0 < F) (hFD : F ≤ D)
    (L : ℕ) (hP : ∀ k ≤ L, InductionP M k D F) (hzF : row.zF M.delta < 1)
    (hu : frakU d row.historyCutoff D F < 1) :
    ∀ t, row.g ≤ t → ∀ z : Homogenization.Vec d,
      paperENNRealLpNorm M.P.toMeasure 32
          (fun ω => haarStat row M L z (L + t) ω - ENNReal.ofReal F) ≤
        ENNReal.ofReal (row.eStar M.delta D F) :=
  excess_bound_proof row hd hO M hD hF hFD L hP hzF hu

/-- **G8 (probability of the bad event).** Under the conclusion of G7 and `θ_R > F`: for every
`m' ≥ L + g` and `z`, `ℙ(𝒢(z + Q_{m'})ᶜ) ≤ (e_⋆/(θ_R - F))^{32}` (Markov at order 32).
(v2, 2026-10-19: hypothesis `0 ≤ F` added after W1's finding — for `F < 0` the excess
`T - ofReal F` does not control `T - F`.) -/
theorem badEvent_prob_le (row : Row d) (M : SubdiffusiveProcess.Model.GMCModel d) {D F : ℝ}
    (L : ℕ) (hθ : F < row.thetaR) (hF : 0 ≤ F)
    (hG7 : ∀ t, row.g ≤ t → ∀ z : Homogenization.Vec d,
      paperENNRealLpNorm M.P.toMeasure 32
          (fun ω => haarStat row M L z (L + t) ω - ENNReal.ofReal F) ≤
        ENNReal.ofReal (row.eStar M.delta D F)) :
    ∀ m', L + row.g ≤ m' → ∀ z : Homogenization.Vec d,
      M.P.toMeasure (goodEvent row M L z m')ᶜ ≤
        ENNReal.ofReal ((row.eStar M.delta D F / (row.thetaR - F)) ^ 32) :=
  badEvent_prob_le_proof row M L hθ hF hG7

/-- **G9 (bad response of the matched pairs).** Under the hypotheses of G7, `θ_R > F` and the
conclusion of G8, the bad-response bound holds for both matched pairs, every target `z + Q_{m'}`
(`m' ≥ L + g`) and every depth-`ν` cell, with `bad = Φ_{log(1+2F)}(U_{g-ν})/F · (e_⋆/(θ_R-F))^{31}`
(Hölder, C3, C7 and the native cap A6 of the cell). -/
theorem badResponseBound_holds (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ))
    (hO : row.Obligations) (M : SubdiffusiveProcess.Model.GMCModel d) {D F : ℝ} (hD : 0 < D)
    (hF : 0 < F) (hFD : F ≤ D) (L : ℕ) (hP : ∀ k ≤ L, InductionP M k D F)
    (hzF : row.zF M.delta < 1) (hu : frakU d row.historyCutoff D F < 1) (hθ : F < row.thetaR)
    (hG8 : ∀ m', L + row.g ≤ m' → ∀ z : Homogenization.Vec d,
      M.P.toMeasure (goodEvent row M L z m')ᶜ ≤
        ENNReal.ofReal ((row.eStar M.delta D F / (row.thetaR - F)) ^ 32)) :
    BadResponseBound row M L D F :=
  badResponseBound_holds_proof row hd hO M hD hF hFD L hP hzF hu hθ hG8

end GMCExplicitDelta.Assembly
