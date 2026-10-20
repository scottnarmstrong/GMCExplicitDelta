module

public import GMCExplicitDelta.HistoryLane.Defs
public import GMCExplicitDelta.Proofs.FineSensitivity.RatioNorms
public import GMCExplicitDelta.Proofs.GridMax.Final
public import GMCExplicitDelta.Proofs.FineSensitivity.FineSensitivity

/-!
# Intermediate statements: fine source history and the subunit grid bound (G3, G4, G6)

Intermediate statements of the proof, each proved in `GMCExplicitDelta/Proofs/`. They are the
model-level inputs of the assembly of G7 (`excess_bound`, `HistoryLane/Excess.lean`); the
deterministic and numerical parts of G5, G6 and G7 are proved in `HistoryLane/`.

* `fineSensitivity` — G3: weighted sensitivity `‖J^max(U;b_L)‖_{32}` of a scale-`k` cell in terms of
  `‖J^max(U;b_k)‖_{32}` and the one-point norms `F_r, G_r` of `ρ = b_L/b_k`.
* `fineRatioNorms` — G4: the shifted one-point norms `F_r, G_r` (S8, N2).
* `gridMax_norm_le` — G6 (first part): `‖sup_{V ⊆ U'} J^max(V;b_L)‖_{32} ≤ B_L`.
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta.Assembly

open Contract

variable {d : ℕ}

/-- **G3 (weighted sensitivity for transferred fine scales).** Let `0 ≤ k < L`, `U = z + Q_k`,
`ρ = b_L/b_k` (`cutoffRatio`). If `‖(ρ(x)-1)²‖_{32} ≤ F_r` and `‖ρ(x)+ρ(x)⁻¹-2‖_{32} ≤ G_r` for all
`x`, then for every `η ∈ (0,1]`,
`‖J^max(U;b_L)‖_{32} ≤ (1+η)‖J^max(U;b_k)‖_{32} + β_d(1+‖J^max(U;b_k)‖_{32})[F_r/(2η) + G_r]`.
(G3: C12 on `U` with old coefficient `b_k` and new `b_kρ`, Young, conditioning on
`g_0,…,g_k` and independence of `ρ` (N2), Minkowski's integral inequality, then C13.) -/
theorem fineSensitivity (hd : d ∈ ({2, 3, 4} : Finset ℕ))
    (M : SubdiffusiveProcess.Model.GMCModel d) {k L : ℕ} (hkL : k < L) (z : Homogenization.Vec d)
    {η Fr Gr : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hFr : 0 ≤ Fr) (hGr : 0 ≤ Gr)
    (hF : ∀ x : Homogenization.Vec d,
      paperENNRealLpNorm M.P.toMeasure 32
          (fun ω => ENNReal.ofReal ((cutoffRatio M k L ω x - 1) ^ 2)) ≤ ENNReal.ofReal Fr)
    (hG : ∀ x : Homogenization.Vec d,
      paperENNRealLpNorm M.P.toMeasure 32
          (fun ω => ENNReal.ofReal (cutoffRatio M k L ω x + (cutoffRatio M k L ω x)⁻¹ - 2)) ≤
        ENNReal.ofReal Gr) :
    paperENNRealLpNorm M.P.toMeasure 32 (normalizedDefect M L (cubeAt z k)) ≤
      (1 + ENNReal.ofReal η) *
          paperENNRealLpNorm M.P.toMeasure 32 (normalizedDefect M k (cubeAt z k)) +
        ENNReal.ofReal (sphereFactor d) *
          (1 + paperENNRealLpNorm M.P.toMeasure 32 (normalizedDefect M k (cubeAt z k))) *
          ENNReal.ofReal (Fr / (2 * η) + Gr) :=
  fineSensitivity_proof hd M hkL z hη hη1 hFr hGr hF hG

/-- **G4 (shifted one-point norms).** For `0 ≤ k < L`, `r = L - k` and every `x`, with `δ = M.delta`:
`‖(ρ(x)-1)²‖_{32} ≤ e^{(128𝖺+2κ_h)rδ²}[C_h rδ² + A_F r²]` and
`‖ρ(x)+ρ(x)⁻¹-2‖_{32} ≤ e^{(32𝖺+κ_h)rδ²}[C_h rδ² + A_G r²]` (S8 for the unshifted layers, N2 for
the drift `|c| ≤ κ_h r δ²`; `κ_h = 0` in `d = 2`). -/
theorem fineRatioNorms (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (M : SubdiffusiveProcess.Model.GMCModel d) {k L : ℕ} (hkL : k < L) (x : Homogenization.Vec d) :
    paperENNRealLpNorm M.P.toMeasure 32
        (fun ω => ENNReal.ofReal ((cutoffRatio M k L ω x - 1) ^ 2)) ≤
        ENNReal.ofReal (fineF d M.delta ((L - k : ℕ) : ℝ)) ∧
      paperENNRealLpNorm M.P.toMeasure 32
          (fun ω => ENNReal.ofReal (cutoffRatio M k L ω x + (cutoffRatio M k L ω x)⁻¹ - 2)) ≤
        ENNReal.ofReal (fineG d M.delta ((L - k : ℕ) : ℝ)) :=
  fineRatioNorms_proof row hd hO M hkL x

/-- **G6 (whole-sum grid bound, first part).** For every unit triadic cube `U'` (scale `0`), every
translation `z` and `L ≥ 0`: `‖sup_{V ⊆ U'} J^max(V;b_L)‖_{32} ≤ B_L` (covering by the `N_g` grid
points, S1(c); S8 and S10 for the grid maxima and the remainder; C4 and N2 for the trial). -/
theorem gridMax_norm_le (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (z : Homogenization.Vec d)
    (R : Homogenization.TriadicCube d) (hR : R.scale = 0) :
    paperENNRealLpNorm M.P.toMeasure 32 (subcellMax M L z R) ≤
      ENNReal.ofReal (gridBound row M.delta L) :=
  gridMax_norm_le_proof row hd hO M L z R hR

end GMCExplicitDelta.Assembly
