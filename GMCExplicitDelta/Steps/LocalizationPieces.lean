module

public import GMCExplicitDelta.Localization.H11
public import GMCExplicitDelta.Proofs.LocWeights.Weights
public import GMCExplicitDelta.Localization.Bridge
public import GMCExplicitDelta.Localization.GoodEvent
public import GMCExplicitDelta.Proofs.WeightedLocalization.Main
public import GMCExplicitDelta.Proofs.GradPieces.Tail
public import GMCExplicitDelta.Proofs.EnergyTest.L1
public import GMCExplicitDelta.Proofs.FluxBound.G1b

/-!
# Intermediate statements: the deterministic pieces of the pointwise localized inequality

Intermediate statements of the proof, each proved in `GMCExplicitDelta/Proofs/`. Each statement is
about one sample `ω` (deterministic), the frozen coefficient `b_L(ω) = a_L(ω)/ā_L`, the cube
`Q_n = originCube d n` (Chapter 2 domain `cubeAt 0 n`), its depth-`k` cells `cellAt 0 R`, and the
frozen maximizer `v = frozenH1 M L (cubeAt 0 n) p q ω` (`Localization/CoreDefs.lean`). Together with
`frozenJ_nonneg`, `frozenJ_le_cellJ` and the Haar tail bound H12 they give `loc_pointwise`
(`Localization/Core.lean`).

* `goodEvent_cell_bound` — G1(a): on `𝒢(Q_n)`, `J^max(R; b_L) ≤ θ_R q_s^k` for every depth-`k` cell.
* `frozenJ_eq_energy` — C1(b) with C3: `J(U,p,q;b_L) = ½⨍_U ∇v·b_L∇v`.
* `loc_L3` — L3 with Young's inequality, for any weights below a function `φ` on the cells.
* `loc_L1` — L1: `𝒲² ≤ K_s(b_L∇v)² P_s((v - v̄)𝐠)²` (harmonic energy test + Haar duality).
* `loc_G1flux` — G1(c): on `𝒢(Q_n)`, `K_s(b_L∇v)² ≤ R⨍∇v·b_L∇v = 2R J(Q_n,p,q;b_L)`.
* `loc_H11` — H11: `P_s((u - ū)𝐠) ≤ ∑_k b_k ‖D_k∇u‖` for every `u ∈ H¹(Q_n)` (ASSEMBLED:
  `loc_H11_assembled`, `Localization/H11.lean`, from the H-level targets of
  `Steps/LocalizationHaar.lean`).
* `loc_L2_mean`, `loc_L2_drop`, `loc_L2_tail` — L2 (deterministic part): the Haar blocks of `∇v`.
* `loc_weights` — H7 + H13: weights `w_R ≤ min_R φ` on the depth-`ν` cells with average `≥ c_ν`.
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta.Localization

open Assembly Contract

variable {d : ℕ}

/-- **G1(a) (descendant bound on the good event).** If `T_{2s}(Q_n) ≤ θ_R` then every depth-`k` cell
`R` of `Q_n` has `J^max(R; b_L) ≤ θ_R q_s^k` (because `e_j` is nondecreasing in `j`, C11(b)). -/
theorem goodEvent_cell_bound (row : Row d) (hO : row.Obligations)
    (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) (hω : ω ∈ goodEvent row M L 0 n) (k : ℕ)
    (R : Homogenization.TriadicCube d) (hR : R ∈ descendantsAtDepth (originCube d (n : ℤ)) k) :
    normalizedDefect M L (cellAt 0 R) ω ≤ ENNReal.ofReal (row.thetaR * row.qs ^ k) :=
  goodEvent_cell_bound_proof row hO M L n ω hω k R hR

/-- **Energy identity of the frozen maximizer** (C1(b), C3): `J(U, p, q; b_L) = ½⨍_U ∇v·b_L∇v`. -/
theorem frozenJ_eq_energy (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (p q : Homogenization.Vec d) (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    frozenJ M L U p q ω = (1 / 2) * Ch02.average U fun x =>
      vecDot ((frozenH1 M L U p q ω).grad x) (frozenFlux M L U p q ω x) :=
  frozenJ_eq_energy_proof M L U p q ω

/-- **L3 (weighted localization) with Young's inequality.** For weights `0 ≤ w_R ≤ 1` on the depth-`k`
cells of `Q_n` with `w_R ≤ φ` on each cell, and `ε > 0`:
`avg_R w_R J(R,p,q) ≤ (1+ε)/2 · ⨍_{Q_n} φ ∇v·b_L∇v + (1+ε⁻¹)(avg_R J(R,p,q) - J(Q_n,p,q))`. -/
theorem loc_L3 (M : SubdiffusiveProcess.Model.GMCModel d) (L n k : ℕ)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) (p q : Homogenization.Vec d) {ε : ℝ}
    (hε : 0 < ε) (φ : Homogenization.Vec d → ℝ) (hφm : Measurable φ)
    (hφ1 : ∀ x ∈ cubeSet (originCube d (n : ℤ)), φ x ≤ 1) (w : Homogenization.TriadicCube d → ℝ)
    (hw : ∀ R, 0 ≤ w R ∧ w R ≤ 1)
    (hwφ : ∀ R ∈ descendantsAtDepth (originCube d (n : ℤ)) k, ∀ x ∈ cubeSet R, w R ≤ φ x) :
    cellJw M L n k w p q ω ≤
      (1 + ε) / 2 * cubeAverage (originCube d (n : ℤ)) (fun x =>
          φ x * vecDot ((frozenH1 M L (cubeAt 0 n) p q ω).grad x)
            (frozenFlux M L (cubeAt 0 n) p q ω x)) +
        (1 + ε⁻¹) * (cellJ M L n k p q ω - frozenJ M L (cubeAt 0 n) p q ω) :=
  loc_L3_proof M L ω n k p q hε φ hφm hφ1 w hw hwφ

/-- **L1 (harmonic energy test).** `𝒲 = ⨍φ∇v·b_L∇v = -⨍(v - v̄)𝐠·b_L∇v` (test `φ(v - v̄) ∈ H¹₀`), hence by
Haar duality (H1(a)) `𝒲² ≤ K_s(b_L∇v)² · P_s((v - v̄)𝐠)²`. -/
theorem loc_L1 (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) (p q : Homogenization.Vec d) :
    ENNReal.ofReal (locEnergy row M L n p q ω) ^ 2 ≤
      haarDual (originCube d (n : ℤ)) row.qs (frozenFlux M L (cubeAt 0 n) p q ω) *
        haarPrimal (originCube d (n : ℤ)) row.qs
          (locTestField row n (frozenH1 M L (cubeAt 0 n) p q ω).toFun) :=
  loc_L1_proof row hd hO M L n ω p q

/-- **G1(c), flux part.** On `𝒢(Q_n)`: `K_s(b_L∇v)² ≤ R ⨍_{Q_n} ∇v·b_L∇v = 2R J(Q_n,p,q;b_L)`
(H1(b), C5 on each cell, C6 and the concavity of `𝗑`: `(1-w)∑_k w^k max_R λ_max(X_R) ≤ R`). -/
theorem loc_G1flux (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) (hω : ω ∈ goodEvent row M L 0 n)
    (p q : Homogenization.Vec d) :
    haarDual (originCube d (n : ℤ)) row.qs (frozenFlux M L (cubeAt 0 n) p q ω) ≤
      ENNReal.ofReal (2 * (row.R : ℝ) * frozenJ M L (cubeAt 0 n) p q ω) :=
  loc_G1flux_proof row hd hO M L n ω hω p q

/-- **H11 (Haar summation of the localized test field).** For every `u ∈ H¹(Q_n)`:
`P_s((u - ū)𝐠) ≤ ∑_{k≥0} b_k ‖D_k∇u‖`, with `b_k = row.haarB k` (H9, H10) and `𝐠 = ∇φ` the scaled
plateau-cosine cutoff. Proof route: H2 (Neumann primitive `T`), `u - ū = ∑_k T D_k∇u`, H9 with
H5/H6 (`‖TD_k𝐅‖ ≤ ℓ_k‖D_k𝐅‖`) for `k ≥ 1` and H10 for `k = 0`. -/
theorem loc_H11 (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations) (n : ℕ)
    (u : H1Function (openCubeSet (originCube d (n : ℤ)))) :
    haarPrimal (originCube d (n : ℤ)) row.qs (locTestField row n u.toFun) ≤
      (tsum fun k : ℕ => ENNReal.ofReal (row.haarB k * incNorm (originCube d (n : ℤ)) k u.grad)) ^ 2 :=
  loc_H11_assembled row hd hO n u

/-- **L2, mean block.** `‖D_0∇v‖² = |⨍_{Q_n}∇v|² = |-p + Y_{Q_n}q|²` (C1(b)). -/
theorem loc_L2_mean (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) (p q : Homogenization.Vec d) :
    incNorm (originCube d (n : ℤ)) 0 (frozenH1 M L (cubeAt 0 n) p q ω).grad ^ 2 =
      vecNormSq (-p + (frozenY M L (cubeAt 0 n) ω).mulVec q) := by
  rw [incNorm_zero_sq]
  congr 1
  funext i
  exact avgVec_frozenGrad M L n p q ω i

/-- **L2, drop blocks** (deterministic part). On `𝒢(Q_n)`, for `k ≥ 1` and every constant `c`:
`‖D_k∇v‖ ≤ √(2y_k(avg_R J(R) - J(Q_n))) + √(avg_R |-p + Y_R q - c|²)` (H1(e) with `c`, then C1(d) and
the gradient part of G1(c) on each depth-`k` cell). -/
theorem loc_L2_drop (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) (hω : ω ∈ goodEvent row M L 0 n)
    (p q c : Homogenization.Vec d) (k : ℕ) (hk : 1 ≤ k) :
    incNorm (originCube d (n : ℤ)) k (frozenH1 M L (cubeAt 0 n) p q ω).grad ≤
      Real.sqrt (2 * row.yk k * (cellJ M L n k p q ω - frozenJ M L (cubeAt 0 n) p q ω)) +
        Real.sqrt (cellRes M L n k p q c ω) :=
  loc_L2_drop_proof row hd hO M L n ω hω p q c k hk

/-- **L2, tail blocks.** On `𝒢(Q_n)`, for `k ≥ 1`: `‖D_k∇v‖² ≤ ‖E_k∇v‖² ≤ y_k ⨍∇v·b_L∇v = 2y_k J(Q_n)`
(C5 on each depth-`k` cell and G1(a), C6). -/
theorem loc_L2_tail (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) (hω : ω ∈ goodEvent row M L 0 n)
    (p q : Homogenization.Vec d) (k : ℕ) (hk : 1 ≤ k) :
    incNorm (originCube d (n : ℤ)) k (frozenH1 M L (cubeAt 0 n) p q ω).grad ^ 2 ≤
      2 * row.yk k * frozenJ M L (cubeAt 0 n) p q ω :=
  loc_L2_tail_proof row hd hO M L n ω hω p q k hk

/-- **H7 + H13 (localization weights).** There are weights `0 ≤ w_R ≤ 1` on the depth-`ν` cells of
`Q_n`, below the cutoff on each cell (`w_R` = product of the one-dimensional endpoint minima of the
profile), with average `≥ c_ν` (`Haar.cNu_le_exactLocalizationWeight`). -/
theorem loc_weights (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (n : ℕ) :
    ∃ w : Homogenization.TriadicCube d → ℝ, (∀ R, 0 ≤ w R ∧ w R ≤ 1) ∧
      row.cNu ≤ descendantsAverage (originCube d (n : ℤ)) row.nu w ∧
      ∀ R ∈ descendantsAtDepth (originCube d (n : ℤ)) row.nu, ∀ x ∈ cubeSet R,
        w R ≤ cubeCutoff row n x :=
  loc_weights_proof row hd hO n

end GMCExplicitDelta.Localization
