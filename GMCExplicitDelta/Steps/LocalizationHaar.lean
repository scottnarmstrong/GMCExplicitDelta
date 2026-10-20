module

public import GMCExplicitDelta.Localization.HaarDefs
public import GMCExplicitDelta.Proofs.HaarBlocks.CellPoincare
public import GMCExplicitDelta.Proofs.Multiplier.Final
public import GMCExplicitDelta.Proofs.HaarMode.Haar
public import GMCExplicitDelta.Proofs.HaarBlocks.NeumannBlock
public import GMCExplicitDelta.Proofs.HaarMode.Neumann
public import GMCExplicitDelta.Localization.HaarMinkowski
public import GMCExplicitDelta.Localization.HaarComplete

/-!
# Intermediate statements: the Haar/Neumann analysis with explicit constants (H1, H2, H5–H10)

Intermediate statements of the proof, each proved in `GMCExplicitDelta/Proofs/`. Generic statements
on a triadic cube `Q` (for the cutoff-dependent ones, `Q_n = originCube d n`, side `3^n`), in the
vocabulary of `Localization/HaarDefs.lean`. Together they give H11 (`loc_H11`, proved in
`Localization/H11.lean`): with `𝐅 = ∇u`, `u - ū = (a·x - avg) + ∑_{k=1}^N T D_k𝐅 + r_N`, where
`a = E_0𝐅`, `T D_k𝐅` are Neumann primitives (H2), and the remainder `r_N` is the Neumann primitive of
`𝐅 - E_N𝐅`; then H10, H9 + H5/H6, H9 + H8 and Minkowski bound `P_s((u - ū)𝐠)`.

* `neumann_exists` — H2: every `L²` field has a Neumann primitive.
* `cell_poincare` — H8: `‖(I - E_j)h‖² ≤ 9^{-j}(ℓ/π)²‖∇h‖²` on a cube of side `ℓ`.
* `neumann_block_bound` — H5 (constant `5/54`) and H6 (planar first block): for `k ≥ 1`,
  `‖T D_k𝐅‖² ≤ (𝖫_k/κ_ω²) ℓ² ‖D_k𝐅‖²`.
* `haar_multiplier` — H9 (with H7, H8, H1(c)): `P_s((w-w̄)𝐠)² ≤ 𝖻(Λ)² m²` when
  `‖w - w̄‖² ≤ (Λ/κ_ω²)ℓ²m²` and `‖∇w‖² ≤ m²`.
* `haar_constant_mode` — H10: `P_s((a·x - avg)𝐠)² ≤ b_0²|a|²`.
* `haarPrimal_add_le` — H1 (Minkowski for `P_s`).
* `energy_sub_projection_tendsto` — H1 (Haar completeness): `‖f - E_N f‖ → 0` in `L²`.
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta.Localization

open Assembly Contract

variable {d : ℕ}

/-- **H2 (Neumann primitive, existence).** Every field `G ∈ L²(Q; ℝ^d)` has a Neumann primitive:
a mean-zero `w ∈ H¹(Q)` with `⨍∇w·∇φ = ⨍G·∇φ` for all `φ ∈ H¹(Q)` (the `L²` projection of `G` on
gradients; Lax–Milgram on mean-zero `H¹`, or the Hodge decomposition of CoarseGraining). -/
theorem neumann_exists (Q : Homogenization.TriadicCube d)
    (G : Homogenization.Vec d → Homogenization.Vec d)
    (hG : ∀ i, MeasureTheory.MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q)) :
    ∃ w : H1Function (openCubeSet Q), IsNeumannPrimitive Q G w :=
  neumann_exists_proof Q G hG

/-- **H8 (cell Poincaré inequality, sharp constant).** On a cube of side `ℓ`, for `h ∈ H¹` and every
depth `j`: `‖h - E_j h‖² ≤ 9^{-j}(ℓ/π)²‖∇h‖²` (first nonzero Neumann eigenvalue `π²/ℓ²` of each
depth-`j` cell; e.g. Efron–Stein tensorization of the one-dimensional Wirtinger inequality). -/
theorem cell_poincare (Q : Homogenization.TriadicCube d) (j : ℕ)
    (h : H1Function (openCubeSet Q)) :
    Haar.energy Q (fun x => h.toFun x - cubeProjection Q j h.toFun x) ≤
      cubeScaleFactor Q ^ 2 / (9 ^ j * Real.pi ^ 2) * vecEnergy Q h.grad :=
  cell_poincare_proof Q j h

/-- **H5 + H6 (primitive on Haar blocks).** For `k ≥ 1`, the Neumann primitive `w = T D_k𝐅` of the
`k`-th Haar block of `𝐅 ∈ L²(Q_n)` satisfies `‖w‖² ≤ (𝖫_k/κ_ω²)(3^n)²‖D_k𝐅‖²`: for `d ≥ 3` (and `d = 2`,
`k ≥ 2`) this is H5, `𝖫_k/κ_ω² = (5/54)9^{1-k}` (H3 + H4 by duality); for `d = 2`, `k = 1` it is H6,
`𝖫_1/π² = 1/(5π²) + 243/(10π⁶)`. -/
theorem neumann_block_bound (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ))
    (hO : row.Obligations) (n k : ℕ) (hk : 1 ≤ k)
    (F : Homogenization.Vec d → Homogenization.Vec d)
    (hF : ∀ i, MeasureTheory.MemLp (fun x => F x i) 2 (normalizedCubeMeasure (originCube d (n : ℤ))))
    (w : H1Function (openCubeSet (originCube d (n : ℤ))))
    (hw : IsNeumannPrimitive (originCube d (n : ℤ)) (vecIncrement (originCube d (n : ℤ)) k F) w) :
    Haar.energy (originCube d (n : ℤ)) w.toFun ≤
      row.haarL k / row.kappaOmega ^ 2 * ((3 : ℝ) ^ n) ^ 2 *
        vecEnergy (originCube d (n : ℤ)) (vecIncrement (originCube d (n : ℤ)) k F) :=
  neumann_block_bound_proof row hd hO n k hk F hF w hw

/-- **H9 (multiplier coefficients, with H7, H8 and H1(c)).** If `w ∈ H¹(Q_n)` has
`‖w - w̄‖² ≤ (Λ/κ_ω²)(3^n)²m²` and `‖∇w‖² ≤ m²`, then `P_s((w - w̄)𝐠)² ≤ 𝖻(Λ)²m²`, where
`𝖻(Λ)² = Λ + (q_s-1)∑_j q_s^j min{Λ, 9^{-j}η_ω(1+dΛ)}` and `𝐠` is the scaled cutoff gradient
(`‖(w-w̄)𝐠‖² ≤ Λm²` from `|𝐠| ≤ κ_ω3^{-n}`; `‖∇((w-w̄)𝐠)‖² ≤ κ_ω²3^{-2n}(1+dΛ)m²` from H7; H8;
H1(c)). -/
theorem haar_multiplier (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (n : ℕ) (w : H1Function (openCubeSet (originCube d (n : ℤ)))) {Λ m : ℝ} (hΛ : 0 ≤ Λ)
    (hm : 0 ≤ m)
    (hw : Haar.energy (originCube d (n : ℤ))
        (fun x => w.toFun x - cubeAverage (originCube d (n : ℤ)) w.toFun) ≤
      Λ / row.kappaOmega ^ 2 * ((3 : ℝ) ^ n) ^ 2 * m ^ 2)
    (hgw : vecEnergy (originCube d (n : ℤ)) w.grad ≤ m ^ 2) :
    haarPrimal (originCube d (n : ℤ)) row.qs (fun x =>
        (w.toFun x - cubeAverage (originCube d (n : ℤ)) w.toFun) • cubeCutoffGrad row n x) ≤
      ENNReal.ofReal (multSq row Λ * m ^ 2) :=
  haar_multiplier_proof row hd hO n w hΛ hm hw hgw

/-- **H10 (exact constant mode).** For every constant vector `a`:
`P_s((a·x - ⨍a·x)𝐠)² ≤ b_0²|a|²`, `b_0 = row.haarB 0` (the integrals `𝖫_∘, 𝖱_∘, 𝖧_∘` of H10; the
one-dimensional integrals are `Haar.cutoff_integrals_row`). -/
theorem haar_constant_mode (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ))
    (hO : row.Obligations) (n : ℕ) (a : Homogenization.Vec d) :
    haarPrimal (originCube d (n : ℤ)) row.qs (fun x =>
        (vecDot a x - cubeAverage (originCube d (n : ℤ)) (fun y => vecDot a y)) •
          cubeCutoffGrad row n x) ≤
      ENNReal.ofReal (row.haarB 0 ^ 2 * vecNormSq a) :=
  haar_constant_mode_proof row hd hO n a

/-- **H1 (Minkowski for `P_s`).** For `L²` fields, `P_s(h₁ + h₂) ≤ P_s(h₁) + P_s(h₂)`, in the form
`P_s(h_i)² ≤ c_i² ⇒ P_s(h₁ + h₂)² ≤ (c₁ + c₂)²`. -/
theorem haarPrimal_add_le (Q : Homogenization.TriadicCube d) {q : ℝ} (hq : 0 < q)
    {h₁ h₂ : Homogenization.Vec d → Homogenization.Vec d}
    (hh₁ : ∀ i, MeasureTheory.MemLp (fun x => h₁ x i) 2 (normalizedCubeMeasure Q))
    (hh₂ : ∀ i, MeasureTheory.MemLp (fun x => h₂ x i) 2 (normalizedCubeMeasure Q))
    {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (h₁le : haarPrimal Q q h₁ ≤ ENNReal.ofReal (c₁ ^ 2))
    (h₂le : haarPrimal Q q h₂ ≤ ENNReal.ofReal (c₂ ^ 2)) :
    haarPrimal Q q (h₁ + h₂) ≤ ENNReal.ofReal ((c₁ + c₂) ^ 2) :=
  haarPrimal_add_le_proof Q hq hh₁ hh₂ hc₁ hc₂ h₁le h₂le

/-- **H1 (completeness of the triadic Haar system in `L²`).** For `f ∈ L²(Q)`, `‖f - E_N f‖² → 0`. -/
theorem energy_sub_projection_tendsto (Q : Homogenization.TriadicCube d)
    {f : Homogenization.Vec d → ℝ} (hf : MeasureTheory.MemLp f 2 (normalizedCubeMeasure Q)) :
    Filter.Tendsto (fun N => Haar.energy Q (fun x => f x - cubeProjection Q N f x))
      Filter.atTop (nhds 0) :=
  energy_sub_projection_tendsto_proof Q hf

end GMCExplicitDelta.Localization
