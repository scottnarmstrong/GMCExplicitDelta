module

public import GMCExplicitDelta.Localization.HaarDefs
public import GMCExplicitDelta.Proofs.ProjPoincare.Main
public import GMCExplicitDelta.Proofs.PlanarBlock.PlanarFirstBlock

/-!
# Intermediate statements: projected triadic Poincaré (H4) and the planar first Haar block (H6)

Intermediate statements of the proof, each proved in `GMCExplicitDelta/Proofs/`, consumed by the
H5/H6 assembly of `neumann_block_bound` (`Proofs/LocHaar*.lean`). Volume-normalized norms on a
triadic cube (`Haar.energy`, `vecEnergy`), side `ℓ = cubeScaleFactor`.

* `projected_poincare` — H4: for a `C¹` function `v` (partial derivatives `g i`
  along the coordinate lines), `‖(𝒫 - ℳ)v‖² ≤ (5/54) ℓ² ∑ᵢ ‖∂ᵢv‖²` on one cube `U`, where
  `(𝒫 - ℳ)v = cubeIncrement U 1 v` (child averages minus the mean).
* `planar_first_block` — H6: in `d = 2`, the Neumann primitive `w` of `D₁𝐅`
  satisfies `‖w‖² ≤ (1/(5π²) + 243/(10π⁶)) ℓ² ‖D₁𝐅‖²`.

Available tools (all in `GMCExplicitDelta/Haar/`): `NeumannSpectral.neumann_coeff_identity`
(`λ_p c_p(w) = -∑_j (π p_j/ℓ) s_{j,p}(G)` for a Neumann primitive, cosine modes `cubeCos`, mixed modes
`cubeSin`), `PoincareTorus` (cosine Parseval `Torus.hasSum_sq_boxCoeff_cos`, mixed Bessel
`Torus.tsum_sq_boxCoeff_le`), `PoincareCell` (`boxMeasure_eq_normalizedCubeMeasure`,
`energy_eq_integral_sq`, `cube_poincare`), `TriadicProjection` (projections/increments).
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta.Localization

variable {d : ℕ}

/-- **H4 (projected triadic Poincaré inequality, constant `5/54`).** On a triadic cube `U` of side
`ℓ`, let `v` be continuous with continuous partial derivatives `g i` along the coordinate lines.
Then `‖(𝒫 - ℳ)v‖² ≤ (5/54)ℓ² ∑ᵢ ‖g i‖²` (normalized norms on `U`), where `𝒫` averages on the `3^d`
children and `ℳ` is the mean (`cubeIncrement U 1`). Proof (step H4): one dimension on thirds
via the primitive `Φ` of a mean-zero step function (`‖Φ‖² ≤ (5/54)ℓ²‖F‖²`, modes `(-1,0,1)`,
`(1,-2,1)`), then Efron–Stein over the child digits (`Homogenization.efronStein_pi`) and slicing
along each coordinate. -/
theorem projected_poincare (hd : 1 ≤ d) (U : Homogenization.TriadicCube d)
    {v : Homogenization.Vec d → ℝ} {g : Fin d → Homogenization.Vec d → ℝ}
    (hv : Continuous v) (hg : ∀ i, Continuous (g i))
    (hder : ∀ (i : Fin d) (x : Homogenization.Vec d),
      HasDerivAt (fun t => v (Function.update x i t)) (g i x) (x i)) :
    Haar.energy U (cubeIncrement U 1 v) ≤
      5 / 54 * cubeScaleFactor U ^ 2 * ∑ i, Haar.energy U (g i) :=
  projected_poincare_proof hd U hv hg hder

/-- **H6 (planar first Haar block).** In `d = 2`, on a triadic cube `Q` of side `ℓ`, the Neumann
primitive `w = T D₁𝐅` of the first Haar block of `𝐅 ∈ L²(Q; ℝ²)` satisfies
`‖w‖² ≤ (1/(5π²) + 243/(10π⁶)) ℓ² ‖D₁𝐅‖²`. Proof (step H6): split `𝐆 = D₁𝐅` (a mean-zero
step field on the nine children) into its axis part (fiber averages; exact constant `1/54` via the
one-dimensional primitive, `1/54 ≤ 1/(5π²)`) and its mixed part (only modes `p₁p₂ ≠ 0`; eigenvalue gap
`2π²` vs `5π²` and the nine-cell bound `s_{j,(±1,±1)}² ≤ (81/(4π⁴))‖𝐆^mix_j‖²`). -/
theorem planar_first_block (Q : Homogenization.TriadicCube 2)
    (F : Homogenization.Vec 2 → Homogenization.Vec 2)
    (hF : ∀ i, MeasureTheory.MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (w : H1Function (openCubeSet Q))
    (hw : IsNeumannPrimitive Q (vecIncrement Q 1 F) w) :
    Haar.energy Q w.toFun ≤
      (1 / (5 * Real.pi ^ 2) + 243 / (10 * Real.pi ^ 6)) * cubeScaleFactor Q ^ 2 *
        vecEnergy Q (vecIncrement Q 1 F) :=
  planar_first_block_proof Q F hF w hw

end GMCExplicitDelta.Localization
