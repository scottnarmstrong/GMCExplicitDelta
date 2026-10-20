module

public import GMCExplicitDelta.Localization.CoreDefs

/-!
# Localization lane: vocabulary of the Haar/Neumann analysis (H2–H11)

§8. All objects live on a triadic cube `Q` (in applications `Q_n = originCube d n`, side
`3^n`), with volume-normalized `L²` norms (`Haar.energy`, i.e. `cubeAverage` over the half-open
`cubeSet Q`) and `H¹` functions on the open cube `openCubeSet Q` (CoarseGraining `H1Function`).

* `vecEnergy Q G = ‖G‖² = ∑_i ‖G_i‖²`;
* `vecIncrement Q k G = D_k G`, `vecProjection Q k G = E_k G` (componentwise);
* `IsNeumannPrimitive Q G w`: `w ∈ H¹(Q)` has mean zero and `⨍∇w·∇φ = ⨍G·∇φ` for every `φ ∈ H¹(Q)`
  (the Neumann primitive `w = T G` of H2);
* `multSq row Λ = 𝖻(Λ)² = Λ + (q_s - 1)∑_j q_s^j min{Λ, 9^{-j}η_ω(1 + dΛ)}` (H9); for `k ≥ 1`,
  `multSq row (row.haarL k) = row.haarB k ^ 2`.
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta.Localization

open Assembly Contract

variable {d : ℕ}

/-- `‖G‖² = ∑_i ‖G_i‖²` (volume-normalized on `Q`). -/
noncomputable def vecEnergy (Q : Homogenization.TriadicCube d)
    (G : Homogenization.Vec d → Homogenization.Vec d) : ℝ :=
  ∑ i, Haar.energy Q fun x => G x i

/-- `D_k G`, componentwise (`D_0 = E_0`). -/
noncomputable def vecIncrement (Q : Homogenization.TriadicCube d) (k : ℕ)
    (G : Homogenization.Vec d → Homogenization.Vec d) : Homogenization.Vec d → Homogenization.Vec d :=
  fun x i => cubeIncrement Q k (fun y => G y i) x

/-- `E_k G`, componentwise. -/
noncomputable def vecProjection (Q : Homogenization.TriadicCube d) (k : ℕ)
    (G : Homogenization.Vec d → Homogenization.Vec d) : Homogenization.Vec d → Homogenization.Vec d :=
  fun x i => cubeProjection Q k (fun y => G y i) x

/-- `w` is the Neumann primitive `T G` of H2: `w ∈ H¹(Q)`, `⨍_Q w = 0`, and `⨍∇w·∇φ = ⨍G·∇φ` for every
`φ ∈ H¹(Q)`. -/
def IsNeumannPrimitive (Q : Homogenization.TriadicCube d)
    (G : Homogenization.Vec d → Homogenization.Vec d) (w : H1Function (openCubeSet Q)) : Prop :=
  cubeAverage Q w.toFun = 0 ∧
    ∀ φ : H1Function (openCubeSet Q),
      cubeAverage Q (fun x => vecDot (w.grad x) (φ.grad x)) =
        cubeAverage Q (fun x => vecDot (G x) (φ.grad x))

/-- The H9 multiplier constant `𝖻(Λ)² = Λ + (q_s - 1)∑_j q_s^j min{Λ, 9^{-j}η_ω(1 + dΛ)}`. -/
noncomputable def multSq (row : Row d) (Λ : ℝ) : ℝ :=
  Λ + (row.qs - 1) * minSeries row.qs Λ (row.etaOmega * (1 + (d : ℝ) * Λ))

end GMCExplicitDelta.Localization
