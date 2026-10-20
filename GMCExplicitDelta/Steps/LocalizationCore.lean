module

public import GMCExplicitDelta.Localization.Core

/-!
# Intermediate statements: the pointwise localized inequality (L1 + L2 + L3 + H11 + G1 + H13, deterministic)

Proved by
`loc_pointwise_assembled` (`Localization/Core.lean`) from the pieces of
`Steps/LocalizationPieces.lean`. This is the
deterministic heart of L4: for one sample `ω` in the good event `𝒢(Q_n)`, the localized energy of the
depth-`ν` cells is bounded by the Haar-weighted gradient pieces of the maximizer `v` of `J(Q_n,p,q;b_L)`.

proof (`b = b_L(ω)`, `v` the maximizer on `Q_n`, `v_R` the maximizers on the cells,
`φ` the plateau-cosine cutoff `φ_ω` scaled to `Q_n`, `𝐠 = ∇φ`, `w_R = min_R φ`):
* L3: `avg_R w_R J(R) ≤ (1+ε)/2 𝒲 + (1+ε⁻¹)(J_ν - J_0)` with `𝒲 = ⨍ φ ∇v·b∇v`;
* L1: `𝒲 = -⨍(v - v̄)𝐠·b∇v ≤ K_s(b∇v) P_s((v - v̄)𝐠)`, and G1(c) `K_s(b∇v)² ≤ R⨍∇v·b∇v = 2RJ_0`;
* H11: `P_s((v - v̄)𝐠) ≤ ∑_k b_k ‖D_k∇v‖`;
* L2 (deterministic part): `‖D_0∇v‖ = |-p + Y_Q q|`; for `k ≥ 1`,
  `‖D_k∇v‖ ≤ √(2y_k(J_k - J_0)) + √(avg_R |-p + Y_R q - c_k|²)`; and on `𝒢`,
  `‖D_k∇v‖ ≤ √(y_k · 2J_0) ≤ u_s^k√(2RJ_0)`, so the tail `k > K ≥ g` is at most `T_g√(2RJ_0)`;
* H13: `avg_R w_R ≥ c_ν`.
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta.Localization

open Assembly Contract

variable {d : ℕ}

/-- **Pointwise localized inequality.** For every observation scale `n` and Haar truncation `K ≥ g`
there are deterministic weights `0 ≤ w_R ≤ 1` on the depth-`ν` cells of `Q_n` with average `≥ c_ν`
such that, for every sample `ω` in the good event `𝒢(Q_n)`, every pair `(p, q)` and every sequence of
centres `c` with `c 0 = 0`,
`avg_R w_R J(R,p,q) ≤ (1+ε)/2 · (√(2RJ₀) ∑_{k≤K} b_k(√(2y_k(J_k - J₀)) + √(avg_R|-p+Y_Rq-c_k|²))
  + 2R T_g J₀) + (1+ε⁻¹)(J_ν - J₀)`, where `J₀ = J(Q_n,p,q;b_L)` and `J_k = avg_{R depth k} J(R,p,q;b_L)`. -/
theorem loc_pointwise (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (M : SubdiffusiveProcess.Model.GMCModel d) (L n K : ℕ) (hK : row.g ≤ K) :
    ∃ w : Homogenization.TriadicCube d → ℝ, (∀ R, 0 ≤ w R ∧ w R ≤ 1) ∧
      row.cNu ≤ descendantsAverage (originCube d (n : ℤ)) row.nu w ∧
      ∀ ω ∈ goodEvent row M L 0 n, ∀ p q : Homogenization.Vec d, ∀ c : ℕ → Homogenization.Vec d,
        c 0 = 0 →
        cellJw M L n row.nu w p q ω ≤
          locBound row (frozenJ M L (cubeAt 0 n) p q ω) (cellJ M L n row.nu p q ω)
            (haarSum row M L n K p q c ω) :=
  loc_pointwise_assembled row hd hO M L n K hK

end GMCExplicitDelta.Localization
