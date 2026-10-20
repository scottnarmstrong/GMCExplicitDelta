module

public import GMCExplicitDelta.Localization.Defs
public import GMCExplicitDelta.Haar.TriadicProjection
public import GMCExplicitDelta.Haar.CutoffProduct

/-!
# Localization lane: vocabulary of the deterministic pieces (L1–L3, H11, G1)

§8, §10 G1, §12 L1–L3. Fix a sample `ω`, the cutoff `L`, a pair `(p, q)` and the cube
`Q_n = originCube d n` (as a triadic cube; its Chapter 2 domain is `cubeAt 0 n`).

**The maximizer.** `frozenSol M L U p q ω` is the canonical (mean-zero) maximizer of
`J(U, ā_L^{-1/2}p, ā_L^{1/2}q; a_L)` given by CoarseGraining's existence theorem. By C3 the maximizer of
`J(U, p, q; b_L)` (`b_L = a_L/ā_L`) is `v = √ā_L · frozenSol`; it is `frozenH1 M L U p q ω`
(an `H1Function` on `U`), with gradient `∇v = (frozenH1 …).grad` and flux
`b_L∇v = frozenFlux M L U p q ω`. In these terms `J(U,p,q;b_L) = ½⨍_U ∇v·b_L∇v` and `⨍_U∇v = -p + Y_U q`.

**Haar quantities of vector fields** on a triadic cube `Q` (volume-normalized, componentwise; `D_k` is
`cubeIncrement`, with `D_0 = E_0` the mean):
* `incNorm Q k G = ‖D_k G‖ = (∑_i ‖D_k G_i‖²)^{1/2}`;
* `haarPrimal Q q G = P_s(G)² = ∑_k q^k ‖D_k G‖²` (an `ℝ≥0∞` series, so no summability side
  conditions), with `q = q_s`;
* `haarDual Q q G = K_s(G)² = ∑_k q^{-k} ‖D_k G‖²`.

**The cutoff** (H7): `cubeCutoff row n x = φ_ω(3^{-n}x)` with `φ_ω = Haar.cutoffProduct ω` (plateau
width `ω = row.omegaEff`; the full cosine in `d = 2`), and its gradient
`cubeCutoffGrad row n x = 3^{-n}(∇φ_ω)(3^{-n}x)`.

**The localized quantities**: `locEnergy row M L n p q ω = 𝒲 = ⨍_{Q_n} φ ∇v·b_L∇v` and, for an `H¹`
function `u`, `locTestField row n u = (u - ū)𝐠` (the field of L1 and H11).
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta.Localization

open Assembly Contract

variable {d : ℕ}

/-! ### The maximizer of the frozen response -/

/-- The canonical maximizer of `J(U, ā_L^{-1/2}p, ā_L^{1/2}q; a_L)` (mean zero on `U`). -/
noncomputable def frozenSol (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (p q : Homogenization.Vec d) (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    Ch02.Solution U (aCutoffCoeffOnData M L ω U).toCoeffOn :=
  (Ch02.canonicalMaximizer (Ch02.responseExistenceTheory U _)
    ((Real.sqrt (ahom M L))⁻¹ • p) (Real.sqrt (ahom M L) • q)).toSolution

/-- The maximizer `v(·, U, p, q; b_L) = √ā_L · frozenSol` as an `H¹` function on `U` (C3). -/
noncomputable def frozenH1 (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (p q : Homogenization.Vec d) (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    H1Function (U : Set (Homogenization.Vec d)) :=
  Real.sqrt (ahom M L) • (frozenSol M L U p q ω).toH1

/-- The flux `b_L∇v` of the frozen maximizer, `b_L = a_L/ā_L`. -/
noncomputable def frozenFlux (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (U : Ch02.Domain d) (p q : Homogenization.Vec d)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) : Homogenization.Vec d → Homogenization.Vec d :=
  fun x => (SubdiffusiveProcess.Model.aCutoff M L ω x / ahom M L) • (frozenH1 M L U p q ω).grad x

/-! ### Haar quantities of vector fields -/

/-- `‖D_k G‖ = (∑_i ‖D_k G_i‖²)^{1/2}` (volume-normalized; `D_0 = E_0`). -/
noncomputable def incNorm (Q : Homogenization.TriadicCube d) (k : ℕ)
    (G : Homogenization.Vec d → Homogenization.Vec d) : ℝ :=
  Real.sqrt (∑ i, Haar.energy Q (cubeIncrement Q k fun x => G x i))

/-- `P_s(G)² = ∑_{k≥0} q^k ‖D_k G‖²` as an `ℝ≥0∞` series (H1, `q = q_s`). -/
noncomputable def haarPrimal (Q : Homogenization.TriadicCube d) (q : ℝ)
    (G : Homogenization.Vec d → Homogenization.Vec d) : ℝ≥0∞ :=
  ∑' k : ℕ, ENNReal.ofReal (q ^ k * ∑ i, Haar.energy Q (cubeIncrement Q k fun x => G x i))

/-- `K_s(G)² = ∑_{k≥0} q^{-k} ‖D_k G‖²` (H1). -/
noncomputable def haarDual (Q : Homogenization.TriadicCube d) (q : ℝ)
    (G : Homogenization.Vec d → Homogenization.Vec d) : ℝ≥0∞ :=
  haarPrimal Q q⁻¹ G

/-! ### The cutoff on `Q_n` -/

/-- `φ(x) = φ_ω(3^{-n}x)`, the plateau-cosine cutoff (H7) scaled to `Q_n = (-3^n/2, 3^n/2)^d`. -/
noncomputable def cubeCutoff (row : Row d) (n : ℕ) (x : Homogenization.Vec d) : ℝ :=
  Haar.cutoffProduct row.omegaEff fun i => x i / (3 : ℝ) ^ n

/-- `𝐠(x) = ∇φ(x) = 3^{-n}(∇φ_ω)(3^{-n}x)`. -/
noncomputable def cubeCutoffGrad (row : Row d) (n : ℕ) (x : Homogenization.Vec d) :
    Homogenization.Vec d :=
  fun i => Haar.cutoffGradient row.omegaEff (fun j => x j / (3 : ℝ) ^ n) i / (3 : ℝ) ^ n

/-- The localized test field `(u - ū)𝐠` of L1 and H11 (`ū` the average over `Q_n`). -/
noncomputable def locTestField (row : Row d) (n : ℕ)
    (u : Homogenization.Vec d → ℝ) : Homogenization.Vec d → Homogenization.Vec d :=
  fun x => (u x - cubeAverage (originCube d (n : ℤ)) u) • cubeCutoffGrad row n x

/-- `𝒲 = ⨍_{Q_n} φ ∇v·b_L∇v`, the cutoff-weighted energy of the frozen maximizer (L1, L3). -/
noncomputable def locEnergy (row : Row d) (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    (p q : Homogenization.Vec d) (ω : SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  cubeAverage (originCube d (n : ℤ)) fun x =>
    cubeCutoff row n x * vecDot ((frozenH1 M L (cubeAt 0 n) p q ω).grad x)
      (frozenFlux M L (cubeAt 0 n) p q ω x)

end GMCExplicitDelta.Localization
