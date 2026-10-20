module

public import GMCExplicitDelta.Contract.DerivedHistory
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Contract layer: mean-sensitive averaging, native caps, excess and bad charge

§3.3 items 7–8 (A2–A6, G7–G9) and the sphere constant `𝓛_d` of A4 (O.avg.1).
The averaging constants depend on the caps only through `ϖ = min(F/D, 1)`, which is invariant
under the λ-scaling `(D, F) ↦ (λD, λF)` (R4(c)).
-/

@[expose] public section

open Real

namespace GMCExplicitDelta.Contract

/-! ### A2: associated Stirling numbers -/

/-- The pair of rows `(𝒜(p, ·), 𝒜(p+1, ·))` as lists indexed by `k = 0, …, p` (resp. `p + 1`),
built by the recurrence `𝒜(p+2,k) = k𝒜(p+1,k) + (p+1)𝒜(p,k-1)`, `𝒜(0,0) = 1`, `𝒜(1,·) = 0` (A2). -/
def assocStirlingRows : ℕ → List ℕ × List ℕ
  | 0 => ([1], [0, 0])
  | p + 1 =>
    let ab := assocStirlingRows p
    (ab.2, (List.range (p + 3)).map fun k =>
      k * ab.2.getD k 0 + (p + 1) * (if k = 0 then 0 else ab.1.getD (k - 1) 0))

/-- The associated Stirling number `𝒜(p, k)`: by A2, the number of partitions of `{1, …, p}` into
`k` blocks all of size `≥ 2`. -/
def assocStirling (p k : ℕ) : ℕ := (assocStirlingRows p).1.getD k 0

/-- The table `𝒜(32, k)`, `k = 1, …, 16`, quoted in A2;
indexed by `k - 1`. Obligation O.avg.2 states that it agrees with `assocStirling 32`. -/
def assocStirling32Table : List ℕ :=
  [1, 2147483615, 308800190920486, 765011543314355365, 187128474745367109190,
    9648191836041940120446, 154227582326730813420156, 948856977801169301069205,
    2550133124516049612389850, 3217076814220214136741550, 1967326750353779714399500,
    581105308935958505448750, 79198178493972888850500, 4449180413533177822500,
    79318164037837725000, 191898783962510625]

/-! ### A3: the mean-sensitive moment bound -/

/-- `ϖ = min(F/D, 1)` (§1.7, A1). -/
noncomputable def varpi (D F : ℝ) : ℝ := min (F / D) 1

/-- `T_ϖ = ϖ^{32/31}` (§1.7, A3). The producer uses a rational `T_+ ≥ T_ϖ` (O.avg.3); the
contract uses the exact value, and `B̄₃₂` is nondecreasing in `T`. -/
noncomputable def Tvarpi (D F : ℝ) : ℝ := varpi D F ^ ((32 : ℝ) / 31)

/-- `B̄₃₂(n, ϖ) = (∑_{k=1}^{16} 𝒜(32,k) n^{k-32} T_ϖ^{k-1})^{1/32}` (A3),
written with `k + 1` for `k ∈ range 16`. -/
noncomputable def Bbar32 (n : ℕ) (D F : ℝ) : ℝ :=
  (∑ k ∈ Finset.range 16,
      (assocStirling 32 (k + 1) : ℝ) * Tvarpi D F ^ k / (n : ℝ) ^ (31 - k)) ^ ((1 : ℝ) / 32)

/-- The normalized native cuts `𝔲₀ = 1`, `𝔲_ℓ = min{1, σ_d B̄₃₂(3^{d(ℓ-1)}, ϖ)}` for `ℓ ≥ 1`
(A6). -/
noncomputable def frakU (d ℓ : ℕ) (D F : ℝ) : ℝ :=
  if ℓ = 0 then 1 else min 1 ((sigmaNorm d : ℝ) * Bbar32 (3 ^ (d * (ℓ - 1))) D F)

/-- The native caps `U_k = min{D, F + σ_d D B̄₃₂(3^{d(k-1)}, ϖ)}` for `k ≥ 1` (A6;
`native_operator_cap`). The value at `k = 0` is not used. -/
noncomputable def nativeCap (d k : ℕ) (D F : ℝ) : ℝ :=
  min D (F + (sigmaNorm d : ℝ) * D * Bbar32 (3 ^ (d * (k - 1))) D F)

/-! ### C7: the rescaled-pair map -/

/-- `Φ_t(j) = (1+j)cosh t - 1 + √(j(j+2)) sinh t` (C7, §3.3 item 8). -/
noncomputable def PhiMap (t j : ℝ) : ℝ :=
  (1 + j) * Real.cosh t - 1 + √(j * (j + 2)) * Real.sinh t

namespace Row

variable {d : ℕ} (row : Row d)

/-! ### Items 7–8: coarse convolution, excess and bad charge -/

/-- `S_∞ = ∑_{ℓ≥0} 𝔲_ℓ x^{-ℓ}` (G7). Summable when `3^{-d/2} < x` and `𝔲_{12} < 1`
(O.avg.4, O.avg.5, with A6's ratio bound). -/
noncomputable def Sinf (D F : ℝ) : ℝ := ∑' ℓ : ℕ, frakU d ℓ D F * row.xHist⁻¹ ^ ℓ

/-- The complete excess `e_⋆ = (1-w)D x^g S_∞ + x^g H` (G7). -/
noncomputable def eStar (δ D F : ℝ) : ℝ :=
  (1 - row.wHaar) * D * row.xHist ^ row.g * row.Sinf D F + row.xHist ^ row.g * row.Hhist δ D

/-- The bad charge `bad = Φ_{log(1+2F)}(U_{g-ν})/F · (e_⋆/(θ_R - F))^{31}` (G9, O.bad.2;
producer `matched`). -/
noncomputable def badCharge (δ D F : ℝ) : ℝ :=
  PhiMap (Real.log (1 + 2 * F)) (nativeCap d (row.g - row.nu) D F) / F *
    (row.eStar δ D F / (row.thetaR - F)) ^ 31

end Row

/-! ### A4: the sphere constant `𝓛_d` (O.avg.1) -/

/-- The rising factorial `(x)_n = x(x+1)⋯(x+n-1)` over `ℚ`. -/
def risingQ (x : ℚ) (n : ℕ) : ℚ := ∏ i ∈ Finset.range n, (x + i)

/-- The coefficient of `λ^{32-j}` in `𝒫_d(λ) = 𝔼[T + λ(1-T)]^{32}`, `T ∼ Beta(1/2, (d-1)/2)`:
`binom(32,j)(1/2)_j((d-1)/2)_{32-j}/(d/2)_{32}` (A4). -/
def spherePolyCoeff (d j : ℕ) : ℚ :=
  (Nat.choose 32 j : ℚ) * risingQ (1 / 2) j * risingQ (((d : ℚ) - 1) / 2) (32 - j) /
    risingQ ((d : ℚ) / 2) 32

/-- `𝒫_d(λ) = ∑_{j=0}^{32} binom(32,j) λ^{32-j} (1/2)_j((d-1)/2)_{32-j}/(d/2)_{32}` (A4). -/
def spherePoly (d : ℕ) (lam : ℚ) : ℚ :=
  ∑ j ∈ Finset.range 33, spherePolyCoeff d j * lam ^ (32 - j)

/-- `𝒫_d'(λ)` (A4). -/
def spherePolyDeriv (d : ℕ) (lam : ℚ) : ℚ :=
  ∑ j ∈ Finset.range 32, spherePolyCoeff d j * ((32 - j : ℕ) : ℚ) * lam ^ (31 - j)

/-- The tangent points `a_d` of A4 (exact decimals). -/
def sphereTangent (d : ℕ) : ℚ :=
  if d = 2 then -859243472898 / 10 ^ 12
  else if d = 3 then -809137015788 / 10 ^ 12 else -766245299107 / 10 ^ 12

/-- `𝓛_d = 𝒫_d(a_d) - 2|𝒫_d'(a_d)|`, a lower bound of `min_{[-1,1]} 𝒫_d` by convexity (A4). -/
def sphereLower (d : ℕ) : ℚ :=
  spherePoly d (sphereTangent d) - 2 * |spherePolyDeriv d (sphereTangent d)|

end GMCExplicitDelta.Contract
