module

public import GMCExplicitDelta.Contract.DerivedGeometry

/-!
# Contract layer: contraction coefficients, variance budgets and the terminal barrier

§3.3 items 10–12, L4–L6, V3–V5, T2–T4. Quantities that move under the λ-scaling of R4
take the caps `D F : ℝ` as explicit arguments; the row's values are obtained at
`D = row.D`, `F = row.F`, and the scaled values at `(λD, λF)`.
-/

@[expose] public section

open Real

namespace GMCExplicitDelta.Contract

/-! ### Dimension-only factors -/

/-- `σ_A`: `1` for `d = 2`, `√(1+2F)` for `d ≥ 3` (L6). -/
noncomputable def sigmaA (d : ℕ) (F : ℝ) : ℝ := if d = 2 then 1 else √(1 + 2 * F)

/-- `σ_V`: `1` for `d = 2`, `√2` for `d ≥ 3` (L6). -/
noncomputable def sigmaV (d : ℕ) : ℝ := if d = 2 then 1 else √2

/-- `σ_B`: `1` for `d = 2`, `1+2F` for `d ≥ 3` (L6). -/
noncomputable def sigmaB (d : ℕ) (F : ℝ) : ℝ := if d = 2 then 1 else 1 + 2 * F

/-- The variance lag `ℓ_v`: `3` for `d = 2`, `2` for `d ≥ 3` (V3). -/
def ellV (d : ℕ) : ℕ := if d = 2 then 3 else 2

/-- `vi = (2F + 2D²)/F`, the normalized initial variance (V1). -/
noncomputable def vi (D F : ℝ) : ℝ := (2 * F + 2 * D ^ 2) / F

namespace Row

variable {d : ℕ} (row : Row d)

/-! ### Item 10: contraction coefficients -/

/-- `A = (1+ε)R σ_A / c_ν`. -/
noncomputable def coefA (F : ℝ) : ℝ :=
  (1 + (row.epsilon : ℝ)) * (row.R : ℝ) / row.cNu * sigmaA d F

/-- `A_v = (1+ε)√(2R) σ_V / (2c_ν)`. -/
noncomputable def coefAv : ℝ :=
  (1 + (row.epsilon : ℝ)) * √(2 * (row.R : ℝ)) / (2 * row.cNu) * sigmaV d

/-- `B = (1+ε⁻¹) σ_B / c_ν`. -/
noncomputable def coefB (F : ℝ) : ℝ := (1 + (row.epsilon : ℝ)⁻¹) / row.cNu * sigmaB d F

/-- `τ_abs = (1+ε)R K_s ρ_s^{g+1} / (c_ν(1-ρ_s))` (O.geo.4). This is the certified
majorant form of `(1+ε)R T_g/c_ν`: L4 accepts any `τ_abs ≥ (1+ε)R T_g/c_ν`, and
H12 gives `T_g ≤ K_s ρ_s^{g+1}/(1-ρ_s)`. -/
noncomputable def tauAbs : ℝ :=
  (1 + (row.epsilon : ℝ)) * (row.R : ℝ) * row.Ks * row.rhoS ^ (row.g + 1) /
    (row.cNu * (1 - row.rhoS))

/-! ### Item 11: variance budgets -/

/-- `ρ_v`: `32/207` for `d = 2`; `(5 + 2(η_v + η_v⁻¹))2^d 3^{-2d}` for `d ≥ 3` (V3). -/
noncomputable def rhoV : ℝ :=
  if d = 2 then 32 / 207
  else (5 + 2 * ((row.young : ℝ) + (row.young : ℝ)⁻¹)) * 2 ^ d / 3 ^ (2 * d)

/-- `c_v`: `27/23` for `d = 2`; `1 + 2/η_v` for `d ≥ 3` (V3). -/
noncomputable def cV : ℝ := if d = 2 then 27 / 23 else 1 + 2 / (row.young : ℝ)

/-- The variance start index `j_v`: `g - ⌊g/2⌋` for `d = 2`, `⌊g/2⌋` for `d ≥ 3` (V5). -/
def jV : ℕ := if d = 2 then row.g - row.g / 2 else row.g / 2

/-- The Haar split `K' = g - j_v`: `⌊g/2⌋` for `d = 2`, `g - ⌊g/2⌋` for `d ≥ 3` (V5, §17). -/
def Kprime : ℕ := if d = 2 then row.g / 2 else row.g - row.g / 2

/-- `Q_{t0} = ℓ_v vi ρ_v^{⌊(j_v-1)/ℓ_v⌋}/(1-ρ_v)` (V4 with `j = j_v`). -/
noncomputable def Qt0 (D F : ℝ) : ℝ :=
  (ellV d : ℝ) * vi D F * row.rhoV ^ ((row.jV - 1) / ellV d) / (1 - row.rhoV)

/-- `Q_{f0} = vi(1 + ℓ_v/(1-ρ_v))` (V4). -/
noncomputable def Qf0 (D F : ℝ) : ℝ := vi D F * (1 + (ellV d : ℝ) / (1 - row.rhoV))

/-- `Q_for = ℓ_v c_v F/(1-ρ_v)` (V4). -/
noncomputable def Qfor (F : ℝ) : ℝ := (ellV d : ℝ) * row.cV * F / (1 - row.rhoV)

/-- `B_tail = K_s(u_s/3)^{K'+1}/(1-u_s/3)`, the H12 majorant of `∑_{k>K'} b_k` (V5). -/
noncomputable def Btail : ℝ := row.Ks * (row.us / 3) ^ (row.Kprime + 1) / (1 - row.us / 3)

/-! ### Item 12: terminal barrier -/

/-- The window length `M = h - g + 1` (§1.7 with `r = 0`). -/
def Mwin : ℕ := row.h - row.g + 1

/-- The terminal fraction `t_⋆ = Z/M` (§1.7, §3.2). -/
noncomputable def tStar : ℝ := (row.Z : ℝ) / (row.Mwin : ℝ)

/-- `u_⋆ = t_⋆F`. -/
noncomputable def uStar (F : ℝ) : ℝ := row.tStar * F

end Row

/-- The planar matching divisor `𝗋(μ) = (1+μ)(1+μ/2)` (L5(a)). -/
noncomputable def rMatch (μ : ℝ) : ℝ := (1 + μ) * (1 + μ / 2)

/-- The planar matching multiplier `𝖢(μ) = 1 + μ + μ²/2` (L5(a)). -/
noncomputable def cMatch (μ : ℝ) : ℝ := 1 + μ + μ ^ 2 / 2

/-- The planar matching ratio `𝗊(μ) = 𝖢(μ)/𝗋(μ)` (L6, T4). -/
noncomputable def qMatch (μ : ℝ) : ℝ := cMatch μ / rMatch μ

namespace Row

variable {d : ℕ} (row : Row d)

/-- `r_⋆`: `𝗋(u_⋆) = (1+u_⋆)(1+u_⋆/2)` for `d = 2`, `1` for `d ≥ 3`. -/
noncomputable def rStar (F : ℝ) : ℝ := if d = 2 then rMatch (row.uStar F) else 1

/-- `𝗊_⋆`: `(1+u_⋆+u_⋆²/2)/r_⋆` for `d = 2`, `1` for `d ≥ 3`. -/
noncomputable def qStar (F : ℝ) : ℝ := if d = 2 then qMatch (row.uStar F) else 1

/-- The barrier coefficient `C(t_⋆) = A S_d √(1-t_⋆)√𝗊_⋆ + (A_v/√r_⋆)[S_b√(Q_{t0}+Q_for(1-t_⋆²))
+ B_tail√(Q_{f0}+Q_for(1-t_⋆²))]` (T2). -/
noncomputable def Cbar (D F : ℝ) : ℝ :=
  row.coefA F * row.Sd * √(1 - row.tStar) * √(row.qStar F) +
    row.coefAv / √(row.rStar F) *
      (row.Sb * √(row.Qt0 D F + row.Qfor F * (1 - row.tStar ^ 2)) +
        row.Btail * √(row.Qf0 D F + row.Qfor F * (1 - row.tStar ^ 2)))

/-- The scalar barrier `𝔰 = (1-τ_abs)Z - C(t_⋆)√Z - νB(1-t_⋆)𝗊_⋆ - M b_bad` (T3, O.bar.1). -/
noncomputable def barrier (D F : ℝ) : ℝ :=
  (1 - row.tauAbs) * (row.Z : ℝ) - row.Cbar D F * √(row.Z : ℝ)
    - (row.nu : ℝ) * row.coefB F * (1 - row.tStar) * row.qStar F
    - (row.Mwin : ℝ) * (row.badBudget : ℝ)

/-! ### T4: the planar all-λ derivative test (application, O.bar.2) -/

/-- `v_{t0} = 2ℓ_v ρ_v^{⌊(j_v-1)/ℓ_v⌋}/(1-ρ_v)` (T4 application). -/
noncomputable def vT0 : ℝ :=
  2 * (ellV d : ℝ) * row.rhoV ^ ((row.jV - 1) / ellV d) / (1 - row.rhoV)

/-- `v_{f0} = 2(1 + ℓ_v/(1-ρ_v))` (T4 application). -/
noncomputable def vF0 : ℝ := 2 * (1 + (ellV d : ℝ) / (1 - row.rhoV))

/-- `v_{t1} = Q_{t0} - v_{t0} + Q_for(1-t_⋆²)`, so `v_{t0}+v_{t1} = Q_{t0}+Q_for(1-t_⋆²)` (T4
application). -/
noncomputable def vT1 (D F : ℝ) : ℝ := row.Qt0 D F - row.vT0 + row.Qfor F * (1 - row.tStar ^ 2)

/-- `v_{f1} = Q_{f0} - v_{f0} + Q_for(1-t_⋆²)` (T4 application). -/
noncomputable def vF1 (D F : ℝ) : ℝ := row.Qf0 D F - row.vF0 + row.Qfor F * (1 - row.tStar ^ 2)

end Row

/-- `n_i = v_{i1}(1-u_⋆²/2) - v_{i0}(3u_⋆/2+u_⋆²)` (T4). -/
noncomputable def nMatch (v0 v1 u : ℝ) : ℝ := v1 * (1 - u ^ 2 / 2) - v0 * (3 * u / 2 + u ^ 2)

/-- `m_i = n_i/(2√(v_{i0}+v_{i1}) 𝗋(u_⋆)^{3/2})`, written `𝗋·√𝗋` for `𝗋^{3/2}` (T4). -/
noncomputable def mMatch (v0 v1 u : ℝ) : ℝ :=
  nMatch v0 v1 u / (2 * √(v0 + v1) * (rMatch u * √(rMatch u)))

namespace Row

variable {d : ℕ} (row : Row d)

/-- T4's `a = A S_d √(1-t_⋆)` (T4 application). -/
noncomputable def t4a (F : ℝ) : ℝ := row.coefA F * row.Sd * √(1 - row.tStar)

/-- T4's `b = A_v S_b` (T4 application). -/
noncomputable def t4b : ℝ := row.coefAv * row.Sb

/-- T4's `c = A_v B_tail` (T4 application). -/
noncomputable def t4c : ℝ := row.coefAv * row.Btail

/-- T4's `𝓛 = νB(1-t_⋆)/√Z` (T4 application). -/
noncomputable def t4L (F : ℝ) : ℝ := (row.nu : ℝ) * row.coefB F * (1 - row.tStar) / √(row.Z : ℝ)

/-- T4's `𝓡(λ) = a√𝗊(λu_⋆) + b√((v_{t0}+λv_{t1})/𝗋(λu_⋆)) + c√((v_{f0}+λv_{f1})/𝗋(λu_⋆))
+ 𝓛𝗊(λu_⋆)`, with `a, b, c, 𝓛, v_{··}` evaluated at the caps `(D, F)` (T4). -/
noncomputable def t4R (D F lam : ℝ) : ℝ :=
  row.t4a F * √(qMatch (lam * row.uStar F)) +
    row.t4b * √((row.vT0 + lam * row.vT1 D F) / rMatch (lam * row.uStar F)) +
    row.t4c * √((row.vF0 + lam * row.vF1 D F) / rMatch (lam * row.uStar F)) +
    row.t4L F * qMatch (lam * row.uStar F)

/-- The right side of the derivative test (S):
`(1-u_⋆²/2)/𝗋(u_⋆)² · [a u_⋆/(4√𝗊(u_⋆)) + 𝓛u_⋆/2]` (T4). -/
noncomputable def t4Loss (F : ℝ) : ℝ :=
  (1 - row.uStar F ^ 2 / 2) / rMatch (row.uStar F) ^ 2 *
    (row.t4a F * row.uStar F / (4 * √(qMatch (row.uStar F))) + row.t4L F * row.uStar F / 2)

end Row

end GMCExplicitDelta.Contract
