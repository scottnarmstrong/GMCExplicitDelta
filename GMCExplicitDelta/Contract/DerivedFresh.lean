module

public import GMCExplicitDelta.Contract.DerivedAveraging
public import GMCExplicitDelta.Contract.DerivedBarrier
public import GMCExplicitDelta.Insertion.CoshGeneratorPoly
public import Mathlib.Data.Matrix.Mul
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Contract layer: the band operator, fresh returns and seeds

§3.3 item 13, I2–I10, K2–K3.

The generator `𝐋` of I2 is `GMCExplicitDelta.Insertion.coshL` (on `ℝ[X]`,
`𝐋 x^k = (k²/2)x^k + (k(2k-1)/2)x^{k-1}`). Two forms of the band operator are provided:

* **matrix form** (the definition, §3.3 item 13): `generatorMatrix` is the matrix of
  `coshL` in the monomial basis `1, x, …, x^{32}` with the convention
  `generatorMatrix i j = [x^j](𝐋 x^i)` (definitionally, `generatorMatrix_apply`), so that matrix
  products compose operators (`(𝐋²)_{ij} = [x^j](𝐋²x^i)`). `bandMatrix δ` is
  `𝐐 = I + 𝗎s_δ𝐋 + c₂(𝖺s_δ𝐋)²/2 + c₃∑_{n≥3}(𝖺s_δ𝐋)^n/n!` (entrywise `tsum`), and
  `bandRow δ h r = (𝐐^h)_{32,r} = [x^r](𝐐^h x^{32})`. The fresh returns `post`, `seed` use this
  form, and the numerics layer encloses it by `𝐐_{N_b} + ε_b𝐄_low` (I4(b)).
* **series form** (I4(a)): `𝐐^h x^{32} = ∑_n d_n s_δ^n 𝐋^n x^{32}` with `d_n = [z^n]𝖢(z)^h`,
  stated through `coshL` itself: `bandSeriesCoeff δ h r` (coefficient of `x^r`) and
  `bandSeriesEval δ h y` (value at `y`), in the shape of `Insertion.gaussianMajorant`.
  The identity between the two forms is the intermediate statement
  `GMCExplicitDelta.Contract.bandRow_eq_bandSeriesCoeff` (`Steps/BandOperatorSeries.lean`).
-/

@[expose] public section

open Real Polynomial

namespace GMCExplicitDelta.Contract

/-! ### I2: the generator matrix and the band operator -/

/-- The matrix of the generator `𝐋 = Insertion.coshL` (I2) on polynomials of degree `≤ 32` in the
monomial basis: entry `(i, j)` is `[x^j](𝐋 x^i)`. Lower bidiagonal with diagonal `i²/2` and
subdiagonal `i(2i-1)/2`. -/
noncomputable def generatorMatrix : Matrix (Fin 33) (Fin 33) ℝ :=
  Matrix.of fun i j => (Insertion.coshL (X ^ (i : ℕ) : ℝ[X])).coeff (j : ℕ)

theorem generatorMatrix_apply (i j : Fin 33) :
    generatorMatrix i j = (Insertion.coshL (X ^ (i : ℕ) : ℝ[X])).coeff (j : ℕ) := rfl

/-- The one-band operator `𝐐 = 𝖢(s_δ𝐋) = I + 𝗎s_δ𝐋 + (c₂/2)(𝖺s_δ𝐋)² + c₃∑_{n≥3}(𝖺s_δ𝐋)^n/n!`
with `s_δ = δ²` (I3), as a `33 × 33` matrix; the series is summed entrywise. -/
noncomputable def bandMatrix (δ : ℝ) : Matrix (Fin 33) (Fin 33) ℝ :=
  Matrix.of fun i j =>
    ((1 : Matrix (Fin 33) (Fin 33) ℝ) + ((varU : ℝ) * δ ^ 2) • generatorMatrix +
        ((ratioC2 : ℝ) / 2) • (((proxyA : ℝ) * δ ^ 2) • generatorMatrix) ^ 2) i j +
      (ratioC3 : ℝ) * ∑' n : ℕ,
        ((((proxyA : ℝ) * δ ^ 2) • generatorMatrix) ^ (n + 3)) i j / ((n + 3).factorial : ℝ)

/-- `[x^r](𝐐^h x^{32}) = (𝐐^h)_{32,r}`. -/
noncomputable def bandRow (δ : ℝ) (h : ℕ) (r : Fin 33) : ℝ := ((bandMatrix δ) ^ h) 32 r

/-! ### I3, I4(a): the series form through `coshL` -/

/-- The one-band coefficient majorant `𝖢(z) = 1 + 𝗎z + (c₂/2)(𝖺z)² + c₃∑_{n≥3}(𝖺z)^n/n!` (I3) as a
formal power series. -/
noncomputable def bandSeries : PowerSeries ℝ :=
  PowerSeries.mk fun n =>
    if n = 0 then 1
    else if n = 1 then (varU : ℝ)
    else if n = 2 then (ratioC2 : ℝ) * (proxyA : ℝ) ^ 2 / 2
    else (ratioC3 : ℝ) * (proxyA : ℝ) ^ n / (n.factorial : ℝ)

/-- `[x^r]∑_n d_n s_δ^n 𝐋^n x^{32}`, `d_n = [z^n]𝖢(z)^h` (I4(a)). -/
noncomputable def bandSeriesCoeff (δ : ℝ) (h r : ℕ) : ℝ :=
  ∑' n : ℕ, (δ ^ 2) ^ n * PowerSeries.coeff n (bandSeries ^ h) *
    ((Insertion.coshL ^ n) (X ^ 32 : ℝ[X])).coeff r

/-- `(∑_n d_n s_δ^n 𝐋^n x^{32})(y)`, `d_n = [z^n]𝖢(z)^h` (I3, I4(a)): the form in which the
conditional moment transfer I3 produces `(𝐐^h x^{32})(j_e)`. -/
noncomputable def bandSeriesEval (δ : ℝ) (h : ℕ) (y : ℝ) : ℝ :=
  ∑' n : ℕ, (δ ^ 2) ^ n * PowerSeries.coeff n (bandSeries ^ h) *
    ((Insertion.coshL ^ n) (X ^ 32 : ℝ[X])).eval y

/-- `z_b = 1520 𝖺 δ²`, the `∞`-norm bound of `𝖺s_δ𝐋` (I4(b), O.band.1). -/
noncomputable def bandNormBound (δ : ℝ) : ℝ := 1520 * (proxyA : ℝ) * δ ^ 2

namespace Row

variable {d : ℕ} (row : Row d)

/-! ### Item 13: fresh returns and seeds -/

/-- The fresh drift exponent `γ_h = κhδ²` (§1.7, N3). -/
noncomputable def gammaH (δ : ℝ) : ℝ := (kappaQ1 : ℝ) * (row.h : ℝ) * δ ^ 2

/-- `F_next = t_⋆F` (T3). -/
noncomputable def Fnext (F : ℝ) : ℝ := row.tStar * F

/-- `D_next = U_h` (A6 with `k = h`). -/
noncomputable def Dnext (D F : ℝ) : ℝ := nativeCap d row.h D F

/-- The old moment profile `μ₀ = 1`, `μ_r = F_next^{(32-r)/31} D_next^{32(r-1)/31}` (I5). -/
noncomputable def profile (D F : ℝ) (r : ℕ) : ℝ :=
  if r = 0 then 1
  else row.Fnext F ^ ((32 - (r : ℝ)) / 31) * row.Dnext D F ^ (32 * ((r : ℝ) - 1) / 31)

/-- `𝓜 = ∑_{r=0}^{32}[x^r](𝐐^h x^{32}) μ_r` (I6). -/
noncomputable def freshMoment (δ D F : ℝ) : ℝ :=
  ∑ r : Fin 33, bandRow δ row.h r * row.profile D F r

/-- `sym = (β_d^{32}𝓜)^{1/32}` (I6). -/
noncomputable def sym (δ D F : ℝ) : ℝ :=
  ((sphereFactorPow d : ℝ) * row.freshMoment δ D F) ^ ((1 : ℝ) / 32)

/-- The fresh norm return: `post = sym` for `d = 2`, `Φ_{γ_h}(sym)` for `d ≥ 3` (I7, I9;
). -/
noncomputable def post (δ D F : ℝ) : ℝ :=
  if d = 2 then row.sym δ D F else PhiMap (row.gammaH δ) (row.sym δ D F)

/-- The fresh mean return: `e^{γ_h}(1+F_next) - 1` for `d = 2`, `e^{2γ_h}F_next + (e^{2γ_h}-1)/2`
for `d ≥ 3` (I8, I9). -/
noncomputable def meanpost (δ F : ℝ) : ℝ :=
  if d = 2 then Real.exp (row.gammaH δ) * (1 + row.Fnext F) - 1
  else Real.exp (2 * row.gammaH δ) * row.Fnext F + (Real.exp (2 * row.gammaH δ) - 1) / 2

/-- The seed evaluation point `x₀`: `0` for `d = 2`, `cosh γ_h - 1` for `d ≥ 3` (K2). -/
noncomputable def seedPoint (δ : ℝ) : ℝ := if d = 2 then 0 else Real.cosh (row.gammaH δ) - 1

/-- The norm seed `seed = ([𝐐^h x^{32}](x₀))^{1/32}` (K2). -/
noncomputable def seed (δ : ℝ) : ℝ :=
  (∑ r : Fin 33, bandRow δ row.h r * row.seedPoint δ ^ (r : ℕ)) ^ ((1 : ℝ) / 32)

/-- The mean seed: `e^{γ_h} - 1` for `d = 2`, `(e^{2γ_h} - 1)/2` for `d ≥ 3` (K3;
). -/
noncomputable def meanseed (δ : ℝ) : ℝ :=
  if d = 2 then Real.exp (row.gammaH δ) - 1 else (Real.exp (2 * row.gammaH δ) - 1) / 2

end Row

end GMCExplicitDelta.Contract
