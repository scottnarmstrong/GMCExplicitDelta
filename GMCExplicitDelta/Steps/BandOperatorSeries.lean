module

public import GMCExplicitDelta.Contract.DerivedFresh
public import GMCExplicitDelta.Proofs.FreshInsertion.BandSeries

/-!
# Intermediate statements: the two forms of the band operator (I4(a))

The contract defines the fresh returns through the matrix `𝐐 = 𝖢(s_δ𝐋)` (`bandMatrix`, `bandRow`),
as in §3.3 item 13, while the moment transfer I3 (and `Insertion.gaussianMajorant`) work
with the series `∑_n d_n s_δ^n 𝐋^n x^{32}` through `Insertion.coshL`. These targets identify the
two (I4(a): `𝐐^h x^p = ∑_n d_n s_δ^n 𝐋^n x^p`, `d_n = [z^n]𝖢(z)^h`, with `generatorMatrix` the
matrix of `coshL` on polynomials of degree `≤ 32`).

Both statements are proved in `GMCExplicitDelta/Proofs/FreshInsertion/BandSeries.lean`.
-/

@[expose] public section

namespace GMCExplicitDelta.Contract

/-- **I4(a), coefficient form.** `[x^r](𝐐^h x^{32})` computed with the matrix `𝐐 = 𝖢(s_δ𝐋)`
equals the coefficient of `x^r` in `∑_n d_n s_δ^n 𝐋^n x^{32}`, `d_n = [z^n]𝖢(z)^h`. -/
theorem bandRow_eq_bandSeriesCoeff (δ : ℝ) (h : ℕ) (r : Fin 33) :
    bandRow δ h r = bandSeriesCoeff δ h r :=
  bandRow_eq_bandSeriesCoeff_proof δ h r

/-- **I4(a), evaluation form.** `(∑_n d_n s_δ^n 𝐋^n x^{32})(y) = ∑_r [x^r](𝐐^h x^{32}) y^r`. -/
theorem bandSeriesEval_eq_sum (δ : ℝ) (h : ℕ) (y : ℝ) :
    bandSeriesEval δ h y = ∑ r : Fin 33, bandRow δ h r * y ^ (r : ℕ) :=
  bandSeriesEval_eq_sum_proof δ h y

end GMCExplicitDelta.Contract
