module

public import GMCExplicitDelta.Proofs.Variance.PairAlgebra
public import GMCExplicitDelta.Proofs.Variance.VarianceTools

/-! # Integrating the centered decrement trace inequality -/

@[expose] public section

open MeasureTheory Matrix Homogenization Homogenization.Book

namespace GMCExplicitDelta.Assembly

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem frozenVar_centered_trace_decrement {D Z : Ω → Homogenization.Mat d}
    (hD : ∀ i j, MemLp (fun ω => D ω i j) 2 μ)
    (hZ : ∀ i j, MemLp (fun ω => Z ω i j) 2 μ)
    (hTD : Integrable (fun ω => Matrix.trace (D ω)) μ)
    (hTZ : Integrable (fun ω => Matrix.trace (Z ω)) μ)
    (δ g : ℝ) (hmeanD : (∫ ω, Matrix.trace (D ω) ∂μ) = (d : ℝ) * δ)
    (hmeanZ : (∫ ω, Matrix.trace (Z ω) ∂μ) = 0)
    (hp : ∀ ω, frobSq (D ω) ≤ 2 * frozenVar_matrixPair (D ω) (Z ω + g • 1)) :
    (∫ ω, frobSq (D ω - δ • (1 : Homogenization.Mat d)) ∂μ) + (d : ℝ) * δ ^ 2 ≤
      2 * g * ((d : ℝ) * δ) + 2 * ∫ ω, frozenVar_matrixPair (D ω - δ • 1) (Z ω) ∂μ := by
  have hDc (i j : Fin d) : MemLp
      (fun ω => (D ω - δ • (1 : Homogenization.Mat d)) i j) 2 μ :=
    (hD i j).sub (memLp_const _)
  have hP := frozenVar_integrable_matrixPair hDc hZ
  have hp' (ω : Ω) : frobSq (D ω) ≤
      2 * frozenVar_matrixPair (D ω - δ • 1) (Z ω) +
        2 * g * Matrix.trace (D ω) + 2 * δ * Matrix.trace (Z ω) := by
    calc
      _ ≤ 2 * frozenVar_matrixPair (D ω) (Z ω + g • 1) := hp ω
      _ = _ := by rw [frozenVar_matrixPair_center (D ω) (Z ω) δ g]; ring
  have hsum : Integrable (fun ω =>
      2 * frozenVar_matrixPair (D ω - δ • 1) (Z ω) + 2 * g * Matrix.trace (D ω)) μ :=
    (hP.const_mul 2).add (hTD.const_mul (2 * g))
  have hint := integral_mono (Localization.cellMoment_integrable_frobSq hD)
    (hsum.add (hTZ.const_mul (2 * δ))) hp'
  dsimp only [Pi.add_apply] at hint
  rw [integral_add hsum (hTZ.const_mul (2 * δ)),
    integral_add (hP.const_mul 2) (hTD.const_mul (2 * g)), integral_const_mul,
    integral_const_mul, integral_const_mul, hmeanD, hmeanZ, mul_zero, add_zero] at hint
  rw [frozenVar_integral_center hTD (Localization.cellMoment_integrable_frobSq hD) δ, hmeanD]
  linarith only [hint]

end GMCExplicitDelta.Assembly
