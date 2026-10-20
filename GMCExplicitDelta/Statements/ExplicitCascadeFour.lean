module

public import GMCExplicitDelta.StatementProofs.ExplicitCascadeFour
public import SubdiffusiveProcess.Vocab.NormalizedDefect
public import SubdiffusiveProcess.LambdaStability.ScalarCarriers

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta

/-- Explicit cutoff-uniform coarse-graining cascade in dimension four.

For every model with `δ ≤ .15698`, every cutoff `m`, every cube `z + Q_n` with `n ≥ m`
and every Euclidean unit vector `e`, the normalized defect `Jmax_m(z + Q_n)` of `a_m / ā_m` and the
directional energy are measurable functions of the environment, and
`‖Jmax_m(z + Q_n)‖_{L^32} ≤ C₃₂ δ²` and `E J(z + Q_n, ā_m^{-1/2} e, ā_m^{1/2} e; a_m) ≤ C_mean δ²`,
with `C₃₂ = 5918767600/61606801` and `C_mean = 423596800/61606801`. -/
theorem explicit_cascade_four (M : SubdiffusiveProcess.Model.GMCModel 4)
    (hδ : M.delta ≤ 15698 / 100000) (m n : ℕ) (hmn : m ≤ n) (z : Homogenization.Vec 4) :
    Measurable (normalizedDefect M m
        (SubdiffusiveProcess.LambdaStability.translatedDomain z (originCube 4 (n : ℤ)))) ∧
    paperENNRealLpNorm M.P.toMeasure 32
        (normalizedDefect M m
          (SubdiffusiveProcess.LambdaStability.translatedDomain z (originCube 4 (n : ℤ)))) ≤
      ENNReal.ofReal (5918767600 / 61606801 * M.delta ^ 2) ∧
    ∀ e : Homogenization.Vec 4, vecNormSq e = 1 →
      Measurable (fun ω => J (SubdiffusiveProcess.LambdaStability.translatedDomain z (originCube 4 (n : ℤ)))
          (aCutoffCoeffOnData M m ω
            (SubdiffusiveProcess.LambdaStability.translatedDomain z (originCube 4 (n : ℤ)))).toCoeffOn
          ((Real.sqrt (ahom M m))⁻¹ • e) (Real.sqrt (ahom M m) • e)) ∧
      ∫⁻ ω, ENNReal.ofReal
          (J (SubdiffusiveProcess.LambdaStability.translatedDomain z (originCube 4 (n : ℤ)))
            (aCutoffCoeffOnData M m ω
              (SubdiffusiveProcess.LambdaStability.translatedDomain z
                (originCube 4 (n : ℤ)))).toCoeffOn
            ((Real.sqrt (ahom M m))⁻¹ • e) (Real.sqrt (ahom M m) • e)) ∂M.P.toMeasure ≤
        ENNReal.ofReal (423596800 / 61606801 * M.delta ^ 2) :=
  by exact GMCExplicitDelta.StatementProofs.explicit_cascade_four

end GMCExplicitDelta
