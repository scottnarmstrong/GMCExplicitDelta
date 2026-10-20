module

public import GMCExplicitDelta.StatementProofs.ExplicitCascadeTwo
public import SubdiffusiveProcess.Vocab.NormalizedDefect
public import SubdiffusiveProcess.LambdaStability.ScalarCarriers

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta

/-- Explicit cutoff-uniform coarse-graining cascade in dimension two.

For every model with `δ ≤ .36665`, every cutoff `m`, every cube `z + Q_n` with `n ≥ m`
and every Euclidean unit vector `e`, the normalized defect `Jmax_m(z + Q_n)` of `a_m / ā_m` and the
directional energy are measurable functions of the environment, and
`‖Jmax_m(z + Q_n)‖_{L^32} ≤ C₃₂ δ²` and `E J(z + Q_n, ā_m^{-1/2} e, ā_m^{1/2} e; a_m) ≤ C_mean δ²`,
with `C₃₂ = 23138371504/53772889` and `C_mean = 230590996/53772889`. -/
theorem explicit_cascade_two (M : SubdiffusiveProcess.Model.GMCModel 2)
    (hδ : M.delta ≤ 36665 / 100000) (m n : ℕ) (hmn : m ≤ n) (z : Homogenization.Vec 2) :
    Measurable (normalizedDefect M m
        (SubdiffusiveProcess.LambdaStability.translatedDomain z (originCube 2 (n : ℤ)))) ∧
    paperENNRealLpNorm M.P.toMeasure 32
        (normalizedDefect M m
          (SubdiffusiveProcess.LambdaStability.translatedDomain z (originCube 2 (n : ℤ)))) ≤
      ENNReal.ofReal (23138371504 / 53772889 * M.delta ^ 2) ∧
    ∀ e : Homogenization.Vec 2, vecNormSq e = 1 →
      Measurable (fun ω => J (SubdiffusiveProcess.LambdaStability.translatedDomain z (originCube 2 (n : ℤ)))
          (aCutoffCoeffOnData M m ω
            (SubdiffusiveProcess.LambdaStability.translatedDomain z (originCube 2 (n : ℤ)))).toCoeffOn
          ((Real.sqrt (ahom M m))⁻¹ • e) (Real.sqrt (ahom M m) • e)) ∧
      ∫⁻ ω, ENNReal.ofReal
          (J (SubdiffusiveProcess.LambdaStability.translatedDomain z (originCube 2 (n : ℤ)))
            (aCutoffCoeffOnData M m ω
              (SubdiffusiveProcess.LambdaStability.translatedDomain z
                (originCube 2 (n : ℤ)))).toCoeffOn
            ((Real.sqrt (ahom M m))⁻¹ • e) (Real.sqrt (ahom M m) • e)) ∂M.P.toMeasure ≤
        ENNReal.ofReal (230590996 / 53772889 * M.delta ^ 2) :=
  by exact GMCExplicitDelta.StatementProofs.explicit_cascade_two

end GMCExplicitDelta
