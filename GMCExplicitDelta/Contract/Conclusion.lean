module

public import SubdiffusiveProcess.Vocab.NormalizedDefect
public import SubdiffusiveProcess.LambdaStability.ScalarCarriers

/-!
# Contract layer: the conclusion of the cascade

`CascadeConclusion M C₃₂ C_mean` is the conclusion of the main theorems
`explicit_cascade_two/three/four`, quantified over the cutoff `m`, the scale `n ≥ m` and the
translation `z`, generalized over the dimension `d` and the two constants: for every cube `z + Q_n`
with `n ≥ m`, the normalized defect `Jmax_m(z + Q_n)` is measurable with
`‖Jmax_m(z + Q_n)‖_{L^32} ≤ C₃₂ δ²`, and for every Euclidean unit vector `e` the directional energy
`J(z + Q_n, ā_m^{-1/2} e, ā_m^{1/2} e; a_m)` is measurable with mean `≤ C_mean δ²` (step T0).

`cascadeConclusion_two_iff` (and three, four) unfold it at the literals of the main theorems, so that
each main theorem follows by applying the unfolded conclusion to its `m n hmn z`.
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta.Contract

/-- The conclusion of the main theorems, generalized over `d` and the constants `C₃₂, C_mean`
(step T0). -/
def CascadeConclusion {d : ℕ} (M : SubdiffusiveProcess.Model.GMCModel d) (C32 Cmean : ℝ) :
    Prop :=
  ∀ m n : ℕ, m ≤ n → ∀ z : Homogenization.Vec d,
    Measurable (normalizedDefect M m
        (SubdiffusiveProcess.LambdaStability.translatedDomain z (originCube d (n : ℤ)))) ∧
    paperENNRealLpNorm M.P.toMeasure 32
        (normalizedDefect M m
          (SubdiffusiveProcess.LambdaStability.translatedDomain z (originCube d (n : ℤ)))) ≤
      ENNReal.ofReal (C32 * M.delta ^ 2) ∧
    ∀ e : Homogenization.Vec d, vecNormSq e = 1 →
      Measurable (fun ω => J (SubdiffusiveProcess.LambdaStability.translatedDomain z
            (originCube d (n : ℤ)))
          (aCutoffCoeffOnData M m ω
            (SubdiffusiveProcess.LambdaStability.translatedDomain z
              (originCube d (n : ℤ)))).toCoeffOn
          ((Real.sqrt (ahom M m))⁻¹ • e) (Real.sqrt (ahom M m) • e)) ∧
      ∫⁻ ω, ENNReal.ofReal
          (J (SubdiffusiveProcess.LambdaStability.translatedDomain z (originCube d (n : ℤ)))
            (aCutoffCoeffOnData M m ω
              (SubdiffusiveProcess.LambdaStability.translatedDomain z
                (originCube d (n : ℤ)))).toCoeffOn
            ((Real.sqrt (ahom M m))⁻¹ • e) (Real.sqrt (ahom M m) • e)) ∂M.P.toMeasure ≤
        ENNReal.ofReal (Cmean * M.delta ^ 2)

/-- The `d = 2` cascade conclusion at the constants of `explicit_cascade_two`, unfolded to the
root's statement body. -/
theorem cascadeConclusion_two_iff (M : SubdiffusiveProcess.Model.GMCModel 2) :
    CascadeConclusion M (23138371504 / 53772889) (230590996 / 53772889) ↔
      ∀ m n : ℕ, m ≤ n → ∀ z : Homogenization.Vec 2,
        Measurable (normalizedDefect M m
            (SubdiffusiveProcess.LambdaStability.translatedDomain z (originCube 2 (n : ℤ)))) ∧
        paperENNRealLpNorm M.P.toMeasure 32
            (normalizedDefect M m
              (SubdiffusiveProcess.LambdaStability.translatedDomain z (originCube 2 (n : ℤ)))) ≤
          ENNReal.ofReal (23138371504 / 53772889 * M.delta ^ 2) ∧
        ∀ e : Homogenization.Vec 2, vecNormSq e = 1 →
          Measurable (fun ω => J (SubdiffusiveProcess.LambdaStability.translatedDomain z
                (originCube 2 (n : ℤ)))
              (aCutoffCoeffOnData M m ω
                (SubdiffusiveProcess.LambdaStability.translatedDomain z
                  (originCube 2 (n : ℤ)))).toCoeffOn
              ((Real.sqrt (ahom M m))⁻¹ • e) (Real.sqrt (ahom M m) • e)) ∧
          ∫⁻ ω, ENNReal.ofReal
              (J (SubdiffusiveProcess.LambdaStability.translatedDomain z (originCube 2 (n : ℤ)))
                (aCutoffCoeffOnData M m ω
                  (SubdiffusiveProcess.LambdaStability.translatedDomain z
                    (originCube 2 (n : ℤ)))).toCoeffOn
                ((Real.sqrt (ahom M m))⁻¹ • e) (Real.sqrt (ahom M m) • e)) ∂M.P.toMeasure ≤
            ENNReal.ofReal (230590996 / 53772889 * M.delta ^ 2) :=
  Iff.rfl

/-- The `d = 3` cascade conclusion at the constants of `explicit_cascade_three`, unfolded. -/
theorem cascadeConclusion_three_iff (M : SubdiffusiveProcess.Model.GMCModel 3) :
    CascadeConclusion M (89475125 / 1186923) (17849411 / 3560769) ↔
      ∀ m n : ℕ, m ≤ n → ∀ z : Homogenization.Vec 3,
        Measurable (normalizedDefect M m
            (SubdiffusiveProcess.LambdaStability.translatedDomain z (originCube 3 (n : ℤ)))) ∧
        paperENNRealLpNorm M.P.toMeasure 32
            (normalizedDefect M m
              (SubdiffusiveProcess.LambdaStability.translatedDomain z (originCube 3 (n : ℤ)))) ≤
          ENNReal.ofReal (89475125 / 1186923 * M.delta ^ 2) ∧
        ∀ e : Homogenization.Vec 3, vecNormSq e = 1 →
          Measurable (fun ω => J (SubdiffusiveProcess.LambdaStability.translatedDomain z
                (originCube 3 (n : ℤ)))
              (aCutoffCoeffOnData M m ω
                (SubdiffusiveProcess.LambdaStability.translatedDomain z
                  (originCube 3 (n : ℤ)))).toCoeffOn
              ((Real.sqrt (ahom M m))⁻¹ • e) (Real.sqrt (ahom M m) • e)) ∧
          ∫⁻ ω, ENNReal.ofReal
              (J (SubdiffusiveProcess.LambdaStability.translatedDomain z (originCube 3 (n : ℤ)))
                (aCutoffCoeffOnData M m ω
                  (SubdiffusiveProcess.LambdaStability.translatedDomain z
                    (originCube 3 (n : ℤ)))).toCoeffOn
                ((Real.sqrt (ahom M m))⁻¹ • e) (Real.sqrt (ahom M m) • e)) ∂M.P.toMeasure ≤
            ENNReal.ofReal (17849411 / 3560769 * M.delta ^ 2) :=
  Iff.rfl

/-- The `d = 4` cascade conclusion at the constants of `explicit_cascade_four`, unfolded. -/
theorem cascadeConclusion_four_iff (M : SubdiffusiveProcess.Model.GMCModel 4) :
    CascadeConclusion M (5918767600 / 61606801) (423596800 / 61606801) ↔
      ∀ m n : ℕ, m ≤ n → ∀ z : Homogenization.Vec 4,
        Measurable (normalizedDefect M m
            (SubdiffusiveProcess.LambdaStability.translatedDomain z (originCube 4 (n : ℤ)))) ∧
        paperENNRealLpNorm M.P.toMeasure 32
            (normalizedDefect M m
              (SubdiffusiveProcess.LambdaStability.translatedDomain z (originCube 4 (n : ℤ)))) ≤
          ENNReal.ofReal (5918767600 / 61606801 * M.delta ^ 2) ∧
        ∀ e : Homogenization.Vec 4, vecNormSq e = 1 →
          Measurable (fun ω => J (SubdiffusiveProcess.LambdaStability.translatedDomain z
                (originCube 4 (n : ℤ)))
              (aCutoffCoeffOnData M m ω
                (SubdiffusiveProcess.LambdaStability.translatedDomain z
                  (originCube 4 (n : ℤ)))).toCoeffOn
              ((Real.sqrt (ahom M m))⁻¹ • e) (Real.sqrt (ahom M m) • e)) ∧
          ∫⁻ ω, ENNReal.ofReal
              (J (SubdiffusiveProcess.LambdaStability.translatedDomain z (originCube 4 (n : ℤ)))
                (aCutoffCoeffOnData M m ω
                  (SubdiffusiveProcess.LambdaStability.translatedDomain z
                    (originCube 4 (n : ℤ)))).toCoeffOn
                ((Real.sqrt (ahom M m))⁻¹ • e) (Real.sqrt (ahom M m) • e)) ∂M.P.toMeasure ≤
            ENNReal.ofReal (423596800 / 61606801 * M.delta ^ 2) :=
  Iff.rfl

end GMCExplicitDelta.Contract
