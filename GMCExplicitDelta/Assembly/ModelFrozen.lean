module

public import GMCExplicitDelta.Assembly.ModelInduction
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Assembly: frozen quantities of the coefficient `b_L`

§1.3, §1.5, V2. Fix a cutoff `L` and freeze `b_L = a_L/ā_L`.

* `frozenX M L U = X_U(b_L) = ā_L⁻¹ · 𝐚(U; a_L)` and `frozenY M L U = Y_U(b_L) = ā_L · 𝐚_*(U; a_L)⁻¹`
  (C3: `X_U(λb) = λX_U(b)`, `Y_U(λb) = λ⁻¹Y_U(b)`), with `aMatrix`, `aStarMatrix` of the
  subdiffusive-process vocabulary; `frozenDefect = 𝓙(U;b_L) = (X+Y)/2 - I`.
* `alphaMean M L n = α_n`, `betaMean M L n = β_n`: the scalars with `𝔼X_n = α_nI`, `𝔼Y_n = β_nI`
  (C8), defined as normalized traces `d⁻¹ 𝔼 tr X_n`, `d⁻¹ 𝔼 tr Y_n` (so no isotropy is built into the
  definitions); `fMean = f_n = (α_n + β_n - 2)/2`.
* `varV = V_n`, `varW = W_n` (§1.5), with `frobSq A = ‖A‖_F²`.
* `cellAvg n k A` is the average of `A` over the scale-`k` cells of `Q_n`; `cellAvgVar`,
  `cellAvgDefectVar` are the stacked centered variances of those averages in the hypotheses of V2,
  normalized exactly as `V_k`, `W_k` (`1/(𝔑d)` with `𝔑 = 1` for `d = 2`, `𝔑 = 2` for `d ≥ 3`).

Here `Q_n = cubeAt 0 n`. Expectations are Bochner integrals against `M.P`.
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta.Assembly

variable {d : ℕ}

/-- `X_U(b_L) = 𝐚(U; b_L) = ā_L⁻¹ 𝐚(U; a_L)` (§1.3, C3). -/
noncomputable def frozenX (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) : Homogenization.Mat d :=
  (ahom M L)⁻¹ • aMatrix U (aCutoffCoeffOnData M L ω U).toCoeffOn

/-- `Y_U(b_L) = 𝐚_*(U; b_L)⁻¹ = ā_L 𝐚_*(U; a_L)⁻¹` (§1.3, C3). -/
noncomputable def frozenY (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) : Homogenization.Mat d :=
  ahom M L • (aStarMatrix U (aCutoffCoeffOnData M L ω U).toCoeffOn)⁻¹

/-- The defect matrix `𝓙(U; b_L) = (X_U + Y_U)/2 - I` (§1.3). -/
noncomputable def frozenDefect (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (U : Ch02.Domain d) (ω : SubdiffusiveProcess.Model.PotentialSample d) : Homogenization.Mat d :=
  (1 / 2 : ℝ) • (frozenX M L U ω + frozenY M L U ω) - 1

/-- The squared Frobenius norm `‖A‖_F² = ∑_{ij} A_{ij}²`. -/
noncomputable def frobSq (A : Homogenization.Mat d) : ℝ := ∑ i, ∑ j, A i j ^ 2

/-- `α_n = d⁻¹ 𝔼 tr X_n` (§1.5; `𝔼X_n = α_nI` by C8). -/
noncomputable def alphaMean (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) : ℝ :=
  (d : ℝ)⁻¹ * ∫ ω, Matrix.trace (frozenX M L (cubeAt 0 n) ω) ∂M.P.toMeasure

/-- `β_n = d⁻¹ 𝔼 tr Y_n` (§1.5; `𝔼Y_n = β_nI` by C8). -/
noncomputable def betaMean (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) : ℝ :=
  (d : ℝ)⁻¹ * ∫ ω, Matrix.trace (frozenY M L (cubeAt 0 n) ω) ∂M.P.toMeasure

/-- The frozen mean `f_n = (α_n + β_n - 2)/2 = 𝔼 J(Q_n, e, e; b_L)` (§1.5; the last identity is C8). -/
noncomputable def fMean (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) : ℝ :=
  (alphaMean M L n + betaMean M L n) / 2 - 1

/-- The frozen variance `V_n` (§1.5): `½𝔼‖Y_n - β_nI‖_F²` for `d = 2`,
`(2d)⁻¹𝔼[‖X_n - α_nI‖_F² + ‖Y_n - β_nI‖_F²]` for `d ≥ 3`. -/
noncomputable def varV (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) : ℝ :=
  if d = 2 then
    (1 / 2) * ∫ ω, frobSq (frozenY M L (cubeAt 0 n) ω - betaMean M L n • (1 : Homogenization.Mat d))
      ∂M.P.toMeasure
  else
    (1 / (2 * (d : ℝ))) * ∫ ω,
      (frobSq (frozenX M L (cubeAt 0 n) ω - alphaMean M L n • (1 : Homogenization.Mat d)) +
        frobSq (frozenY M L (cubeAt 0 n) ω - betaMean M L n • (1 : Homogenization.Mat d)))
      ∂M.P.toMeasure

/-- `W_n = d⁻¹𝔼‖𝓙(Q_n;b_L) - f_nI‖_F²` (§1.5). -/
noncomputable def varW (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) : ℝ :=
  (d : ℝ)⁻¹ * ∫ ω, frobSq (frozenDefect M L (cubeAt 0 n) ω - fMean M L n • (1 : Homogenization.Mat d))
    ∂M.P.toMeasure

/-- The average of a matrix observable over the scale-`k` cells `V_i` of `Q_n` (V2):
`N⁻¹∑_i A(V_i)`, `N = 3^{d(n-k)}`. -/
noncomputable def cellAvg (n k : ℕ) (A : Ch02.Domain d → Homogenization.Mat d) :
    Homogenization.Mat d :=
  ((descendantsAtScale (originCube d (n : ℤ)) (k : ℤ)).card : ℝ)⁻¹ •
    ∑ R ∈ descendantsAtScale (originCube d (n : ℤ)) (k : ℤ), A (cellAt 0 R)

/-- The stacked centered variance of the scale-`k` cell averages in V2:
`(𝔑d)⁻¹𝔼‖avg_i(𝐗_k(V_i) - 𝔼𝐗_k)‖_F²` with `𝐗 = Y` (`d = 2`) or `𝐗 = (X, Y)` (`d ≥ 3`), centered at
`𝔼X_k = α_kI`, `𝔼Y_k = β_kI`. -/
noncomputable def cellAvgVar (M : SubdiffusiveProcess.Model.GMCModel d) (L n k : ℕ) : ℝ :=
  if d = 2 then
    (1 / 2) * ∫ ω, frobSq (cellAvg n k (fun U => frozenY M L U ω) -
        betaMean M L k • (1 : Homogenization.Mat d)) ∂M.P.toMeasure
  else
    (1 / (2 * (d : ℝ))) * ∫ ω,
      (frobSq (cellAvg n k (fun U => frozenX M L U ω) -
          alphaMean M L k • (1 : Homogenization.Mat d)) +
        frobSq (cellAvg n k (fun U => frozenY M L U ω) -
          betaMean M L k • (1 : Homogenization.Mat d))) ∂M.P.toMeasure

/-- The centered variance of the scale-`k` cell average of the defect matrix in V2:
`d⁻¹𝔼‖avg_i(𝓙(V_i) - f_kI)‖_F²`. -/
noncomputable def cellAvgDefectVar (M : SubdiffusiveProcess.Model.GMCModel d) (L n k : ℕ) : ℝ :=
  (d : ℝ)⁻¹ * ∫ ω, frobSq (cellAvg n k (fun U => frozenDefect M L U ω) -
      fMean M L k • (1 : Homogenization.Mat d)) ∂M.P.toMeasure

theorem frobSq_nonneg (A : Homogenization.Mat d) : 0 ≤ frobSq A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem varV_nonneg (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) : 0 ≤ varV M L n := by
  unfold varV
  split_ifs
  · exact mul_nonneg (by norm_num) (MeasureTheory.integral_nonneg fun _ => frobSq_nonneg _)
  · exact mul_nonneg (by positivity) (MeasureTheory.integral_nonneg fun _ =>
      add_nonneg (frobSq_nonneg _) (frobSq_nonneg _))

end GMCExplicitDelta.Assembly
