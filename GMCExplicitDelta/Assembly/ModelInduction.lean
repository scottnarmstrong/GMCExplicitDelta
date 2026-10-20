module

public import GMCExplicitDelta.Contract.Conclusion
public import GMCExplicitDelta.Contract.Obligations

/-!
# Assembly: model vocabulary of the induction statement

Model-level objects of §1.2–1.6 used by the assembly of `cascade_of_obligations`
(step R5). Every definition is stated through the existing subdiffusive-process objects
(`normalizedDefect`, `aCutoffCoeffOnData`, `ahom`, `J`, `paperScalarProbeMaxOn`), never through a new
coefficient object:

* `cubeAt z n` is the cube `z + Q_n` of the main theorems (`translatedDomain z (originCube d n)`),
  `cellAt z R` the translate `z + R` of a triadic cube `R` (so the depth-`j` cells of `z + Q_n` are
  `cellAt z R`, `R ∈ descendantsAtDepth (originCube d n) j`).
* `frozenJ M m U p q` is `J(U, p, q; b_m)` with `b_m = a_m/ā_m`, written through `a_m` by the
  homogeneity identity C3: `J(U,p,q;a/s) = J(U, s^{-1/2}p, s^{1/2}q; a)`.
* `scaledDefect M m U s` is `J^max(U; a_m/s)`; `normalizedDefect M m U = scaledDefect M m U (ā_m)`
  (definitionally) is `J^max_m(U)`.
* `InductionP M m D F` is the induction statement `𝖯(m;D,F)` of §1.6, with exactly the conjuncts
  (measurability included) of `Contract.CascadeConclusion`, so that
  `CascadeConclusion M C₃₂ C_mean ↔ ∀ m, InductionP M m (C₃₂δ²) (C_meanδ²)` holds by `Iff.rfl`.
* `normShift M m = H_m = (m+1)τ² + log ā_m` (§1.4), and `freshNorm M L m = ā_L e^{-(m-L)τ²}`, the
  normalization for which `a_m/freshNorm M L m = b_L e^{Z_{L,m}}` (N2, the unshifted fresh coefficient
  of I6).
* `lamOf row δ = (δ/δ_*)²`, the disorder ratio `λ` of R4/R5.
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta.Assembly

variable {d : ℕ}

/-- The cube `z + Q_n` (§1.1), as in the main theorems. -/
abbrev cubeAt (z : Homogenization.Vec d) (n : ℕ) : Ch02.Domain d :=
  SubdiffusiveProcess.LambdaStability.translatedDomain z (originCube d (n : ℤ))

/-- The translate `z + R` of a triadic cube `R`. The depth-`j` cells of `z + Q_n` (§1.1) are
`cellAt z R` for `R ∈ descendantsAtDepth (originCube d n) j`. -/
abbrev cellAt (z : Homogenization.Vec d) (R : Homogenization.TriadicCube d) : Ch02.Domain d :=
  SubdiffusiveProcess.LambdaStability.translatedDomain z R

/-- `J(U, p, q; b_m)` for `b_m = a_m/ā_m` (§1.3–1.4), written through `a_m` by C3. -/
noncomputable def frozenJ (M : SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) (U : Ch02.Domain d)
    (p q : Homogenization.Vec d) (ω : SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  J U (aCutoffCoeffOnData M m ω U).toCoeffOn ((Real.sqrt (ahom M m))⁻¹ • p)
    (Real.sqrt (ahom M m) • q)

/-- `J^max(U; a_m/s) = sup_{|e|=1} J(U, s^{-1/2}e, s^{1/2}e; a_m)`, the normalized defect of `a_m` at an
arbitrary scalar normalization `s` (§1.3; C3). -/
noncomputable def scaledDefect (M : SubdiffusiveProcess.Model.GMCModel d) (m : ℕ)
    (U : Ch02.Domain d) (s : ℝ) (ω : SubdiffusiveProcess.Model.PotentialSample d) : ℝ≥0∞ :=
  paperScalarProbeMaxOn U (aCutoffCoeffOnData M m ω U).toCoeffOn s

theorem normalizedDefect_eq_scaledDefect (M : SubdiffusiveProcess.Model.GMCModel d) (m : ℕ)
    (U : Ch02.Domain d) : normalizedDefect M m U = scaledDefect M m U (ahom M m) :=
  rfl

/-- **The induction statement `𝖯(m;D,F)`** (§1.6): for every `n ≥ m`, every deterministic
`z` and every unit `e`, `‖J^max_m(z+Q_n)‖_{32} ≤ D` and `𝔼 J(z+Q_n, e, e; b_m) ≤ F`, together with the
measurability of both observables (the conjuncts of `Contract.CascadeConclusion`). -/
def InductionP (M : SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) (D F : ℝ) : Prop :=
  ∀ n : ℕ, m ≤ n → ∀ z : Homogenization.Vec d,
    Measurable (normalizedDefect M m (cubeAt z n)) ∧
    paperENNRealLpNorm M.P.toMeasure 32 (normalizedDefect M m (cubeAt z n)) ≤
      ENNReal.ofReal D ∧
    ∀ e : Homogenization.Vec d, vecNormSq e = 1 →
      Measurable (frozenJ M m (cubeAt z n) e e) ∧
      ∫⁻ ω, ENNReal.ofReal (frozenJ M m (cubeAt z n) e e ω) ∂M.P.toMeasure ≤ ENNReal.ofReal F

/-- The cascade conclusion is the induction statement at every cutoff, with the caps
`C₃₂δ²`, `C_meanδ²`. -/
theorem cascadeConclusion_iff_forall_inductionP (M : SubdiffusiveProcess.Model.GMCModel d)
    (C32 Cmean : ℝ) :
    Contract.CascadeConclusion M C32 Cmean ↔
      ∀ m, InductionP M m (C32 * M.delta ^ 2) (Cmean * M.delta ^ 2) :=
  Iff.rfl

/-- `H_m = (m+1)τ² + log ā_m`, so that `b_m = exp(∑_{k≤m} g_k - H_m)` (§1.4). -/
noncomputable def normShift (M : SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) : ℝ :=
  ((m : ℝ) + 1) * SubdiffusiveProcess.Model.tauSq M.P + Real.log (ahom M m)

/-- The unshifted fresh normalization `ā_L e^{-(m-L)τ²}`: `a_m/freshNorm M L m = b_L e^{Z_{L,m}}` with
`Z_{L,m} = ∑_{i=L+1}^m g_i` (N2, I6), and `ā_m = freshNorm M L m · e^{H_m - H_L}`. -/
noncomputable def freshNorm (M : SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ) : ℝ :=
  ahom M L * Real.exp (-(((m : ℝ) - L) * SubdiffusiveProcess.Model.tauSq M.P))

/-- The disorder ratio `λ = (δ/δ_*)²` of R4–R5. -/
noncomputable def lamOf (row : Contract.Row d) (δ : ℝ) : ℝ := (δ / (row.deltaStar : ℝ)) ^ 2

end GMCExplicitDelta.Assembly
