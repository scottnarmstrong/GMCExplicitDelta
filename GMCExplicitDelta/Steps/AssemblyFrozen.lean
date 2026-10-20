module

public import GMCExplicitDelta.Assembly.ModelFrozen
public import GMCExplicitDelta.Proofs.Observables.Measurable
public import GMCExplicitDelta.Proofs.Observables.Mean
public import GMCExplicitDelta.Proofs.Variance.Isotropy
public import GMCExplicitDelta.Proofs.NativeCaps.Native
public import GMCExplicitDelta.Proofs.Variance.Initial
public import GMCExplicitDelta.Proofs.Variance.CenteredDecrement
public import GMCExplicitDelta.Proofs.Variance.Parity

/-!
# Intermediate statements: measurability, isotropy, monotonicity, variance and native caps of the frozen coefficient

Intermediate statements of the assembly of `cascade_of_obligations`. Each is proved in
`GMCExplicitDelta/Proofs/`. Model vocabulary: `GMCExplicitDelta.Assembly`
(`Assembly/ModelInduction.lean`, `Assembly/ModelFrozen.lean`).

* `measurable_cascadeObservables` — measurability of `J^max(U; a_m/s)` and of every fixed probe
  `J(U,p,q;a_m)` (needed for the measurability conjuncts of `𝖯(m)`).
* `lintegral_frozenJ_eq_fMean` — C8 (with stationarity): `𝔼 J(z+Q_n, e, e; b_L) = f_n`.
* `fMean_nonneg_antitone` — C9: `f_n ≥ 0`, `f_n` nonincreasing.
* `varV_le_initial` — V1.
* `varV_le_centeredDecrement` — V2.
* `cellAvgVar_le_parity` — V3 (`κ_v = 2^d 3^{-d(n-k)}` for `k ≥ L+1`).
* `nativeCap_bound` — A6.
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta.Assembly

open Contract

variable {d : ℕ}

/-- **Measurability of the cascade observables.** For every cutoff `m`, domain `U` and scalar `s`,
`J^max(U; a_m/s)` is measurable, and so is every fixed probe `ω ↦ J(U, p, q; a_m)`. (For `s = ā_m` and
`(p, q) = (ā_m^{-1/2}e, ā_m^{1/2}e)` these are the observables of `𝖯(m)`.) -/
theorem measurable_cascadeObservables (M : SubdiffusiveProcess.Model.GMCModel d) (m : ℕ)
    (U : Ch02.Domain d) :
    (∀ s : ℝ, Measurable (scaledDefect M m U s)) ∧
      ∀ p q : Homogenization.Vec d,
        Measurable (fun ω => J U (aCutoffCoeffOnData M m ω U).toCoeffOn p q) :=
  measurable_cascadeObservables_proof M m U

/-- **C8 (isotropy) with stationarity.** For every cutoff `L`, scale `n`, translation `z` and unit `e`,
`𝔼 J(z + Q_n, e, e; b_L) = f_n` (in `ℝ≥0∞`, `J ≥ 0`). -/
theorem lintegral_frozenJ_eq_fMean (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    (z e : Homogenization.Vec d) (he : vecNormSq e = 1) :
    ∫⁻ ω, ENNReal.ofReal (frozenJ M L (cubeAt z n) e e ω) ∂M.P.toMeasure =
      ENNReal.ofReal (fMean M L n) :=
  lintegral_frozenJ_eq_fMean_proof M L n z e he

/-- **C9 (annealed normalization).** For fixed `L`, `f_n ≥ 0` for every `n` and `n ↦ f_n` is
nonincreasing. -/
theorem fMean_nonneg_antitone (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) :
    (∀ n, 0 ≤ fMean M L n) ∧ ∀ a b, a ≤ b → fMean M L b ≤ fMean M L a :=
  fMean_nonneg_antitone_proof M L

/-- **V1 (initial variance bound, any finite `D`).** If `‖J^max(Q_n; b_L)‖_{32} ≤ D` and `f_n ≤ F`
(`D, F ≥ 0`, `n ≥ L`), then `V_n ≤ 2F + 2D²`. -/
theorem varV_le_initial (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) (hLn : L ≤ n)
    {D F : ℝ} (hD : 0 ≤ D) (hF : 0 ≤ F)
    (hJ : paperENNRealLpNorm M.P.toMeasure 32 (normalizedDefect M L (cubeAt 0 n)) ≤
      ENNReal.ofReal D)
    (hf : fMean M L n ≤ F) :
    varV M L n ≤ 2 * F + 2 * D ^ 2 :=
  varV_le_initial_proof M L n hLn hD hF hJ hf

/-- **V2 (centered decrement recurrence).** Let `L ≤ k < n`. If the stacked centered averages over
the scale-`k` cells of `Q_n` satisfy `cellAvgVar ≤ κ_v V_k` and `cellAvgDefectVar ≤ κ_v W_k`, then for
every `t > 0`, `V_n ≤ [5 + 2(t + t⁻¹)]κ_v V_k + (1 + 2/t)(f_k² - f_n²)`. -/
theorem varV_le_centeredDecrement (M : SubdiffusiveProcess.Model.GMCModel d) (L k n : ℕ)
    (hLk : L ≤ k) (hkn : k < n) {κv t : ℝ} (ht : 0 < t) (hκ : 0 ≤ κv)
    (hX : cellAvgVar M L n k ≤ κv * varV M L k)
    (hJ : cellAvgDefectVar M L n k ≤ κv * varW M L k) :
    varV M L n ≤ (5 + 2 * (t + t⁻¹)) * κv * varV M L k +
      (1 + 2 / t) * (fMean M L k ^ 2 - fMean M L n ^ 2) :=
  varV_le_centeredDecrement_proof M L k n hLk hkn ht hκ hX hJ

/-- **V3 (parity colouring above the cutoff).** For `d ∈ {2,3,4}` and `L + 1 ≤ k ≤ n`, the hypotheses
of V2 hold with `κ_v = 2^d 3^{-d(n-k)}`. -/
theorem cellAvgVar_le_parity (hd : d ∈ ({2, 3, 4} : Finset ℕ))
    (M : SubdiffusiveProcess.Model.GMCModel d) (L k n : ℕ) (hk : L + 1 ≤ k) (hkn : k ≤ n) :
    cellAvgVar M L n k ≤ (2 : ℝ) ^ d / (3 : ℝ) ^ (d * (n - k)) * varV M L k ∧
      cellAvgDefectVar M L n k ≤ (2 : ℝ) ^ d / (3 : ℝ) ^ (d * (n - k)) * varW M L k :=
  cellAvgVar_le_parity_proof hd M L k n hk hkn

/-- **A6 (native caps of the frozen coefficient).** Assume `𝖯(L; D, F)` with `0 < F ≤ D`. Then for
every `k ≥ 1` and `z`: `‖J^max(z + Q_{L+k}; b_L)‖_{32} ≤ U_k` and
`‖(J^max(z + Q_{L+k}; b_L) - F)_+‖_{32} ≤ D𝔲_k`, with `U_k = nativeCap d k D F`,
`𝔲_k = frakU d k D F`. -/
theorem nativeCap_bound {row : Row d} (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (M : SubdiffusiveProcess.Model.GMCModel d) {D F : ℝ} (hD : 0 < D) (hF : 0 < F) (hFD : F ≤ D)
    (L : ℕ) (hP : InductionP M L D F) :
    ∀ k, 1 ≤ k → ∀ z : Homogenization.Vec d,
      paperENNRealLpNorm M.P.toMeasure 32 (normalizedDefect M L (cubeAt z (L + k))) ≤
          ENNReal.ofReal (nativeCap d k D F) ∧
        paperENNRealLpNorm M.P.toMeasure 32
            (fun ω => normalizedDefect M L (cubeAt z (L + k)) ω - ENNReal.ofReal F) ≤
          ENNReal.ofReal (D * frakU d k D F) :=
  nativeCap_bound_proof hd hO M hD hF hFD L hP

end GMCExplicitDelta.Assembly
