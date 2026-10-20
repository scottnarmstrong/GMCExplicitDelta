module

public import GMCExplicitDelta.Assembly.ModelFrozen
public import GMCExplicitDelta.Proofs.Normalization.All
public import GMCExplicitDelta.Proofs.FreshMean.Main
public import GMCExplicitDelta.Proofs.FreshInsertion.Seed
public import GMCExplicitDelta.Proofs.Observables.Extend
public import GMCExplicitDelta.Proofs.FreshInsertion.FreshNorm

/-!
# Intermediate statements: seeds, normalization drift, fresh insertion and extension to larger cubes

Intermediate statements of the assembly of `cascade_of_obligations`. Each is proved in
`GMCExplicitDelta/Proofs/`. Model vocabulary: `GMCExplicitDelta.Assembly`.
All contract constants are evaluated at the model's disorder `δ = M.delta`.

* `normSeed_bound`, `meanSeed_bound` — K2, K3 (cutoffs `m ≤ h - 1`).
* `normShift_drift` — N1/N2: `ā_m > 0`, `|H_m - H_k| ≤ κ_h(m-k)δ²`, `|H_m| ≤ κ_h(m+1)δ²`
  (`κ_h = 0` in `d = 2`).
* `freshNorm_return` — I6 for `b_L e^{Z_{L,L+h}} = a_{L+h}/freshNorm`, as used in I9.
* `scaledDefect_shift_le` — I7 (deterministic shift).
* `freshMean_return` — I8, as used in I9.
* `inductionBounds_extend` — R1 / C11(a): bounds at the cutoff scale for all translates give the
  bounds on every larger cube.
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta.Assembly

open Contract

variable {d : ℕ}

/-- **K2 (norm seed).** For `m ≤ h - 1`, every `n ≥ m` and `z`:
`‖J^max_m(z + Q_n)‖_{32} ≤ seed = ([𝐐^h x^{32}](x₀))^{1/32}` at `δ = M.delta`. -/
theorem normSeed_bound (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (M : SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) (hm : m + 1 ≤ row.h) :
    ∀ n, m ≤ n → ∀ z : Homogenization.Vec d,
      paperENNRealLpNorm M.P.toMeasure 32 (normalizedDefect M m (cubeAt z n)) ≤
        ENNReal.ofReal (row.seed M.delta) :=
  normSeed_bound_proof row hd hO M m hm

/-- **K3 (mean seed).** For `m ≤ h - 1`, every `n ≥ m`, `z` and unit `e`:
`𝔼 J(z + Q_n, e, e; b_m) ≤ meanseed` at `δ = M.delta`. -/
theorem meanSeed_bound (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (M : SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) (hm : m + 1 ≤ row.h) :
    ∀ n, m ≤ n → ∀ z e : Homogenization.Vec d, vecNormSq e = 1 →
      ∫⁻ ω, ENNReal.ofReal (frozenJ M m (cubeAt z n) e e ω) ∂M.P.toMeasure ≤
        ENNReal.ofReal (row.meanseed M.delta) :=
  meanSeed_bound_proof row hd hO M m hm

/-- **N1/N2 (drift of the actual normalization).** `ā_m > 0` for every `m`; for `k ≤ m`,
`|H_m - H_k| ≤ κ_h(m-k)δ²`; and `|H_m| ≤ κ_h(m+1)δ²`, where `κ_h = 0` for `d = 2` (C10: `H_m = 0`) and
`κ_h = κ` for `d ≥ 3` (N1 and S7: `τ² ≤ κδ²`). The numeric inputs O.src.* come from `hO`. -/
theorem normShift_drift (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (M : SubdiffusiveProcess.Model.GMCModel d) :
    (∀ m, 0 < ahom M m) ∧
      (∀ k m : ℕ, k ≤ m →
        |normShift M m - normShift M k| ≤ kappaH d * ((m : ℝ) - k) * M.delta ^ 2) ∧
      ∀ m : ℕ, |normShift M m| ≤ kappaH d * ((m : ℝ) + 1) * M.delta ^ 2 :=
  normShift_drift_proof row hd hO M

/-- **I6 (fresh norm return, unshifted), as used in I9.** Let `m = L + h`. If `f_m(b_L) ≤ F_next`,
`‖J^max(z + Q_m; b_L)‖_{32} ≤ D_next` for all `z`, and `0 < F_next ≤ D_next` (with
`F_next = row.Fnext F`, `D_next = row.Dnext D F`), then for every `z`,
`‖J^max(z + Q_m; b_Le^{Z_{L,m}})‖_{32} ≤ sym = (β_d^{32}𝓜)^{1/32}`, where
`b_Le^{Z_{L,m}} = a_m/freshNorm M L m` (N2). -/
theorem freshNorm_return (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (M : SubdiffusiveProcess.Model.GMCModel d) {D F : ℝ} (L : ℕ)
    (hpos : 0 < row.Fnext F) (hle : row.Fnext F ≤ row.Dnext D F)
    (hf : fMean M L (L + row.h) ≤ row.Fnext F)
    (hnorm : ∀ z : Homogenization.Vec d,
      paperENNRealLpNorm M.P.toMeasure 32 (normalizedDefect M L (cubeAt z (L + row.h))) ≤
        ENNReal.ofReal (row.Dnext D F)) :
    ∀ z : Homogenization.Vec d,
      paperENNRealLpNorm M.P.toMeasure 32
          (scaledDefect M (L + row.h) (cubeAt z (L + row.h)) (freshNorm M L (L + row.h))) ≤
        ENNReal.ofReal (row.sym M.delta D F) :=
  freshNorm_return_proof row hd hO M L hpos hle hf hnorm

/-- **I7 (deterministic shift).** If `s > 0`, `|c| ≤ γ`, `y ≥ 0` and `‖J^max(U; a_m/s)‖_{32} ≤ y`, then
`‖J^max(U; a_m/(se^c))‖_{32} ≤ Φ_γ(y)` (C3 and C7). -/
theorem scaledDefect_shift_le (M : SubdiffusiveProcess.Model.GMCModel d) (m : ℕ)
    (U : Ch02.Domain d) {s c γ y : ℝ} (hs : 0 < s) (hc : |c| ≤ γ) (hy : 0 ≤ y)
    (h : paperENNRealLpNorm M.P.toMeasure 32 (scaledDefect M m U s) ≤ ENNReal.ofReal y) :
    paperENNRealLpNorm M.P.toMeasure 32 (scaledDefect M m U (s * Real.exp c)) ≤
      ENNReal.ofReal (PhiMap γ y) :=
  scaledDefect_shift_le_proof M m U hs hc hy h

/-- **I8 (fresh mean return), as used in I9.** Let `m = L + h`. If `f_m(b_L) ≤ F_next = row.Fnext F`
(`F ≥ 0`), then for every `z` and unit `e`, `𝔼 J(z + Q_m, e, e; b_m) ≤ meanpost` at `δ = M.delta`
(`b_m = b_Le^{Z_{L,m} - c}`, N2, N3). -/
theorem freshMean_return (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (M : SubdiffusiveProcess.Model.GMCModel d) {F : ℝ} (hF : 0 ≤ F) (L : ℕ)
    (hf : fMean M L (L + row.h) ≤ row.Fnext F) :
    ∀ z e : Homogenization.Vec d, vecNormSq e = 1 →
      ∫⁻ ω, ENNReal.ofReal (frozenJ M (L + row.h) (cubeAt z (L + row.h)) e e ω) ∂M.P.toMeasure ≤
        ENNReal.ofReal (row.meanpost M.delta F) :=
  freshMean_return_proof row hd hO M hF L hf

/-- **R1 / C11(a) (translates and larger cubes).** If `‖J^max_m(z + Q_m)‖_{32} ≤ D` and
`𝔼 J(z + Q_m, e, e; b_m) ≤ F` for every `z` and unit `e`, then the same bounds hold on `z + Q_n` for
every `n ≥ m` (C2 subadditivity over the depth-`(n-m)` cells, Minkowski). -/
theorem inductionBounds_extend (M : SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) {D F : ℝ}
    (hD : ∀ z : Homogenization.Vec d,
      paperENNRealLpNorm M.P.toMeasure 32 (normalizedDefect M m (cubeAt z m)) ≤ ENNReal.ofReal D)
    (hF : ∀ z e : Homogenization.Vec d, vecNormSq e = 1 →
      ∫⁻ ω, ENNReal.ofReal (frozenJ M m (cubeAt z m) e e ω) ∂M.P.toMeasure ≤ ENNReal.ofReal F) :
    ∀ n, m ≤ n → ∀ z : Homogenization.Vec d,
      paperENNRealLpNorm M.P.toMeasure 32 (normalizedDefect M m (cubeAt z n)) ≤
          ENNReal.ofReal D ∧
        ∀ e : Homogenization.Vec d, vecNormSq e = 1 →
          ∫⁻ ω, ENNReal.ofReal (frozenJ M m (cubeAt z n) e e ω) ∂M.P.toMeasure ≤
            ENNReal.ofReal F :=
  inductionBounds_extend_proof M m hD hF

end GMCExplicitDelta.Assembly
