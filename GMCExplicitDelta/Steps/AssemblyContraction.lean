module

public import GMCExplicitDelta.Assembly.ModelEvents
public import GMCExplicitDelta.Contraction.SequencesBudget
public import GMCExplicitDelta.Proofs.Contraction.Haar
public import GMCExplicitDelta.Proofs.Contraction.Terminal
public import GMCExplicitDelta.Localization.PerScale

/-!
# Intermediate statements: Haar sums, the per-scale inequality and the terminal barrier (H12, L6, T2–T3)

Intermediate statements of the assembly of `cascade_of_obligations`. Each is proved in
`GMCExplicitDelta/Proofs/`.

* `haarB_sums` — H12, as pure statements about the contract constants `b_k = row.haarB k`.
* `perScaleIneq_holds` — L6 on the model, with the bad response (G9) as hypothesis.
* `terminal_lt_of_perScale` — T2 + T3 for abstract sequences: the summed per-scale inequality under
  the terminal hypothesis and the barrier contradiction, giving `f_{L+h} < t_⋆F`, from the sequence
  lemmas of `GMCExplicitDelta/Contraction/` (`T1_shift`, `T1_nu`, `T2_drop`, `VarBudget.sum_tail_le'`,
  `VarBudget.sum_full_le'`, `sq_defect_le`, `V5_split`, `T3_false`) and `haarB_sums`.
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta.Assembly

open Contract

variable {d : ℕ}

/-- **H12 (geometric tails and the Haar sums)**, for the contract's Haar multiplier coefficients
`b_k = row.haarB k`: `b_k ≥ 0`; the partial sums of `∑ b_k` are at most `S_b`; the partial sums of the
tail `∑_{k>K'} b_k` are at most `B_tail`; the partial sums of `∑_{k≥1} b_k√(k y_k/R)` are at most `S_d`;
and `T_g = ∑_{k>g} b_k u_s^k ≤ K_sρ_s^{g+1}/(1-ρ_s)`. -/
theorem haarB_sums (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations) :
    (∀ k, 0 ≤ row.haarB k) ∧
      (∀ N, ∑ k ∈ Finset.range N, row.haarB k ≤ row.Sb) ∧
      (∀ N, ∑ k ∈ Finset.Ioc row.Kprime N, row.haarB k ≤ row.Btail) ∧
      (∀ N, ∑ k ∈ Finset.Icc 1 N,
          row.haarB k * Real.sqrt ((k : ℝ) * row.yk k / (row.R : ℝ)) ≤ row.Sd) ∧
      row.Tg ≤ row.Ks * row.rhoS ^ (row.g + 1) / (1 - row.rhoS) :=
  haarB_sums_proof row hd hO

/-- **L6 (normalized per-scale inequality)** on the model. Assume `𝖯(k; D, F)` for `k ≤ L` and the
bad-response bound (the conclusion of G9, which carries the hypotheses of G7–G8). Then at every
observation scale `m' ∈ [L+g, L+h]` with `f_{m'} > 0`, the per-scale inequality holds for
`f = fMean M L`, `V = varV M L` and `bad = max(row.badCharge δ D F, 0)` (the bad term enters as `max(bad, 0)`: with a negative
`bad` the statement is false) (L4 with the matched pairs of L5:
planar `((1+f_{m'})e, e)` for `d = 2`, reciprocal `(√β_{m'} e, e/√β_{m'})` for `d ≥ 3`). -/
theorem perScaleIneq_holds (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (M : SubdiffusiveProcess.Model.GMCModel d) {D F : ℝ} (L : ℕ)
    (hP : ∀ k ≤ L, InductionP M k D F) (hBad : BadResponseBound row M L D F) (m' : ℕ)
    (hm1 : L + row.g ≤ m') (hm2 : m' ≤ L + row.h) (hf : 0 < fMean M L m') :
    PerScaleIneq row (fMean M L) (varV M L) L F (max (row.badCharge M.delta D F) 0) m' :=
  Localization.perScaleIneq_max row hd hO M L hP hBad (haarB_sums row hd hO).2.2.2.2 m' hm1 hf

/-- **T2 + T3 (summed inequality and barrier contradiction), abstract form.** Let `f, V` be real
sequences with `f` nonincreasing and `0 ≤ f ≤ F` on `[L, ∞)`, `V` satisfying the variance budget
hypotheses of V4 (`VarBudget` with `ℓ_v, ρ_v, c_v` of the row and `vi = vi D F`), and the per-scale
inequality at every `m' ∈ [L+g, L+h]` with `f_{m'} > 0`, with a bad term `bd ≤ b_bad`. If
`0 < F ≤ 1`, `D > 0` and the scalar barrier `𝔰(D, F) > 0`, then `f_{L+h} < t_⋆F`. -/
theorem terminal_lt_of_perScale (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ))
    (hO : row.Obligations) {D F bd : ℝ} (hD : 0 < D) (hF : 0 < F) (hF1 : F ≤ 1)
    (hbd : bd ≤ row.badBudget) (hbar : 0 < row.barrier D F) {f V : ℕ → ℝ} {L : ℕ}
    (hanti : ∀ a b, L ≤ a → a ≤ b → f b ≤ f a) (hf0 : ∀ n, L ≤ n → 0 ≤ f n)
    (hfF : ∀ n, L ≤ n → f n ≤ F)
    (hV : GMCContraction.VarBudget f V L (ellV d) row.rhoV row.cV F (vi D F))
    (hL6 : ∀ m', L + row.g ≤ m' → m' ≤ L + row.h → 0 < f m' → PerScaleIneq row f V L F bd m') :
    f (L + row.h) < row.Fnext F :=
  terminal_lt_of_perScale_proof row hd hO hD hF hF1 hbd hbar hanti hf0 hfF hV hL6

end GMCExplicitDelta.Assembly
