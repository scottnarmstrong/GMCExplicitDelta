module

public import GMCExplicitDelta.Steps.AssemblyFrozen
public import GMCExplicitDelta.Steps.AssemblyGood
public import GMCExplicitDelta.Steps.AssemblyContraction

/-!
# Assembly: the frozen step (step R2)

`frozenStep`: at the model's disorder `δ = M.delta` and caps `(D, F)` satisfying the scalar
hypotheses that R4 supplies at `(δ_λ, λD, λF)` (`z_F < 1`, `𝔲_{12} < 1`, `θ_R > F`, `bad ≤ b_bad`,
`𝔰 > 0`, `0 < F ≤ min(D, 1)`), if `𝖯(k; D, F)` holds for all `k ≤ L`, then
`f_{L+h}(b_L) < t_⋆F = F_next` and `‖J^max(z + Q_{L+h}; b_L)‖_{32} ≤ U_h = D_next` for every `z`.

Proof (R2): G7 → G8 → G9 give the bad-response bound; L6 gives the per-scale inequality at every
observation scale; C8/C9 give `0 ≤ f_n ≤ F`, `f` nonincreasing; V1 gives `V_n ≤ F·vi`; V2 + V3 give the
variance recurrence; these are exactly the hypotheses of the abstract T2–T3 target
`terminal_lt_of_perScale`. The second claim is A6 with `k = h`.
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta.Assembly

open Contract

variable {d : ℕ}

/-- A Euclidean unit vector exists in dimension `d ≥ 1`. -/
theorem exists_vecNormSq_eq_one (hd : 1 ≤ d) : ∃ e : Homogenization.Vec d, vecNormSq e = 1 := by
  classical
  let i : Fin d := ⟨0, hd⟩
  refine ⟨Pi.single i 1, ?_⟩
  rw [vecNormSq, vecDot, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji]
    ring
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- `f_n ≤ F` for `n ≥ L` from `𝖯(L; D, F)` and C8. -/
theorem fMean_le_of_inductionP (M : SubdiffusiveProcess.Model.GMCModel d) {L : ℕ} {D F : ℝ}
    (hF : 0 ≤ F) (hP : InductionP M L D F) (n : ℕ) (hn : L ≤ n) : fMean M L n ≤ F := by
  obtain ⟨e, he⟩ := exists_vecNormSq_eq_one (d := d) (by have := M.shellPrefix.dimension; omega)
  have h := ((hP n hn 0).2.2 e he).2
  rw [lintegral_frozenJ_eq_fMean M L n 0 e he] at h
  exact (ENNReal.ofReal_le_ofReal_iff hF).mp h

/-- The variance recurrence of V4, `V_n ≤ ρ_v V_{n-ℓ_v} + c_v(f_{n-ℓ_v}² - f_n²)` for
`n ≥ L + 1 + ℓ_v`, from V2 and V3 with `t = 23/2`, `ℓ_v = 3` (`d = 2`) or `t = η_v`, `ℓ_v = 2`
(`d ≥ 3`). -/
theorem varV_recurrence (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) :
    ∀ n, L + 1 + ellV d ≤ n →
      varV M L n ≤ row.rhoV * varV M L (n - ellV d) +
        row.cV * (fMean M L (n - ellV d) ^ 2 - fMean M L n ^ 2) := by
  intro n hn
  have hl1 : 1 ≤ ellV d := by unfold ellV; split_ifs <;> norm_num
  have hk : L + 1 ≤ n - ellV d := by omega
  have hkn : n - ellV d < n := by omega
  have hsub : n - (n - ellV d) = ellV d := by omega
  obtain ⟨hX, hJ⟩ := cellAvgVar_le_parity hd M L (n - ellV d) n hk hkn.le
  rw [hsub] at hX hJ
  have hκ : (0 : ℝ) ≤ (2 : ℝ) ^ d / (3 : ℝ) ^ (d * ellV d) := by positivity
  by_cases h2 : d = 2
  · subst h2
    have hV := varV_le_centeredDecrement M L (n - ellV 2) n (by omega) hkn
      (t := 23 / 2) (by norm_num) hκ hX hJ
    have hρ : row.rhoV = (5 + 2 * ((23 / 2 : ℝ) + (23 / 2 : ℝ)⁻¹)) *
        ((2 : ℝ) ^ 2 / (3 : ℝ) ^ (2 * ellV 2)) := by
      simp only [Row.rhoV, ellV, ite_true]; norm_num
    have hc : row.cV = 1 + 2 / (23 / 2 : ℝ) := by
      simp only [Row.cV, ite_true]; norm_num
    rw [hρ, hc]
    exact hV
  · have hy : (0 : ℝ) < (row.young : ℝ) := by exact_mod_cast (hO.par2.2.2.2.2.2 h2).1
    have hV := varV_le_centeredDecrement M L (n - ellV d) n (by omega) hkn
      (t := (row.young : ℝ)) hy hκ hX hJ
    have hl : ellV d = 2 := by simp [ellV, h2]
    have hρ : row.rhoV = (5 + 2 * ((row.young : ℝ) + (row.young : ℝ)⁻¹)) *
        ((2 : ℝ) ^ d / (3 : ℝ) ^ (d * ellV d)) := by
      simp only [Row.rhoV, h2, ite_false, hl]
      rw [mul_comm d 2]
      ring
    have hc : row.cV = 1 + 2 / (row.young : ℝ) := by simp [Row.cV, h2]
    rw [hρ, hc]
    exact hV

/-- **R2 (frozen step).** -/
theorem frozenStep (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (M : SubdiffusiveProcess.Model.GMCModel d) {D F : ℝ} (hD : 0 < D) (hF : 0 < F) (hF1 : F ≤ 1)
    (hFD : F ≤ D) (hzF : row.zF M.delta < 1) (hu : frakU d row.historyCutoff D F < 1)
    (hθ : F < row.thetaR) (hbad : row.badCharge M.delta D F ≤ row.badBudget)
    (hbar : 0 < row.barrier D F) (L : ℕ) (hP : ∀ k ≤ L, InductionP M k D F) :
    fMean M L (L + row.h) < row.Fnext F ∧
      ∀ z : Homogenization.Vec d,
        paperENNRealLpNorm M.P.toMeasure 32 (normalizedDefect M L (cubeAt z (L + row.h))) ≤
          ENNReal.ofReal (row.Dnext D F) := by
  have hPL := hP L le_rfl
  -- G7 → G8 → G9: the bad-response bound
  have hG7 := excess_bound row hd hO M hD hF hFD L hP hzF hu
  have hG8 := badEvent_prob_le row M L hθ hF.le hG7
  have hBad := badResponseBound_holds row hd hO M hD hF hFD L hP hzF hu hθ hG8
  -- C8, C9: the frozen means
  obtain ⟨hf0, hanti⟩ := fMean_nonneg_antitone M L
  have hfF : ∀ n, L ≤ n → fMean M L n ≤ F := fun n hn => fMean_le_of_inductionP M hF.le hPL n hn
  -- V1: the initial variance bound
  have hV1 : ∀ n, L ≤ n → varV M L n ≤ F * vi D F := by
    intro n hn
    have h := varV_le_initial M L n hn hD.le hF.le (hPL n hn 0).2.1 (hfF n hn)
    have e : F * vi D F = 2 * F + 2 * D ^ 2 := by
      unfold vi; field_simp
    rw [e]; exact h
  -- V2 + V3 + V1: the hypotheses of V4
  have hVB : GMCContraction.VarBudget (fMean M L) (varV M L) L (ellV d) row.rhoV row.cV F
      (vi D F) :=
    { one_le := by unfold ellV; split_ifs <;> norm_num
      rho_nonneg := hO.var1.1.le
      rho_lt := hO.var1.2
      c_nonneg := by
        unfold Row.cV
        split_ifs with h2
        · norm_num
        · have : (0 : ℝ) < (row.young : ℝ) := by exact_mod_cast (hO.par2.2.2.2.2.2 h2).1
          positivity
      anti := fun a b _ hab => hanti a b hab
      f_nonneg := fun n _ => hf0 n
      f_le := hfF
      V_nonneg := fun n _ => varV_nonneg M L n
      V_le := hV1
      recur := varV_recurrence row hd hO M L }
  -- T2 + T3 with L6 at every observation scale
  refine ⟨terminal_lt_of_perScale row hd hO hD hF hF1
    (max_le hbad (by exact_mod_cast hO.par2.2.2.2.2.1.le)) hbar
    (fun a b _ hab => hanti a b hab) (fun n _ => hf0 n) hfF hVB
    (fun m' h1 h2 hf => perScaleIneq_holds row hd hO M L hP hBad m' h1 h2 hf), ?_⟩
  -- A6 with k = h
  intro z
  have hh : 1 ≤ row.h := by
    have h1 := hO.par1.2.2.2.1
    have h2 := hO.par1.2.2.2.2.1
    have : 2 ≤ row.g := le_trans (le_max_right _ _) h1
    omega
  exact (nativeCap_bound hd hO M hD hF hFD L hPL row.h hh z).1

end GMCExplicitDelta.Assembly
