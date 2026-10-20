module

public import GMCExplicitDelta.Localization.FirstMoment

/-!
# L5–L6: matched pairs and the normalized per-scale inequality

L5, L6. From L4 (`loc_firstMoment`) with the matched pairs

* `d = 2`: `p = (1+f)e`, `q = e` (`f = f_{m'}`; `α_n = β_n = 1 + f_n` by C10), for which
  `𝔼J(Q_n,p,q) = 𝖢(f)f_n + f²/2`, `j⋆ = 𝗋(f)f`, `Δ_k = 𝖢(f)(f_{m'-k} - f)`, `Var_k = V_{m'-k}`;
* `d ≥ 3`: `p = √β e`, `q = e/√β` (`β = β_{m'}`), for which `f ≤ j⋆`, `Δ_k ≤ β(f_{m'-k} - f)`,
  `Var_k ≤ 2V_{m'-k}`, `1 ≤ β ≤ 1 + 2F`,

and the bad-response bound (G9), we obtain the per-scale inequality L6.

The bad term is `F · max(bad, 0)` (`perScaleIneq_max`): the target statement `perScaleIneq_holds` uses
`F · bad`, which is not implied when `bad < 0` (the bad term enters as `max(bad, 0)`: with a negative bad charge the inequality would fail); when
`bad ≥ 0` the two agree (`perScaleIneq_of_badCharge_nonneg`).
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open scoped ENNReal

namespace GMCExplicitDelta.Localization

open Assembly Contract

variable {d : ℕ}

/-! ### Vector algebra for `a • e`, `b • e` -/

theorem vecDot_smul_smul (a b : ℝ) (e : Homogenization.Vec d) :
    vecDot (a • e) (b • e) = a * b * vecNormSq e := by
  simp only [vecNormSq, vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem vecNormSq_smul (a : ℝ) (e : Homogenization.Vec d) :
    vecNormSq (a • e) = a ^ 2 * vecNormSq e := by
  rw [vecNormSq, vecDot_smul_smul]
  ring

theorem meanJ_smul_smul (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) (a b : ℝ)
    {e : Homogenization.Vec d} (he : vecNormSq e = 1) :
    meanJ M L n (a • e) (b • e) =
      (1 / 2) * alphaMean M L n * a ^ 2 + (1 / 2) * betaMean M L n * b ^ 2 - a * b := by
  rw [meanJ, vecNormSq_smul, vecNormSq_smul, vecDot_smul_smul, he]
  ring

theorem neg_smul_add_smul_smul (a b c : ℝ) (e : Homogenization.Vec d) :
    -(a • e) + c • (b • e) = (c * b - a) • e := by
  ext i
  simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem exists_unit_vec (hd : 1 ≤ d) : ∃ e : Homogenization.Vec d, vecNormSq e = 1 := by
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
theorem fMean_le_of_P (M : SubdiffusiveProcess.Model.GMCModel d) (hd : 1 ≤ d) {L : ℕ} {D F : ℝ}
    (hF : 0 ≤ F) (hP : InductionP M L D F) (n : ℕ) (hn : L ≤ n) : fMean M L n ≤ F := by
  obtain ⟨e, he⟩ := exists_unit_vec hd
  have h := ((hP n hn 0).2.2 e he).2
  rw [lintegral_frozenJ_eq_fMean M L n 0 e he] at h
  exact (ENNReal.ofReal_le_ofReal_iff hF).mp h

theorem eq_of_sq_eq_sq {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (h : X ^ 2 = Y ^ 2) : X = Y :=
  (sq_eq_sq₀ hX hY).mp h

/-! ### L5(b): the drop bound of the reciprocal pair -/

/-- For `β ≥ 1`, `β' ≥ β`:
`½α'β + ½β'/β - 1 - (αβ - 1)/2 ≤ β((α'+β')/2 - 1 - ((α+β)/2 - 1))`. -/
theorem recip_drop_le {α β α' β' : ℝ} (hβ1 : 1 ≤ β) (hb : β ≤ β') :
    (1 / 2) * α' * β + (1 / 2) * β' / β - 1 - (α * β - 1) / 2 ≤
      β * ((α' + β') / 2 - 1 - ((α + β) / 2 - 1)) := by
  have hβpos : 0 < β := by linarith
  have hβinv : β⁻¹ ≤ β := (inv_le_one_of_one_le₀ hβ1).trans hβ1
  have key : 0 ≤ (β' - β) * (β - β⁻¹) := mul_nonneg (by linarith) (by linarith)
  have hinv : β * β⁻¹ = 1 := mul_inv_cancel₀ hβpos.ne'
  have e : (1 / 2) * β' / β = (1 / 2) * (β' * β⁻¹) := by ring
  rw [e]
  nlinarith [key, hinv]

theorem mul_sqrt_le_sqrt {f j : ℝ} (hf : 0 ≤ f) (hj : 0 < j) (hfj : f ≤ j) :
    f / j * Real.sqrt j ≤ Real.sqrt f := by
  rw [div_mul_eq_mul_div, div_le_iff₀ hj]
  have hle : Real.sqrt f ≤ Real.sqrt j := Real.sqrt_le_sqrt hfj
  calc f * Real.sqrt j = (Real.sqrt f * Real.sqrt f) * Real.sqrt j := by
        rw [Real.mul_self_sqrt hf]
    _ = Real.sqrt f * (Real.sqrt f * Real.sqrt j) := by ring
    _ ≤ Real.sqrt f * (Real.sqrt j * Real.sqrt j) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hle (Real.sqrt_nonneg j))
          (Real.sqrt_nonneg f)
    _ = Real.sqrt f * j := by rw [Real.mul_self_sqrt hj.le]

/-! ### L6, planar pair (`d = 2`) -/

theorem perScale_planar (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (h2 : d = 2) (M : SubdiffusiveProcess.Model.GMCModel d) {D F : ℝ} (L : ℕ)
    (hPL : InductionP M L D F) (hBad : BadResponseBound row M L D F)
    (hTg : row.Tg ≤ row.Ks * row.rhoS ^ (row.g + 1) / (1 - row.rhoS)) (m' : ℕ)
    (hm1 : L + row.g ≤ m') (hf : 0 < fMean M L m') (hfF0 : fMean M L m' ≤ F)
    {e : Homogenization.Vec d} (he : vecNormSq e = 1) {bm : ℝ}
    (hbadle : row.badCharge M.delta D F ≤ bm) (hbm0 : 0 ≤ bm) :
    PerScaleIneq row (fMean M L) (varV M L) L F bm m' := by
  have hLm : L ≤ m' := by omega
  have hνK : row.nu ≤ m' - L := by have := hO.par2.2.2.1; omega
  have hFpos : 0 < F := lt_of_lt_of_le hf hfF0
  set f := fMean M L m' with hfdef
  have hαβ : ∀ n, L ≤ n → alphaMean M L n = betaMean M L n := fun n hn =>
    alpha_eq_beta_planar M h2 L hPL n hn
  have hβf : ∀ n, L ≤ n → betaMean M L n = 1 + fMean M L n := fun n hn => by
    simp only [fMean, hαβ n hn]
    ring
  set C := cMatch f with hC
  set r := rMatch f with hr
  have hCpos : 0 < C := by rw [hC, cMatch]; positivity
  have hrpos : 0 < r := by rw [hr, rMatch]; positivity
  have hmJ : ∀ n, L ≤ n → meanJ M L n ((1 + f) • e) ((1 : ℝ) • e) = C * fMean M L n + f ^ 2 / 2 :=
    fun n hn => by
      rw [meanJ_smul_smul M L n _ _ he, hαβ n hn, hβf n hn, hC, cMatch]
      ring
  have hmean : -((1 + f) • e) + betaMean M L m' • ((1 : ℝ) • e) = 0 := by
    rw [neg_smul_add_smul_smul, hβf m' hLm, ← hfdef]
    simp
  have hbad : ∀ R ∈ descendantsAtDepth (originCube d (m' : ℤ)) row.nu,
      ∫⁻ ω in (goodEvent row M L 0 m')ᶜ,
          ENNReal.ofReal (frozenJ M L (cellAt 0 R) ((1 + f) • e) ((1 : ℝ) • e) ω)
        ∂M.P.toMeasure ≤ ENNReal.ofReal (r * F * bm) := by
    intro R hR
    have h := ((hBad m' hm1 0 R hR e he).1 f ⟨hf.le, hfF0⟩)
    rw [one_smul]
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_left hbadle (by positivity)
  have h4 := loc_firstMoment row hd hO M L hPL m' hm1 hTg ((1 + f) • e) ((1 : ℝ) • e)
    hmean (by positivity) hbad
  -- rewrite L4 through L5(a)
  have hj : meanJ M L m' ((1 + f) • e) ((1 : ℝ) • e) = r * f := by
    rw [hmJ m' hLm, hC, hr, cMatch, rMatch]
    ring
  have hΔ : ∀ k ≤ m' - L, meanJ M L (m' - k) ((1 + f) • e) ((1 : ℝ) • e) -
      meanJ M L m' ((1 + f) • e) ((1 : ℝ) • e) = C * (fMean M L (m' - k) - f) := fun k hk => by
    rw [hmJ (m' - k) (by omega), hmJ m' hLm]
    ring
  set S1 := ∑ k ∈ Finset.Icc 1 (m' - L), row.haarB k * Real.sqrt (row.yk k / (row.R : ℝ)) *
    Real.sqrt (fMean M L (m' - k) - f) with hS1
  set S2 := ∑ k ∈ Finset.range (m' - L + 1), row.haarB k * Real.sqrt (varV M L (m' - k)) with hS2
  have hsum1 : ∑ k ∈ Finset.Icc 1 (m' - L), row.haarB k * Real.sqrt (row.yk k / (row.R : ℝ)) *
      Real.sqrt (meanJ M L (m' - k) ((1 + f) • e) ((1 : ℝ) • e) -
        meanJ M L m' ((1 + f) • e) ((1 : ℝ) • e)) = Real.sqrt C * S1 := by
    rw [hS1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hΔ k (Finset.mem_Icc.mp hk).2, Real.sqrt_mul hCpos.le]
    ring
  have hsum2 : ∑ k ∈ Finset.range (m' - L + 1), row.haarB k *
      Real.sqrt (varFactor d * vecNormSq ((1 : ℝ) • e) * varV M L (m' - k)) = S2 := by
    rw [hS2]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [one_smul, he, varFactor, ite_eq_left h2, one_mul, one_mul]
  rw [hsum1, hsum2, hΔ row.nu hνK, hj] at h4
  -- the target, multiplied by `r`
  unfold PerScaleIneq
  have hq : qPair d f = C / r := by rw [qPair, ite_eq_left h2, qMatch]
  have hrP : rPair d f = r := by rw [rPair, ite_eq_left h2]
  have hcoefA : row.coefA F = coefA0 row := by
    rw [Row.coefA, sigmaA, ite_eq_left h2, coefA0, mul_one]
  have hcoefAv : row.coefAv = coefAv0 row := by
    rw [Row.coefAv, sigmaV, ite_eq_left h2, coefAv0, mul_one]
  have hcoefB : row.coefB F = coefB0 row := by
    rw [Row.coefB, sigmaB, ite_eq_left h2, coefB0, mul_one]
  rw [hq, hrP, hcoefA, hcoefAv, hcoefB]
  have e1 : r * Real.sqrt (C / r * f) = Real.sqrt (r * f) * Real.sqrt C := by
    apply eq_of_sq_eq_sq (by positivity) (by positivity)
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
      Real.sq_sqrt hCpos.le]
    field_simp
  have e2 : r * (Real.sqrt f / Real.sqrt r) = Real.sqrt (r * f) := by
    apply eq_of_sq_eq_sq (by positivity) (by positivity)
    rw [mul_pow, div_pow, Real.sq_sqrt hf.le, Real.sq_sqrt hrpos.le,
      Real.sq_sqrt (by positivity)]
    field_simp
  have e3 : r * (C / r) = C := by field_simp
  have hkey : r * (coefA0 row * Real.sqrt (C / r * f) * S1 +
      coefAv0 row * Real.sqrt f / Real.sqrt r * S2 + coefB0 row * (C / r) *
        (fMean M L (m' - row.nu) - f) + F * bm) =
      coefA0 row * Real.sqrt (r * f) * (Real.sqrt C * S1) +
        coefAv0 row * Real.sqrt (r * f) * S2 + coefB0 row * (C * (fMean M L (m' - row.nu) - f)) +
        r * F * bm := by
    calc r * (coefA0 row * Real.sqrt (C / r * f) * S1 +
          coefAv0 row * Real.sqrt f / Real.sqrt r * S2 + coefB0 row * (C / r) *
            (fMean M L (m' - row.nu) - f) + F * bm) =
        coefA0 row * (r * Real.sqrt (C / r * f)) * S1 +
          coefAv0 row * (r * (Real.sqrt f / Real.sqrt r)) * S2 +
          coefB0 row * (r * (C / r)) * (fMean M L (m' - row.nu) - f) + r * F * bm := by ring
      _ = _ := by rw [e1, e2, e3]; ring
  rw [← mul_le_mul_iff_of_pos_left hrpos, hkey]
  calc r * ((1 - row.tauAbs) * f) = (1 - row.tauAbs) * (r * f) := by ring
    _ ≤ _ := h4

/-- The last step of the reciprocal case: multiply L4 by `t = f/j⋆ ∈ (0, 1]`. -/
theorem perScale_recip_final (row : Row d) (hO : row.Obligations) (h2 : d ≠ 2)
    (M : SubdiffusiveProcess.Model.GMCModel d) {F : ℝ} (L m' : ℕ) {j P1 P2 Δν bm : ℝ}
    (hf : 0 < fMean M L m') (hfj : fMean M L m' ≤ j) (hjpos : 0 < j) (hFpos : 0 < F)
    (hbm0 : 0 ≤ bm)
    (hsum1 : P1 ≤ Real.sqrt (1 + 2 * F) * ∑ k ∈ Finset.Icc 1 (m' - L), row.haarB k *
      Real.sqrt (row.yk k / (row.R : ℝ)) * Real.sqrt (fMean M L (m' - k) - fMean M L m'))
    (hsum2 : P2 ≤ Real.sqrt 2 * ∑ k ∈ Finset.range (m' - L + 1), row.haarB k *
      Real.sqrt (varV M L (m' - k)))
    (hΔν : Δν ≤ (1 + 2 * F) * (fMean M L (m' - row.nu) - fMean M L m')) (hΔν0 : 0 ≤ Δν)
    (h4 : (1 - row.tauAbs) * j ≤ coefA0 row * Real.sqrt j * P1 + coefAv0 row * Real.sqrt j * P2 +
      coefB0 row * Δν + F * bm)
    (hP1nn : 0 ≤ P1) (hP2nn : 0 ≤ P2) :
    PerScaleIneq row (fMean M L) (varV M L) L F bm m' := by
  set f := fMean M L m' with hfdef
  set S1 := ∑ k ∈ Finset.Icc 1 (m' - L), row.haarB k * Real.sqrt (row.yk k / (row.R : ℝ)) *
    Real.sqrt (fMean M L (m' - k) - f) with hS1
  set S2 := ∑ k ∈ Finset.range (m' - L + 1), row.haarB k * Real.sqrt (varV M L (m' - k)) with hS2
  have hcA := cNu_pos row hO
  have hRpos := R_pos row hO
  have hεpos := epsilon_pos row hO
  have hA0 : 0 ≤ coefA0 row := by unfold coefA0; positivity
  have hAv0 : 0 ≤ coefAv0 row := by unfold coefAv0; positivity
  have hB0 : 0 ≤ coefB0 row := by unfold coefB0; positivity
  set t := f / j with htdef
  have ht0 : 0 < t := div_pos hf hjpos
  have ht1 : t ≤ 1 := (div_le_one hjpos).mpr hfj
  have htj : t * j = f := by rw [htdef]; field_simp
  have htsq : t * Real.sqrt j ≤ Real.sqrt f := mul_sqrt_le_sqrt hf.le hjpos hfj
  have hb1 : t * (coefA0 row * Real.sqrt j * P1) ≤
      coefA0 row * Real.sqrt (1 + 2 * F) * Real.sqrt f * S1 := by
    calc t * (coefA0 row * Real.sqrt j * P1) = coefA0 row * (t * Real.sqrt j) * P1 := by ring
      _ ≤ coefA0 row * Real.sqrt f * (Real.sqrt (1 + 2 * F) * S1) :=
        mul_le_mul (mul_le_mul_of_nonneg_left htsq hA0) hsum1 hP1nn (by positivity)
      _ = _ := by ring
  have hb2 : t * (coefAv0 row * Real.sqrt j * P2) ≤
      coefAv0 row * Real.sqrt 2 * Real.sqrt f * S2 := by
    calc t * (coefAv0 row * Real.sqrt j * P2) = coefAv0 row * (t * Real.sqrt j) * P2 := by ring
      _ ≤ coefAv0 row * Real.sqrt f * (Real.sqrt 2 * S2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left htsq hAv0) hsum2 hP2nn (by positivity)
      _ = _ := by ring
  have hb3 : t * (coefB0 row * Δν) ≤ coefB0 row * (1 + 2 * F) * (fMean M L (m' - row.nu) - f) := by
    calc t * (coefB0 row * Δν) ≤ 1 * (coefB0 row * Δν) :=
          mul_le_mul_of_nonneg_right ht1 (mul_nonneg hB0 hΔν0)
      _ ≤ coefB0 row * ((1 + 2 * F) * (fMean M L (m' - row.nu) - f)) := by
          rw [one_mul]; exact mul_le_mul_of_nonneg_left hΔν hB0
      _ = _ := by ring
  have hb4 : t * (F * bm) ≤ F * bm := by
    calc t * (F * bm) ≤ 1 * (F * bm) := mul_le_mul_of_nonneg_right ht1 (by positivity)
      _ = _ := one_mul _
  have h4t := mul_le_mul_of_nonneg_left h4 ht0.le
  have hlhs : t * ((1 - row.tauAbs) * j) = (1 - row.tauAbs) * f := by
    rw [← htj]; ring
  rw [hlhs] at h4t
  have hsplit : t * (coefA0 row * Real.sqrt j * P1 + coefAv0 row * Real.sqrt j * P2 +
      coefB0 row * Δν + F * bm) =
      t * (coefA0 row * Real.sqrt j * P1) + t * (coefAv0 row * Real.sqrt j * P2) +
        t * (coefB0 row * Δν) + t * (F * bm) := by ring
  unfold PerScaleIneq
  have hq : qPair d f = 1 := by rw [qPair, ite_eq_right h2]
  have hrP : rPair d f = 1 := by rw [rPair, ite_eq_right h2]
  have hcoefA : row.coefA F = coefA0 row * Real.sqrt (1 + 2 * F) := by
    rw [Row.coefA, sigmaA, ite_eq_right h2, coefA0]
  have hcoefAv : row.coefAv = coefAv0 row * Real.sqrt 2 := by
    rw [Row.coefAv, sigmaV, ite_eq_right h2, coefAv0]
  have hcoefB : row.coefB F = coefB0 row * (1 + 2 * F) := by
    rw [Row.coefB, sigmaB, ite_eq_right h2, coefB0]
  rw [hq, hrP, hcoefA, hcoefAv, hcoefB, one_mul, Real.sqrt_one, div_one]
  linarith [h4t, hsplit, hb1, hb2, hb3, hb4]

/-! ### L6, reciprocal pair (`d ≥ 3`) -/

theorem perScale_recip (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (h2 : d ≠ 2) (M : SubdiffusiveProcess.Model.GMCModel d) {D F : ℝ} (L : ℕ)
    (hPL : InductionP M L D F) (hBad : BadResponseBound row M L D F)
    (hTg : row.Tg ≤ row.Ks * row.rhoS ^ (row.g + 1) / (1 - row.rhoS)) (m' : ℕ)
    (hm1 : L + row.g ≤ m') (hf : 0 < fMean M L m') (hfF0 : fMean M L m' ≤ F)
    {e : Homogenization.Vec d} (he : vecNormSq e = 1) {bm : ℝ}
    (hbadle : row.badCharge M.delta D F ≤ bm) (hbm0 : 0 ≤ bm) :
    PerScaleIneq row (fMean M L) (varV M L) L F bm m' := by
  have hLm : L ≤ m' := by omega
  have hνK : row.nu ≤ m' - L := by have := hO.par2.2.2.1; omega
  have hFpos : 0 < F := lt_of_lt_of_le hf hfF0
  obtain ⟨hge1, hanti⟩ := alphaBeta_ge_one_antitone M L hPL
  set f := fMean M L m' with hfdef
  have hdropf : ∀ k ≤ m' - L, 0 ≤ fMean M L (m' - k) - f := fun k hk => by
    obtain ⟨h1, h2⟩ := hanti (m' - k) m' (by omega) (by omega)
    simp only [hfdef, fMean]
    linarith
  set α := alphaMean M L m' with hαdef
  set β := betaMean M L m' with hβdef
  have hα1 : 1 ≤ α := (hge1 m' hLm).1
  have hβ1 : 1 ≤ β := (hge1 m' hLm).2
  have hβpos : 0 < β := by linarith
  have hfαβ : f = (α + β) / 2 - 1 := rfl
  have hβF : β ≤ 1 + 2 * F := by linarith
  set sβ := Real.sqrt β with hsβ
  have hsβpos : 0 < sβ := Real.sqrt_pos.mpr hβpos
  have hsβsq : sβ ^ 2 = β := Real.sq_sqrt hβpos.le
  have hmJ : ∀ n, meanJ M L n (sβ • e) (sβ⁻¹ • e) =
      (1 / 2) * alphaMean M L n * β + (1 / 2) * betaMean M L n / β - 1 := fun n => by
    rw [meanJ_smul_smul M L n _ _ he, inv_pow, hsβsq, mul_inv_cancel₀ hsβpos.ne']
    ring
  have hmean : -(sβ • e) + betaMean M L m' • (sβ⁻¹ • e) = 0 := by
    rw [neg_smul_add_smul_smul, ← hβdef]
    have : β * sβ⁻¹ - sβ = 0 := by
      rw [← hsβsq]
      field_simp
      ring
    rw [this, zero_smul]
  have hbad : ∀ R ∈ descendantsAtDepth (originCube d (m' : ℤ)) row.nu,
      ∫⁻ ω in (goodEvent row M L 0 m')ᶜ,
          ENNReal.ofReal (frozenJ M L (cellAt 0 R) (sβ • e) (sβ⁻¹ • e) ω)
        ∂M.P.toMeasure ≤ ENNReal.ofReal (F * bm) := by
    intro R hR
    have h := ((hBad m' hm1 0 R hR e he).2 β ⟨hβ1, hβF⟩)
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_left hbadle hFpos.le
  have h4 := loc_firstMoment row hd hO M L hPL m' hm1 hTg (sβ • e) (sβ⁻¹ • e)
    hmean (by positivity) hbad
  set j := meanJ M L m' (sβ • e) (sβ⁻¹ • e) with hjdef
  have hj : j = (α * β - 1) / 2 := by
    rw [hjdef, hmJ m', ← hαdef, ← hβdef]
    field_simp
    ring
  have hfj : f ≤ j := by
    rw [hj, hfαβ]
    nlinarith
  have hjpos : 0 < j := lt_of_lt_of_le hf hfj
  -- L5(b) bounds
  have hΔ : ∀ k ≤ m' - L, meanJ M L (m' - k) (sβ • e) (sβ⁻¹ • e) - j ≤
      β * (fMean M L (m' - k) - f) := fun k hk => by
    obtain ⟨_, hb⟩ := hanti (m' - k) m' (by omega) (by omega)
    rw [hmJ, hj, hfαβ]
    simp only [fMean]
    exact recip_drop_le hβ1 hb
  set S1 := ∑ k ∈ Finset.Icc 1 (m' - L), row.haarB k * Real.sqrt (row.yk k / (row.R : ℝ)) *
    Real.sqrt (fMean M L (m' - k) - f) with hS1
  set S2 := ∑ k ∈ Finset.range (m' - L + 1), row.haarB k * Real.sqrt (varV M L (m' - k)) with hS2
  have hsum1 : ∑ k ∈ Finset.Icc 1 (m' - L), row.haarB k * Real.sqrt (row.yk k / (row.R : ℝ)) *
      Real.sqrt (meanJ M L (m' - k) (sβ • e) (sβ⁻¹ • e) - j) ≤
      Real.sqrt (1 + 2 * F) * S1 := by
    rw [hS1, Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    have hk' := (Finset.mem_Icc.mp hk).2
    have h1 : Real.sqrt (meanJ M L (m' - k) (sβ • e) (sβ⁻¹ • e) - j) ≤
        Real.sqrt (1 + 2 * F) * Real.sqrt (fMean M L (m' - k) - f) := by
      rw [← Real.sqrt_mul (by linarith)]
      exact Real.sqrt_le_sqrt ((hΔ k hk').trans
        (mul_le_mul_of_nonneg_right hβF (hdropf k hk')))
    calc row.haarB k * Real.sqrt (row.yk k / (row.R : ℝ)) *
          Real.sqrt (meanJ M L (m' - k) (sβ • e) (sβ⁻¹ • e) - j) ≤
        row.haarB k * Real.sqrt (row.yk k / (row.R : ℝ)) *
          (Real.sqrt (1 + 2 * F) * Real.sqrt (fMean M L (m' - k) - f)) :=
          mul_le_mul_of_nonneg_left h1
            (mul_nonneg (haarB_nonneg' row k) (Real.sqrt_nonneg _))
      _ = _ := by ring
  have hsum2 : ∑ k ∈ Finset.range (m' - L + 1), row.haarB k *
      Real.sqrt (varFactor d * vecNormSq (sβ⁻¹ • e) * varV M L (m' - k)) ≤
      Real.sqrt 2 * S2 := by
    rw [hS2, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [vecNormSq_smul, he, varFactor, ite_eq_right h2, inv_pow, hsβsq, mul_one]
    have hV := varV_nonneg M L (m' - k)
    have hβi : β⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hβ1
    have h1 : Real.sqrt (2 * β⁻¹ * varV M L (m' - k)) ≤
        Real.sqrt 2 * Real.sqrt (varV M L (m' - k)) := by
      rw [← Real.sqrt_mul (by norm_num)]
      exact Real.sqrt_le_sqrt (by nlinarith)
    calc row.haarB k * Real.sqrt (2 * β⁻¹ * varV M L (m' - k)) ≤
        row.haarB k * (Real.sqrt 2 * Real.sqrt (varV M L (m' - k))) :=
          mul_le_mul_of_nonneg_left h1 (haarB_nonneg' row k)
      _ = _ := by ring
  have hΔν : meanJ M L (m' - row.nu) (sβ • e) (sβ⁻¹ • e) - j ≤
      (1 + 2 * F) * (fMean M L (m' - row.nu) - f) :=
    (hΔ row.nu hνK).trans (mul_le_mul_of_nonneg_right hβF (hdropf row.nu hνK))
  have hΔν0 : 0 ≤ meanJ M L (m' - row.nu) (sβ • e) (sβ⁻¹ • e) - j :=
    sub_nonneg.mpr ((meanJ_nonneg_mono M L hPL m' hLm _ _).2 row.nu hνK)
  have hP1nn : 0 ≤ ∑ k ∈ Finset.Icc 1 (m' - L), row.haarB k * Real.sqrt (row.yk k / (row.R : ℝ)) *
      Real.sqrt (meanJ M L (m' - k) (sβ • e) (sβ⁻¹ • e) - j) := Finset.sum_nonneg fun k _ =>
    mul_nonneg (mul_nonneg (haarB_nonneg' row k) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hP2nn : 0 ≤ ∑ k ∈ Finset.range (m' - L + 1), row.haarB k *
      Real.sqrt (varFactor d * vecNormSq (sβ⁻¹ • e) * varV M L (m' - k)) :=
    Finset.sum_nonneg fun k _ => mul_nonneg (haarB_nonneg' row k) (Real.sqrt_nonneg _)
  exact perScale_recip_final row hO h2 M L m' hf hfj hjpos hFpos hbm0 hsum1 hsum2 hΔν hΔν0 h4
    hP1nn hP2nn

/-! ### L6 -/

/-- **L6 (normalized per-scale inequality)**, with bad term `F · max(bad, 0)`. Assume `𝖯(k; D, F)`
for `k ≤ L`, the bad-response bound (G9) and the H12 tail bound for `T_g`. Then at every observation
scale `m' ≥ L + g` with `f_{m'} > 0` the per-scale inequality holds. -/
theorem perScaleIneq_max (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (M : SubdiffusiveProcess.Model.GMCModel d) {D F : ℝ} (L : ℕ)
    (hP : ∀ k ≤ L, InductionP M k D F) (hBad : BadResponseBound row M L D F)
    (hTg : row.Tg ≤ row.Ks * row.rhoS ^ (row.g + 1) / (1 - row.rhoS)) (m' : ℕ)
    (hm1 : L + row.g ≤ m') (hf : 0 < fMean M L m') :
    PerScaleIneq row (fMean M L) (varV M L) L F (max (row.badCharge M.delta D F) 0) m' := by
  have hd1 : 1 ≤ d := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    omega
  have hPL := hP L le_rfl
  have hLm : L ≤ m' := by omega
  obtain ⟨e, he⟩ := exists_unit_vec hd1
  have hFnn : 0 ≤ F := by
    by_contra hneg'
    have hneg : F < 0 := not_le.mp hneg'
    have h := ((hPL m' hLm 0).2.2 e he).2
    rw [lintegral_frozenJ_eq_fMean M L m' 0 e he, ENNReal.ofReal_of_nonpos hneg.le,
      nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h
    exact absurd hf (not_lt.mpr h)
  have hfF0 := fMean_le_of_P M hd1 hFnn hPL m' hLm
  by_cases h2 : d = 2
  · exact perScale_planar row hd hO h2 M L hPL hBad hTg m' hm1 hf hfF0 he (le_max_left _ _)
      (le_max_right _ _)
  · exact perScale_recip row hd hO h2 M L hPL hBad hTg m' hm1 hf hfF0 he (le_max_left _ _)
      (le_max_right _ _)

/-- **L6 as stated in the target** (`F · bad`), when `bad ≥ 0`. -/
theorem perScaleIneq_of_badCharge_nonneg (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ))
    (hO : row.Obligations) (M : SubdiffusiveProcess.Model.GMCModel d) {D F : ℝ} (L : ℕ)
    (hP : ∀ k ≤ L, InductionP M k D F) (hBad : BadResponseBound row M L D F)
    (hTg : row.Tg ≤ row.Ks * row.rhoS ^ (row.g + 1) / (1 - row.rhoS))
    (hbad0 : 0 ≤ row.badCharge M.delta D F) (m' : ℕ) (hm1 : L + row.g ≤ m')
    (hf : 0 < fMean M L m') :
    PerScaleIneq row (fMean M L) (varV M L) L F (row.badCharge M.delta D F) m' := by
  have h := perScaleIneq_max row hd hO M L hP hBad hTg m' hm1 hf
  rwa [max_eq_left hbad0] at h

end GMCExplicitDelta.Localization
