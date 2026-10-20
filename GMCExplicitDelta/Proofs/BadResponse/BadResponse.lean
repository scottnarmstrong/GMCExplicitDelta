module

public import GMCExplicitDelta.Proofs.BadResponse.Pointwise
public import GMCExplicitDelta.Steps.AssemblyFrozen
public import GMCExplicitDelta.Coarse.PhiLpIntegral
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# G9: bad response of the matched pairs

Proof of `badResponseBound_holds` (G9). Hölder with exponents
`(32, 32/31)` on the bad event: `𝔼[J 1_{𝒢ᶜ}] ≤ ‖J‖_{32} ℙ(𝒢ᶜ)^{31/32}`; pointwise C3 + C7
(`J ≤ r_⋆ Φ_{log(1+2F)}(J^max(U))`, `G9Pointwise.lean`), the `L^{32}` form of C7
(`‖Φ_t(J^max)‖_{32} ≤ Φ_t(U_{g-ν})`), the native cap A6 of the cell (`nativeCap_bound`, at scale
`m'-ν ≥ L+g-ν`, with the monotonicity of `U_k`), and G8.

The statement proved is the target's plus the hypothesis `0 ≤ ε_sub`: the bound `bad` involves
`(e_⋆/(θ_R-F))^{31}`, which must be nonnegative, and `e_⋆ ≥ 0` needs `ε_sub ≥ 0` for `d ≥ 3`
(the contract's `Obligations` does not record the sign of `ε_sub`).
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open MeasureTheory
open scoped ENNReal

namespace GMCExplicitDelta.Assembly

open Contract

variable {d : ℕ}

namespace BadResponse

/-- **Hölder `(32, 32/31)` on a set, with C7.** If `‖X‖_{32} ≤ A`, `f ≤ c Φ_t(X)` where `X < ∞`,
and `μ(S) ≤ r^{32}`, then `∫_S f ≤ c Φ_t(A) r^{31}`. -/
theorem setLIntegral_le_of_phi {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ≥0∞} (hX : Measurable X) {A t c r : ℝ} (hA : 0 ≤ A)
    (ht : 0 ≤ t) (hc : 0 ≤ c) (hr : 0 ≤ r)
    (hXA : paperENNRealLpNorm μ 32 X ≤ ENNReal.ofReal A)
    {f : Ω → ℝ} (hf : ∀ ω, X ω ≠ ⊤ → f ω ≤ c * PhiMap t (X ω).toReal)
    {S : Set Ω} (hS : μ S ≤ ENNReal.ofReal (r ^ 32)) :
    ∫⁻ ω in S, ENNReal.ofReal (f ω) ∂μ ≤ ENNReal.ofReal (c * PhiMap t A * r ^ 31) := by
  -- `X < ∞` almost surely
  have hint : ∫⁻ ω, X ω ^ (32 : ℝ) ∂μ ≠ ⊤ := by
    intro htop
    have h : paperENNRealLpNorm μ 32 X = ⊤ := by
      unfold paperENNRealLpNorm
      rw [htop, ENNReal.top_rpow_of_pos (by norm_num)]
    rw [h] at hXA
    exact ENNReal.ofReal_ne_top (top_le_iff.mp hXA)
  have hfin : ∀ᵐ ω ∂μ, X ω ≠ ⊤ := by
    filter_upwards [ae_lt_top (hX.pow_const _) hint] with ω hω
    intro hω'
    rw [hω', ENNReal.top_rpow_of_pos (by norm_num)] at hω
    exact lt_irrefl _ hω
  -- the C7 majorant `g = Φ_t(X)`
  have hJm : Measurable fun ω => (X ω).toReal := hX.ennreal_toReal
  have hJ0 : ∀ ω, 0 ≤ (X ω).toReal := fun ω => ENNReal.toReal_nonneg
  have hΦm : Measurable fun ω => Coarse.phi t (X ω).toReal :=
    (Coarse.continuous_phi t).measurable.comp hJm
  have hgm : Measurable fun ω => ENNReal.ofReal (PhiMap t (X ω).toReal) :=
    ENNReal.measurable_ofReal.comp hΦm
  have hΦA : 0 ≤ PhiMap t A := Coarse.phi_nonneg hA ht
  -- pointwise
  have h1 : ∫⁻ ω in S, ENNReal.ofReal (f ω) ∂μ ≤
      ENNReal.ofReal c * ∫⁻ ω in S, ENNReal.ofReal (PhiMap t (X ω).toReal) ∂μ := by
    rw [← lintegral_const_mul _ hgm]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_of_ae hfin] with ω hω
    rw [← ENNReal.ofReal_mul hc]
    exact ENNReal.ofReal_le_ofReal (hf ω hω)
  -- Hölder on `S`
  have hpq : (32 : ℝ).HolderConjugate (32 / 31) := ⟨by norm_num, by norm_num, by norm_num⟩
  have h2 := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.restrict S) hpq hgm.aemeasurable
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const,
    Measure.restrict_apply_univ, one_mul] at h2
  -- C7 in `L^{32}`
  have hJA : eLpNorm (fun ω => (X ω).toReal) (ENNReal.ofReal 32) μ ≤ ENNReal.ofReal A := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp) ENNReal.ofReal_ne_top
      hJm.aestronglyMeasurable, ENNReal.toReal_ofReal (by norm_num)]
    refine le_trans ?_ hXA
    unfold paperENNRealLpNorm
    rw [one_div]
    refine ENNReal.rpow_le_rpow (lintegral_mono fun ω => ENNReal.rpow_le_rpow ?_ (by norm_num))
      (by norm_num)
    rw [Real.enorm_eq_ofReal (hJ0 ω)]
    exact ENNReal.ofReal_toReal_le
  have hΦ := Coarse.eLpNorm_phi_comp_le (μ := μ) (p := 32) (by norm_num) hJm.aemeasurable hJ0 ht
    hA hJA
  have h3 : (∫⁻ ω, ENNReal.ofReal (PhiMap t (X ω).toReal) ^ (32 : ℝ) ∂μ.restrict S) ^
      (1 / (32 : ℝ)) ≤ ENNReal.ofReal (PhiMap t A) := by
    refine le_trans (ENNReal.rpow_le_rpow (setLIntegral_le_lintegral S _) (by norm_num)) ?_
    refine le_trans (le_of_eq ?_) hΦ
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp) ENNReal.ofReal_ne_top
      hΦm.aestronglyMeasurable, ENNReal.toReal_ofReal (by norm_num)]
    congr 1
    refine lintegral_congr fun ω => ?_
    rw [Real.enorm_eq_ofReal (Coarse.phi_nonneg (hJ0 ω) ht)]
    rfl
  -- the bad probability
  have h4 : μ S ^ (1 / ((32 : ℝ) / 31)) ≤ ENNReal.ofReal (r ^ 31) := by
    have e : (1 / ((32 : ℝ) / 31)) = 31 / 32 := by norm_num
    rw [e]
    refine le_trans (ENNReal.rpow_le_rpow hS (by norm_num)) (le_of_eq ?_)
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
    congr 1
    rw [← Real.rpow_natCast r 32, ← Real.rpow_mul hr]
    have e' : ((32 : ℕ) : ℝ) * (31 / 32) = ((31 : ℕ) : ℝ) := by norm_num
    rw [e', Real.rpow_natCast]
  calc ∫⁻ ω in S, ENNReal.ofReal (f ω) ∂μ
      ≤ ENNReal.ofReal c * ∫⁻ ω in S, ENNReal.ofReal (PhiMap t (X ω).toReal) ∂μ := h1
    _ ≤ ENNReal.ofReal c * ((∫⁻ ω, ENNReal.ofReal (PhiMap t (X ω).toReal) ^ (32 : ℝ)
          ∂μ.restrict S) ^ (1 / (32 : ℝ)) * μ S ^ (1 / ((32 : ℝ) / 31))) := by
        gcongr
    _ ≤ ENNReal.ofReal c * (ENNReal.ofReal (PhiMap t A) * ENNReal.ofReal (r ^ 31)) := by
        gcongr
    _ = ENNReal.ofReal (c * PhiMap t A * r ^ 31) := by
        rw [ENNReal.ofReal_mul (mul_nonneg hc hΦA), ENNReal.ofReal_mul hc, mul_assoc]

/-- **G9 with `e_⋆ ≥ 0` as a hypothesis.** The hypotheses `z_F < 1`, `𝔲_{12} < 1` of the target
are not used (`z_F < 1` enters only through `e_⋆ ≥ 0`). -/
theorem badResponseBound_of_eStar_nonneg (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ))
    (hO : row.Obligations) (M : SubdiffusiveProcess.Model.GMCModel d) {D F : ℝ} (hD : 0 < D)
    (hF : 0 < F) (hFD : F ≤ D) (L : ℕ) (hP : ∀ k ≤ L, InductionP M k D F)
    (hθ : F < row.thetaR) (he0 : 0 ≤ row.eStar M.delta D F)
    (hG8 : ∀ m', L + row.g ≤ m' → ∀ z : Homogenization.Vec d,
      M.P.toMeasure (goodEvent row M L z m')ᶜ ≤
        ENNReal.ofReal ((row.eStar M.delta D F / (row.thetaR - F)) ^ 32)) :
    BadResponseBound row M L D F := by
  intro m' hm' z R hR e he
  have hνg : row.nu + 1 ≤ row.g := hO.par2.2.2.1
  have hν : row.nu ≤ m' := by omega
  have hU : cellAt z R = cubeAt (z + fun i => (R.index i : ℝ) * (3 : ℝ) ^ R.scale)
      (m' - row.nu) := cellAt_eq_cubeAt z hν hR
  have hLk : L + (m' - row.nu - L) = m' - row.nu := by omega
  -- the native cap of the cell: A6 at scale `m' - ν ≥ L + g - ν`, and `U_k ≤ U_{g-ν}`
  have hA6 := (nativeCap_bound hd hO M hD hF hFD L (hP L le_rfl) (m' - row.nu - L) (by omega)
    (z + fun i => (R.index i : ℝ) * (3 : ℝ) ^ R.scale)).1
  rw [hLk, ← hU] at hA6
  have hcap : paperENNRealLpNorm M.P.toMeasure 32 (normalizedDefect M L (cellAt z R)) ≤
      ENNReal.ofReal (nativeCap d (row.g - row.nu) D F) :=
    hA6.trans (ENNReal.ofReal_le_ofReal (nativeCap_anti hD hF (by omega) (by omega)))
  have hmeas : Measurable (normalizedDefect M L (cellAt z R)) := by
    rw [hU]
    exact (hP L le_rfl (m' - row.nu) (by omega) _).1
  -- the bad probability (G8) and the sign of `e_⋆/(θ_R - F)`
  have hθF : 0 < row.thetaR - F := by linarith
  have hr : 0 ≤ row.eStar M.delta D F / (row.thetaR - F) := div_nonneg he0 hθF.le
  have hS := hG8 m' hm' z
  have hU0 := nativeCap_nonneg' d (row.g - row.nu) hD hF
  have ht : 0 ≤ Real.log (1 + 2 * F) := Real.log_nonneg (by linarith)
  have hbad : ∀ c : ℝ, c * F * row.badCharge M.delta D F =
      c * PhiMap (Real.log (1 + 2 * F)) (nativeCap d (row.g - row.nu) D F) *
        (row.eStar M.delta D F / (row.thetaR - F)) ^ 31 := by
    intro c
    unfold Row.badCharge
    field_simp
  refine ⟨fun μ hμ => ?_, fun β hβ => ?_⟩
  · have hrm : 0 ≤ rMatch μ := by
      unfold rMatch
      have := hμ.1
      positivity
    rw [hbad]
    exact setLIntegral_le_of_phi hmeas hU0 ht hrm hr hcap
      (fun ω hω => frozenJ_planar_le M L _ ω he hμ.1 hμ.2 hω) hS
  · have h := setLIntegral_le_of_phi hmeas hU0 ht zero_le_one hr hcap
      (fun ω hω => (frozenJ_recip_le M L _ ω he hβ.1 hβ.2 hω).trans_eq (one_mul _).symm) hS
    rw [show F * row.badCharge M.delta D F = 1 * F * row.badCharge M.delta D F by ring, hbad]
    exact h

end BadResponse

/-- **G9 (bad response of the matched pairs).** The target statement of `badResponseBound_holds`
plus `0 ≤ ε_sub` (needed for `e_⋆ ≥ 0`, see the module docstring). -/
theorem badResponseBound_holds_proof (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ))
    (hO : row.Obligations) (M : SubdiffusiveProcess.Model.GMCModel d) {D F : ℝ} (hD : 0 < D)
    (hF : 0 < F) (hFD : F ≤ D) (L : ℕ) (hP : ∀ k ≤ L, InductionP M k D F)
    (hzF : row.zF M.delta < 1) (hu : frakU d row.historyCutoff D F < 1) (hθ : F < row.thetaR)
    (hG8 : ∀ m', L + row.g ≤ m' → ∀ z : Homogenization.Vec d,
      M.P.toMeasure (goodEvent row M L z m')ᶜ ≤
        ENNReal.ofReal ((row.eStar M.delta D F / (row.thetaR - F)) ^ 32)) :
    BadResponseBound row M L D F :=
  BadResponse.badResponseBound_of_eStar_nonneg row hd hO M hD hF hFD L hP hθ
    (BadResponse.eStar_nonneg row hO (by exact_mod_cast hO.par4.le) M.shellPrefix.delta_pos hD hF hzF) hG8

end GMCExplicitDelta.Assembly
