module

public import GMCExplicitDelta.Proofs.Observables.Measurable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! G8, with the v2 nonnegative-cap hypothesis. -/
@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open scoped ENNReal

namespace GMCExplicitDelta.Assembly

open Contract
variable {d : ℕ}

theorem measurable_haarStat (row : Row d) (M : SubdiffusiveProcess.Model.GMCModel d)
    (L : ℕ) (z : Homogenization.Vec d) (n : ℕ) : Measurable (haarStat row M L z n) := by
  have hd (j : ℕ) : Measurable (depthMax M L z n j) := by
    unfold depthMax
    simp only [Finset.sup_eq_iSup]
    exact Measurable.iSup (fun R => Measurable.iSup (fun _ => by
      exact (measurable_cascadeObservables_proof M L (cellAt z R)).1 (ahom M L)))
  unfold haarStat
  exact Measurable.tsum (fun j => measurable_const.mul (hd j))

theorem badEvent_prob_le_proof (row : Row d) (M : SubdiffusiveProcess.Model.GMCModel d) {D F : ℝ}
    (L : ℕ) (hθ : F < row.thetaR) (hF : 0 ≤ F)
    (hG7 : ∀ t, row.g ≤ t → ∀ z : Homogenization.Vec d,
      paperENNRealLpNorm M.P.toMeasure 32
          (fun ω => haarStat row M L z (L + t) ω - ENNReal.ofReal F) ≤
        ENNReal.ofReal (row.eStar M.delta D F)) :
    ∀ m', L + row.g ≤ m' → ∀ z : Homogenization.Vec d,
      M.P.toMeasure (goodEvent row M L z m')ᶜ ≤
        ENNReal.ofReal ((row.eStar M.delta D F / (row.thetaR - F)) ^ 32) := by
  intro m' hm z
  let X := fun ω => haarStat row M L z m' ω - ENNReal.ofReal F
  have hX : Measurable X := (measurable_haarStat row M L z m').sub measurable_const
  have hnorm := hG7 (m' - L) (by omega) z
  rw [Nat.add_sub_of_le (by omega : L ≤ m')] at hnorm
  have hmoment : (∫⁻ ω, X ω ^ (32 : ℕ) ∂M.P.toMeasure) ≤
      ENNReal.ofReal (row.eStar M.delta D F) ^ (32 : ℕ) := by
    have h := ENNReal.rpow_le_rpow hnorm (by norm_num : (0 : ℝ) ≤ 32)
    unfold paperENNRealLpNorm at h
    rw [← ENNReal.rpow_mul, inv_mul_cancel₀ (by norm_num : (32 : ℝ) ≠ 0), ENNReal.rpow_one] at h
    change (∫⁻ ω, X ω ^ ((32 : ℕ) : ℝ) ∂M.P.toMeasure) ≤
      ENNReal.ofReal (row.eStar M.delta D F) ^ ((32 : ℕ) : ℝ) at h
    simpa only [ENNReal.rpow_natCast] using h
  have hgap : 0 < row.thetaR - F := sub_pos.mpr hθ
  have hset : (goodEvent row M L z m')ᶜ ⊆
      {ω | ENNReal.ofReal (row.thetaR - F) ^ (32 : ℕ) ≤ X ω ^ (32 : ℕ)} := by
    intro ω hω
    have hθT : ENNReal.ofReal row.thetaR < haarStat row M L z m' ω :=
      lt_of_not_ge hω
    change ENNReal.ofReal (row.thetaR - F) ^ (32 : ℕ) ≤ X ω ^ (32 : ℕ)
    apply pow_le_pow_left'
    apply ENNReal.le_sub_of_add_le_left ENNReal.ofReal_ne_top
    rw [← ENNReal.ofReal_add hF hgap.le]
    have heq : F + (row.thetaR - F) = row.thetaR := by ring
    rw [heq]
    exact hθT.le
  have hMarkov := meas_ge_le_lintegral_div (μ := M.P.toMeasure) (hX.pow_const (32 : ℕ)).aemeasurable
    (ε := ENNReal.ofReal (row.thetaR - F) ^ (32 : ℕ))
    (pow_ne_zero 32 (ENNReal.ofReal_ne_zero_iff.mpr hgap))
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  refine (measure_mono hset).trans (hMarkov.trans ?_)
  calc
    _ ≤ ENNReal.ofReal (row.eStar M.delta D F) ^ (32 : ℕ) /
        ENNReal.ofReal (row.thetaR - F) ^ (32 : ℕ) := by
      exact ENNReal.div_le_div_right hmoment _
    _ ≤ _ := by
      by_cases hE : 0 ≤ row.eStar M.delta D F
      · rw [← ENNReal.ofReal_pow hE, ← ENNReal.ofReal_pow hgap.le,
          ← ENNReal.ofReal_div_of_pos (pow_pos hgap 32), div_pow]
      · simp only [ENNReal.ofReal_of_nonpos (le_of_not_ge hE), zero_pow (by omega : 32 ≠ 0), ENNReal.zero_div]
        exact bot_le

end GMCExplicitDelta.Assembly
