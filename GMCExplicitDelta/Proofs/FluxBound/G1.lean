module

public import GMCExplicitDelta.Proofs.FluxBound.Cube

/-!
# Localization pieces: the concavity step of G1(b)

A tangent-line bound for `𝗑` at `θ_R` and the resulting weighted-average estimate
`(1-w)∑ w^k 𝗑(t_k) ≤ R` when `(1-w)∑ w^k t_k ≤ θ_R`.
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open scoped ENNReal

namespace GMCExplicitDelta.Localization.FluxBound

open Assembly Contract

theorem xfun_le_affine {R : ℝ} (hR : 1 < R) {t : ℝ} (ht : 0 ≤ t) :
    Coarse.xfun t ≤ R + (1 + ((R + R⁻¹) / 2) / ((R - R⁻¹) / 2)) * (t - (R + R⁻¹ - 2) / 2) := by
  have hR0 : 0 < R := by linarith
  have hRr : R * R⁻¹ = 1 := mul_inv_cancel₀ hR0.ne'
  have hinv : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
  have hs0 : 0 < (R - R⁻¹) / 2 := by linarith
  have hu1 : 1 ≤ (R + R⁻¹) / 2 := by nlinarith [sq_nonneg (R - 1), inv_pos.mpr hR0]
  have hu0s : ((R - R⁻¹) / 2) ^ 2 = ((R + R⁻¹) / 2) ^ 2 - 1 := by nlinarith [hRr]
  have hsq : √(t * (t + 2)) ≤ (((R + R⁻¹) / 2) * (t + 1) - 1) / ((R - R⁻¹) / 2) := by
    rw [Real.sqrt_le_iff]
    refine ⟨div_nonneg (by nlinarith) hs0.le, ?_⟩
    rw [div_pow, le_div_iff₀ (by positivity), hu0s]
    nlinarith [sq_nonneg (t + 1 - (R + R⁻¹) / 2)]
  have key : 1 + t + (((R + R⁻¹) / 2) * (t + 1) - 1) / ((R - R⁻¹) / 2) =
      R + (1 + ((R + R⁻¹) / 2) / ((R - R⁻¹) / 2)) * (t - (R + R⁻¹ - 2) / 2) := by
    generalize R⁻¹ = r at hRr hs0 ⊢
    have hne : R - r ≠ 0 := by intro h; rw [h] at hs0; simp at hs0
    field_simp
    linear_combination (4 : ℝ) * hRr
  unfold Coarse.xfun
  linarith

theorem weighted_xfun_le {R w : ℝ} (hR : 1 < R) (hw0 : 0 < w) (hw1 : w < 1) {t : ℕ → ℝ}
    (ht : ∀ k, 0 ≤ t k) (hs : Summable (fun k => w ^ k * t k))
    (hT : (1 - w) * ∑' k, w ^ k * t k ≤ (R + R⁻¹ - 2) / 2) :
    Summable (fun k => w ^ k * Coarse.xfun (t k)) ∧
      (1 - w) * ∑' k, w ^ k * Coarse.xfun (t k) ≤ R := by
  have hR0 : 0 < R := by linarith
  have hinv : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
  have hs0 : 0 < (R - R⁻¹) / 2 := by linarith
  have hu0 : 0 < (R + R⁻¹) / 2 := by have := inv_pos.mpr hR0; linarith
  set B : ℝ := 1 + ((R + R⁻¹) / 2) / ((R - R⁻¹) / 2) with hB
  set θ : ℝ := (R + R⁻¹ - 2) / 2 with hθ
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hg : Summable (fun k : ℕ => w ^ k) := summable_geometric_of_lt_one hw0.le hw1
  have hgs : ∑' k : ℕ, w ^ k = (1 - w)⁻¹ := tsum_geometric_of_lt_one hw0.le hw1
  have hbd : ∀ k, w ^ k * Coarse.xfun (t k) ≤ (R - B * θ) * w ^ k + B * (w ^ k * t k) := by
    intro k
    have := mul_le_mul_of_nonneg_left (xfun_le_affine hR (ht k)) (pow_nonneg hw0.le k)
    calc
      _ ≤ w ^ k * (R + B * (t k - θ)) := this
      _ = _ := by ring
  have hrs : Summable (fun k => (R - B * θ) * w ^ k + B * (w ^ k * t k)) :=
    (hg.mul_left _).add (hs.mul_left _)
  have hsum : Summable (fun k => w ^ k * Coarse.xfun (t k)) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (pow_nonneg hw0.le k)
      (Coarse.xfun_pos (ht k)).le) hbd hrs
  refine ⟨hsum, ?_⟩
  have h1 := hsum.tsum_le_tsum hbd hrs
  rw [(hg.mul_left _).tsum_add (hs.mul_left _), tsum_mul_left, tsum_mul_left, hgs] at h1
  have h1w : 0 < 1 - w := by linarith
  have h2 : (1 - w) * ∑' k, w ^ k * Coarse.xfun (t k) ≤
      (1 - w) * ((R - B * θ) * (1 - w)⁻¹ + B * ∑' k, w ^ k * t k) :=
    mul_le_mul_of_nonneg_left h1 h1w.le
  have h3 : (1 - w) * ((R - B * θ) * (1 - w)⁻¹ + B * ∑' k, w ^ k * t k) =
      (R - B * θ) + B * ((1 - w) * ∑' k, w ^ k * t k) := by
    field_simp
  rw [h3] at h2
  nlinarith [mul_le_mul_of_nonneg_left hT hB0]

end GMCExplicitDelta.Localization.FluxBound
