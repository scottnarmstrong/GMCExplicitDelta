module

public import GMCExplicitDelta.Insertion.FreshModelWeightedProducts

/-! # Mixed powers of deterministic-weight even and odd fresh energies -/

@[expose] public section

open MeasureTheory Homogenization SubdiffusiveProcess.Model
open scoped ENNReal

namespace GMCExplicitDelta.Insertion

/-- The deterministic-weight transfer for each even-binomial term in I3. -/
theorem weighted_layer_sum_mixed_powers_le {d : ℕ} (M : GMCModel d) (I : Finset ℕ)
    {ν : Measure (Vec d)} [SigmaFinite ν] (w z : Vec d → ℝ≥0∞)
    (hw : Measurable w) (hz : Measurable z) (k l : ℕ) (hl : Even l) :
    (∫⁻ ω : PotentialSample d,
      (∫⁻ x, w x * ENNReal.ofReal (Real.cosh (∑ j ∈ I, ω j x) - 1) ∂ν) ^ k *
        (∫⁻ x, z x * ENNReal.ofReal |Real.sinh (∑ j ∈ I, ω j x)| ∂ν) ^ l ∂M.P.toMeasure) ≤
      (∫⁻ x, w x ∂ν) ^ k * (∫⁻ x, z x ∂ν) ^ l *
        bandMomentApply M.delta I.card ((formalCosh - 1) ^ k * formalSinh ^ l) := by
  let p : Fin (k + l) → ℕ := Fin.append (fun _ : Fin k => 2) (fun _ : Fin l => 1)
  let W : Fin (k + l) → Vec d → ℝ≥0∞ :=
    Fin.append (fun _ : Fin k => w) (fun _ : Fin l => z)
  have hp (i : Fin (k + l)) : p i = 1 ∨ p i = 2 := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [p]
    · simp [p]
  have hW (i : Fin (k + l)) : Measurable (W i) := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [W, Fin.append_left] using hw
    · simpa only [W, Fin.append_right] using hz
  have heq : (∑ i : Fin (k + l), p i) = 2 * k + l := by
    simp only [p, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
    ring
  have heven : Even (∑ i : Fin (k + l), p i) := by
    rw [heq]
    exact (even_two_mul k).add hl
  have hb := weighted_layer_sum_hyperbolic_product_le M I (ν := ν) (k + l) W hW p hp heven
  simpa only [W, p, Fin.prod_univ_add, Fin.append_left, Fin.append_right,
    ite_eq_right (by decide : (2 : ℕ) ≠ 1), ↓reduceIte,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hb

end GMCExplicitDelta.Insertion
