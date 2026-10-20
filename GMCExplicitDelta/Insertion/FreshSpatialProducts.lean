module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-! # Nonnegative finite spatial products and Tonelli -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace GMCExplicitDelta.Insertion

/-- Nonnegative finite-product Fubini on repeated copies of a spatial domain. -/
theorem lintegral_fin_product_eq_product {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [SigmaFinite ν] {k : ℕ}
    (f : Fin k → S → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x : Fin k → S, ∏ i : Fin k, f i (x i) ∂Measure.pi (fun _ : Fin k => ν)) =
      ∏ i : Fin k, ∫⁻ x, f i x ∂ν := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hm : Measurable (fun x : Fin k → S => ∏ i : Fin k, f i.succ (x i)) :=
      Finset.measurable_prod Finset.univ (fun i _ => (hf i.succ).comp (measurable_pi_apply i))
    calc
      _ = ∫⁻ x : S × (Fin k → S), f 0 x.1 * ∏ i : Fin k, f i.succ (x.2 i)
          ∂ν.prod (Measure.pi (fun _ : Fin k => ν)) := by
        rw [← ((measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => ν) 0).symm).lintegral_comp_emb
          (MeasurableEquiv.measurableEmbedding _)]
        apply lintegral_congr
        intro x
        simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
          Fin.zero_succAbove, cast_eq, Fin.cons_zero]
      _ = (∫⁻ x, f 0 x ∂ν) * ∏ i : Fin k, ∫⁻ x, f i.succ x ∂ν := by
        rw [lintegral_prod_mul (hf 0).aemeasurable hm.aemeasurable,
          ih (fun i => f i.succ) (fun i => hf i.succ)]
      _ = _ := by rw [Fin.prod_univ_succ]

end GMCExplicitDelta.Insertion
