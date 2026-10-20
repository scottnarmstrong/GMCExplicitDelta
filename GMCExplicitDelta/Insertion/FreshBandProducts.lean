module

public import GMCExplicitDelta.Insertion.FreshProductMoment
public import GMCExplicitDelta.Insertion.FreshMomentFunctional

/-! # The sharp dependent spatial Taylor-product comparison for the model -/

@[expose] public section

open MeasureTheory Homogenization SubdiffusiveProcess.Model
open SubdiffusiveProcess.Model.PotentialField
open scoped ENNReal

namespace GMCExplicitDelta.Insertion

/-- I3's spatial mixed-product comparison, with the marginal bounds discharged
by S9. The parity premise is algebraic; spatial independence is unnecessary. -/
theorem layer_sum_product_series_moment_le {d : ℕ} (M : GMCModel d)
    (I : Finset ℕ) (k : ℕ) (x : Fin k → Vec d)
    (a : Fin k → ℕ → ℝ≥0∞) (degree : Fin k → ℕ → ℕ)
    (heven : ∀ n : Fin k → ℕ, Even (∑ i : Fin k, degree i (n i))) :
    (∫⁻ ω : PotentialSample d, ∏ i : Fin k, ∑' n : ℕ,
      a i n * ENNReal.ofReal |∑ j ∈ I, ω j (x i)| ^ degree i n ∂M.P.toMeasure) ≤
      ∑' n : Fin k → ℕ, (∏ i : Fin k, a i (n i)) *
        bandMomentFunctional M.delta I.card (∑ i : Fin k, degree i (n i)) := by
  have hm (i : Fin k) : Measurable (fun ω : PotentialSample d => ∑ j ∈ I, ω j (x i)) :=
    Finset.measurable_sum I (fun j _ => (measurable_eval (x i)).comp (measurable_pi_apply j))
  exact lintegral_prod_tsum_pow_le k
    (fun i => ((continuous_abs.measurable.comp (hm i)).ennreal_ofReal).aemeasurable)
    a degree (bandMomentFunctional M.delta I.card)
    (bandMomentFunctional_zero M.delta I.card)
    (fun n _ i => layer_sum_abs_even_moment_functional M I (x i) (heven n))

end GMCExplicitDelta.Insertion
