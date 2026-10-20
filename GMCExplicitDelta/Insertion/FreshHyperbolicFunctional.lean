module

public import GMCExplicitDelta.Insertion.FreshHyperbolicProducts
public import GMCExplicitDelta.Insertion.FreshFormalProducts
public import GMCExplicitDelta.Insertion.FreshMomentEvaluation

/-! # The model's spatial hyperbolic-product comparison in functional form -/

@[expose] public section

open MeasureTheory Homogenization SubdiffusiveProcess.Model
open scoped ENNReal

namespace GMCExplicitDelta.Insertion

/-- S9's dependent spatial moment comparison, expressed by the exact formal
functional whose shifted-reference value is the contract band evaluation. -/
theorem layer_sum_hyperbolic_product_le_functional {d : ℕ} (M : GMCModel d)
    (I : Finset ℕ) (k : ℕ) (x : Fin k → Vec d) (p : Fin k → ℕ)
    (hp : ∀ i, p i = 1 ∨ p i = 2) (heven : Even (∑ i : Fin k, p i)) :
    (∫⁻ ω : PotentialSample d, ∏ i : Fin k,
      ENNReal.ofReal (if p i = 1 then |Real.sinh (∑ j ∈ I, ω j (x i))|
        else Real.cosh (∑ j ∈ I, ω j (x i)) - 1) ∂M.P.toMeasure) ≤
      bandMomentApply M.delta I.card
        (∏ i : Fin k, if p i = 1 then formalSinh else formalCosh - 1) := by
  change _ ≤ coefficientFunctional (bandMomentFunctional M.delta I.card)
    (∏ i : Fin k, if p i = 1 then formalSinh else formalCosh - 1)
  rw [coefficientFunctional_fin_hyperbolic _ k p hp]
  exact layer_sum_hyperbolic_product_moment_le M I k x p hp heven

end GMCExplicitDelta.Insertion
