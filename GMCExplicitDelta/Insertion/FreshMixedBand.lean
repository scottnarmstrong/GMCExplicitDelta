module

public import GMCExplicitDelta.Insertion.FreshMixedMoment
public import GMCExplicitDelta.Insertion.FreshBandSource

/-! # The S9 bound for spatial mixed monomials in a fresh field -/

@[expose] public section

open MeasureTheory Homogenization SubdiffusiveProcess.Model
open SubdiffusiveProcess.Model.PotentialField
open scoped ENNReal

namespace GMCExplicitDelta.Insertion

/-- Every mixed spatial monomial of positive even total degree has the same sharp
S9 bound as one evaluation. There is no assumption of spatial independence. -/
theorem layer_sum_mixed_even_moment {d : ℕ} {ι : Type*} (M : GMCModel d)
    (I : Finset ℕ) (s : Finset ι) (x : ι → Vec d) (n : ι → ℕ)
    {N : ℕ} (hN : 0 < N) (hn : ∑ i ∈ s, n i = 2 * N) :
    (∫⁻ ω : PotentialSample d,
      ∏ i ∈ s, ENNReal.ofReal |∑ k ∈ I, ω k (x i)| ^ n i ∂M.P.toMeasure) ≤
      ENNReal.ofReal (((2 * N).factorial : ℝ) * (M.delta ^ 2) ^ N *
        PowerSeries.coeff N (Contract.bandSeries ^ I.card) / 2 ^ N) := by
  have hm (i : ι) : Measurable (fun ω : PotentialSample d => ∑ k ∈ I, ω k (x i)) :=
    Finset.measurable_sum I (fun k _ => (measurable_eval (x i)).comp (measurable_pi_apply k))
  refine lintegral_prod_pow_le_of_marginal_moments s
    (fun i _ => ((continuous_abs.measurable.comp (hm i)).ennreal_ofReal).aemeasurable) n (by omega) hn ?_
  intro i _
  have hb := layer_sum_band_moments M I (x i)
  have heq : (fun ω : PotentialSample d =>
      ENNReal.ofReal |∑ k ∈ I, ω k (x i)| ^ (2 * N)) =
      (fun ω : PotentialSample d => ENNReal.ofReal ((∑ k ∈ I, ω k (x i)) ^ (2 * N))) := by
    funext ω
    rw [← ENNReal.ofReal_pow (abs_nonneg _), pow_abs_two_mul]
  change (∫⁻ ω : PotentialSample d,
    ENNReal.ofReal |∑ k ∈ I, ω k (x i)| ^ (2 * N) ∂M.P.toMeasure) ≤ _
  rw [heq]
  rw [← ofReal_integral_eq_lintegral_ofReal (hb.1 (2 * N))
    (Filter.Eventually.of_forall fun ω => Even.pow_nonneg (even_two_mul N) _)]
  exact ENNReal.ofReal_le_ofReal (hb.2 N)

end GMCExplicitDelta.Insertion
