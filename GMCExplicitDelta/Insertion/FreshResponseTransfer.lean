module

public import GMCExplicitDelta.Insertion.FreshOldEnergy

/-! # The conditional band moment of the new directional response -/

@[expose] public section

open MeasureTheory hiding average
open Homogenization Homogenization.Book.Ch02
open SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab (ScalarCoeffOnData)
open Matrix
open scoped ENNReal

namespace GMCExplicitDelta.Insertion

/-- C12 and I3 control each new directional response using the actual old response.
The old maximizers are selected only after the deterministic old coefficient is fixed. -/
theorem responseJ_exp_moment_le_band {d : ℕ} (M : GMCModel d) (I : Finset ℕ)
    {U : Domain d} {a : Vec d → ℝ} (h : ScalarCoeffOnData U a)
    (hnew : ∀ ω : PotentialSample d,
      ScalarCoeffOnData U (fun x => a x * Real.exp (∑ k ∈ I, ω k x)))
    {e : Vec d} (he : e ⬝ᵥ e = 1) :
    (∫⁻ ω : PotentialSample d, ENNReal.ofReal (responseJ U (hnew ω).toCoeffOn e e) ^ (32 : ℕ)
      ∂M.P.toMeasure) ≤ ENNReal.ofReal
        (Contract.bandSeriesEval M.delta I.card (responseJ U h.toCoeffOn e e)) := by
  obtain ⟨v, _, hv⟩ := responseMaximizerExists U h.toCoeffOn e 0
  obtain ⟨u, _, hu⟩ := responseMaximizerExists U h.toCoeffOn 0 e
  refine le_trans (lintegral_mono fun ω => ?_)
    (old_competitor_energy_moment_le M I h he hv hu)
  have hb := responseJ_le_exp_competitor h (hnew ω) (fun _ => rfl) he hv hu
  rw [half_average_eq_integral_half] at hb
  rw [← ENNReal.ofReal_pow (responseJ_nonneg U (hnew ω).toCoeffOn e e)]
  exact ENNReal.ofReal_le_ofReal
    (pow_le_pow_left₀ (responseJ_nonneg U (hnew ω).toCoeffOn e e) hb 32)

end GMCExplicitDelta.Insertion
