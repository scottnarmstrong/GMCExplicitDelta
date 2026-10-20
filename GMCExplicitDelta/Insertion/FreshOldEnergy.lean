module

public import GMCExplicitDelta.Insertion.FreshOldWeights
public import GMCExplicitDelta.Insertion.FreshSpatialBounded

/-! # The exponential old competitor equals its even/odd weighted decomposition -/

@[expose] public section

open MeasureTheory hiding average
open Homogenization Homogenization.Book.Ch02
open SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab (ScalarCoeffOnData)
open Matrix
open scoped ENNReal

namespace GMCExplicitDelta.Insertion

theorem half_average_eq_integral_half {d : ℕ} (U : Domain d) (f : Vec d → ℝ) :
    (1 / 2 : ℝ) * average U f = ∫ x, f x / 2 ∂Assembly.domainProbability U := by
  rw [Assembly.average_eq_integral_domainProbability, ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by ring

/-- I1's exact weighted decomposition, with spatial integrability proved from
boundedness of the continuous fresh field on the deterministic domain. -/
theorem old_competitor_energy_eq_weighted {d : ℕ} (I : Finset ℕ)
    {U : Domain d} {a : Vec d → ℝ} (h : ScalarCoeffOnData U a)
    {e : Vec d} (he : e ⬝ᵥ e = 1) {v u : Solution U h.toCoeffOn}
    (hv : IsResponseMaximizer U h.toCoeffOn e 0 v)
    (hu : IsResponseMaximizer U h.toCoeffOn 0 e u) (ω : PotentialSample d) :
    (∫ x, a x * (Real.exp (∑ k ∈ I, ω k x) * vecNormSq (v.toH1.grad x) +
      Real.exp (-(∑ k ∈ I, ω k x)) * vecNormSq (u.toH1.grad x)) / 2
      ∂Assembly.domainProbability U) - 1 = responseJ U h.toCoeffOn e e +
        freshEvenEnergy I (Assembly.domainProbability U)
          (competitorEvenWeight a v.toH1.grad u.toH1.grad) ω +
        freshOddEnergy I (Assembly.domainProbability U)
          (competitorOddWeight a v.toH1.grad u.toH1.grad) ω := by
  obtain ⟨i⟩ := Coarse.nonempty_fin_of_dot_one he
  let w := competitorEvenWeight a v.toH1.grad u.toH1.grad
  let z := competitorOddWeight a v.toH1.grad u.toH1.grad
  have hiw : Integrable w (Assembly.domainProbability U) := (U.isDomain.toBoundedMeasurableDomain U.nonempty).integrable_normalizedVolume _
    (integrable_competitorEvenWeight h i v.toH1.gradMemL2 u.toH1.gradMemL2)
  have hiz : Integrable z (Assembly.domainProbability U) := (U.isDomain.toBoundedMeasurableDomain U.nonempty).integrable_normalizedVolume _
    (integrable_competitorOddWeight h i v.toH1.gradMemL2 u.toH1.gradMemL2)
  have hcT : Continuous (fun x : Vec d => ∑ k ∈ I, ω k x) :=
    continuous_finsetSum I (fun k _ => (ω k).1.1.continuous)
  have hiE : Integrable (fun x => w x * (Real.cosh (∑ k ∈ I, ω k x) - 1))
      (Assembly.domainProbability U) := integrable_domainProbability_mul_continuous hiw
    ((Real.continuous_cosh.comp hcT).sub continuous_const)
  have hiO : Integrable (fun x => z x * Real.sinh (∑ k ∈ I, ω k x))
      (Assembly.domainProbability U) :=
    integrable_domainProbability_mul_continuous hiz (Real.continuous_sinh.comp hcT)
  have hiWE : Integrable (fun x => w x + w x * (Real.cosh (∑ k ∈ I, ω k x) - 1))
      (Assembly.domainProbability U) := hiw.add hiE
  have hM : (∫ x, w x ∂Assembly.domainProbability U) = responseJ U h.toCoeffOn e e + 1 := by
    rw [← Assembly.average_eq_integral_domainProbability]
    exact average_old_even_weight h he hv hu
  have hpoint (x : Vec d) : a x *
      (Real.exp (∑ k ∈ I, ω k x) * vecNormSq (v.toH1.grad x) +
        Real.exp (-(∑ k ∈ I, ω k x)) * vecNormSq (u.toH1.grad x)) / 2 =
      w x + w x * (Real.cosh (∑ k ∈ I, ω k x) - 1) + z x * Real.sinh (∑ k ∈ I, ω k x) :=
    exp_energy_eq_even_add_odd _ _ _ _
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint), integral_add hiWE hiO,
    integral_add hiw hiE, hM]
  change (responseJ U h.toCoeffOn e e + 1 + _ + _) - 1 = _
  unfold freshEvenEnergy freshOddEnergy
  dsimp only [w, z]
  ring

/-- I3 for the literal exponential old-competitor energy. -/
theorem old_competitor_energy_moment_le {d : ℕ} (M : GMCModel d) (I : Finset ℕ)
    {U : Domain d} {a : Vec d → ℝ} (h : ScalarCoeffOnData U a)
    {e : Vec d} (he : e ⬝ᵥ e = 1) {v u : Solution U h.toCoeffOn}
    (hv : IsResponseMaximizer U h.toCoeffOn e 0 v)
    (hu : IsResponseMaximizer U h.toCoeffOn 0 e u) :
    (∫⁻ ω : PotentialSample d, ENNReal.ofReal (((∫ x, a x *
      (Real.exp (∑ k ∈ I, ω k x) * vecNormSq (v.toH1.grad x) +
        Real.exp (-(∑ k ∈ I, ω k x)) * vecNormSq (u.toH1.grad x)) / 2
      ∂Assembly.domainProbability U) - 1) ^ (32 : ℕ)) ∂M.P.toMeasure) ≤
      ENNReal.ofReal (Contract.bandSeriesEval M.delta I.card (responseJ U h.toCoeffOn e e)) := by
  refine le_trans (le_of_eq (lintegral_congr fun ω => ?_))
    (old_competitor_weighted_moment M I h he hv hu)
  rw [old_competitor_energy_eq_weighted I h he hv hu ω]

end GMCExplicitDelta.Insertion
