module

public import GMCExplicitDelta.Insertion.FreshDeterministicTransfer

/-! # The conditional transfer for Sobolev energy weights -/

@[expose] public section

open MeasureTheory Homogenization SubdiffusiveProcess.Model
open scoped ENNReal

namespace GMCExplicitDelta.Insertion

/-- I3 only needs integrable weights and almost-everywhere nonnegativity, as
provided by the old Sobolev maximizers. Measurable representatives are chosen
without changing any spatial energy for any fresh sample. -/
theorem deterministic_weight_moment_transfer_ae {d : ℕ} (M : GMCModel d) (I : Finset ℕ)
    {ν : Measure (Vec d)} [SigmaFinite ν] {w z : Vec d → ℝ}
    (hiw : Integrable w ν) (hiz : Integrable z ν) (hw0 : ∀ᵐ x ∂ν, 0 ≤ w x)
    {j : ℝ} (hj : 0 ≤ j) (hwmass : ∫ x, w x ∂ν = j + 1)
    (hzmass : ∫ x, |z x| ∂ν ≤ Real.sqrt (j * (j + 2))) :
    (∫⁻ ω : PotentialSample d, ENNReal.ofReal
      ((j + freshEvenEnergy I ν w ω + freshOddEnergy I ν z ω) ^ (32 : ℕ)) ∂M.P.toMeasure) ≤
      ENNReal.ofReal (Contract.bandSeriesEval M.delta I.card j) := by
  have hwa := hiw.aestronglyMeasurable.aemeasurable
  have hza := hiz.aestronglyMeasurable.aemeasurable
  let w' : Vec d → ℝ := fun x => max (hwa.mk w x) 0
  let z' : Vec d → ℝ := hza.mk z
  have hwm : Measurable w' := hwa.measurable_mk.max measurable_const
  have hzm : Measurable z' := hza.measurable_mk
  have hwp (x : Vec d) : 0 ≤ w' x := le_max_right _ _
  have hew : w' =ᵐ[ν] w := by
    filter_upwards [hwa.ae_eq_mk, hw0] with x hx hp
    change max (hwa.mk w x) 0 = w x
    rw [← hx, max_eq_left hp]
  have hez : z' =ᵐ[ν] z := hza.ae_eq_mk.symm
  have hiw' : Integrable w' ν := hiw.congr hew.symm
  have hiz' : Integrable z' ν := hiz.congr hez.symm
  have hwmass' : ∫ x, w' x ∂ν = j + 1 := (integral_congr_ae hew).trans hwmass
  have hzmass' : ∫ x, |z' x| ∂ν ≤ Real.sqrt (j * (j + 2)) :=
    (integral_congr_ae (hez.mono fun x hx => congrArg abs hx)).trans_le hzmass
  have hE (ω : PotentialSample d) : freshEvenEnergy I ν w' ω = freshEvenEnergy I ν w ω := by
    apply integral_congr_ae
    filter_upwards [hew] with x hx
    rw [hx]
  have hO (ω : PotentialSample d) : freshOddEnergy I ν z' ω = freshOddEnergy I ν z ω := by
    apply integral_congr_ae
    filter_upwards [hez] with x hx
    rw [hx]
  have hb := deterministic_weight_moment_transfer M I hwm hzm hwp hiw' hiz' hj hwmass' hzmass'
  refine le_trans (le_of_eq (lintegral_congr fun ω => ?_)) hb
  rw [hE, hO]

end GMCExplicitDelta.Insertion
