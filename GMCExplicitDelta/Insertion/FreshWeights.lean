module

public import GMCExplicitDelta.Insertion.FreshCompetitor

/-! # The mass of the deterministic old competitor weight -/

@[expose] public section

open Homogenization Homogenization.Book.Ch02
open SubdiffusiveProcess.CoarseGrainingVocab (ScalarCoeffOnData)
open MeasureTheory hiding average
open Matrix

namespace GMCExplicitDelta.Insertion

/-- The nonnegative even weight has mass `j_e + 1`, with the old response `j_e`. -/
theorem average_old_even_weight {d : ℕ} {U : Domain d} {a : Vec d → ℝ}
    (h : ScalarCoeffOnData U a) {e : Vec d} (he : e ⬝ᵥ e = 1)
    {v u : Solution U h.toCoeffOn}
    (hv : IsResponseMaximizer U h.toCoeffOn e 0 v)
    (hu : IsResponseMaximizer U h.toCoeffOn 0 e u) :
    average U (fun x => a x *
      (vecNormSq (v.toH1.grad x) + vecNormSq (u.toH1.grad x)) / 2) =
      responseJ U h.toCoeffOn e e + 1 := by
  obtain ⟨i⟩ := Coarse.nonempty_fin_of_dot_one he
  have hsym := Coarse.scalarCoeffOn_isSymmetric h
  have hV := Coarse.average_energy_v hsym hv
  have hU := Coarse.average_energy_u hsym hu
  simp_rw [Coarse.vecDot_scalar_coeff] at hV hU
  have heq : (fun x => a x *
      (vecNormSq (v.toH1.grad x) + vecNormSq (u.toH1.grad x)) / 2) =
      (fun x => (1 / 2 : ℝ) * (a x * vecDot (v.toH1.grad x) (v.toH1.grad x) +
        a x * vecDot (u.toH1.grad x) (u.toH1.grad x))) := by
    funext x
    unfold vecNormSq
    ring
  rw [heq, Coarse.average_const_mul', Coarse.average_add'
    (Coarse.integrable_energy h i v.toH1.gradMemL2)
    (Coarse.integrable_energy h i u.toH1.gradMemL2), hV, hU,
    Coarse.responseJ_eq_XY hsym, he]
  ring

/-- The sum-gradient energy is precisely the old response. -/
theorem average_old_sum_energy {d : ℕ} {U : Domain d} {a : Vec d → ℝ}
    (h : ScalarCoeffOnData U a) {e : Vec d}
    {v u : Solution U h.toCoeffOn}
    (hv : IsResponseMaximizer U h.toCoeffOn e 0 v)
    (hu : IsResponseMaximizer U h.toCoeffOn 0 e u) :
    average U (fun x => a x * vecNormSq (v.toH1.grad x + u.toH1.grad x) / 2) =
      responseJ U h.toCoeffOn e e := by
  have hb := Coarse.half_average_energy_sum (Coarse.scalarCoeffOn_isSymmetric h) hv hu
  simp_rw [Coarse.vecDot_scalar_coeff] at hb
  have heq : (fun x => a x * vecNormSq (v.toH1.grad x + u.toH1.grad x) / 2) =
      (fun x => (1 / 2 : ℝ) * (a x *
        vecDot (v.toH1.grad x + u.toH1.grad x) (v.toH1.grad x + u.toH1.grad x))) := by
    funext x
    unfold vecNormSq
    ring
  rw [heq, Coarse.average_const_mul']
  exact hb

end GMCExplicitDelta.Insertion
