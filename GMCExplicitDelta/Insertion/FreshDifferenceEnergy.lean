module

public import GMCExplicitDelta.Insertion.FreshWeights

/-! # The difference-gradient energy of the old competitors -/

@[expose] public section

open Homogenization Homogenization.Book.Ch02
open SubdiffusiveProcess.CoarseGrainingVocab (ScalarCoeffOnData)
open MeasureTheory hiding average
open Matrix

namespace GMCExplicitDelta.Insertion

/-- The parallelogram identity in the project's coordinate-vector convention. -/
theorem vecNormSq_add_add_sub {d : ℕ} (v u : Vec d) :
    vecNormSq (v + u) + vecNormSq (v - u) = 2 * (vecNormSq v + vecNormSq u) := by
  change (v + u) ⬝ᵥ (v + u) + (v - u) ⬝ᵥ (v - u) = 2 * (v ⬝ᵥ v + u ⬝ᵥ u)
  simp only [add_dotProduct, sub_dotProduct, dotProduct_add, dotProduct_sub]
  ring

/-- The difference-gradient energy has mass `j_e + 2`. -/
theorem average_old_difference_energy {d : ℕ} {U : Domain d} {a : Vec d → ℝ}
    (h : ScalarCoeffOnData U a) {e : Vec d} (he : e ⬝ᵥ e = 1)
    {v u : Solution U h.toCoeffOn}
    (hv : IsResponseMaximizer U h.toCoeffOn e 0 v)
    (hu : IsResponseMaximizer U h.toCoeffOn 0 e u) :
    average U (fun x => a x * vecNormSq (v.toH1.grad x - u.toH1.grad x) / 2) =
      responseJ U h.toCoeffOn e e + 2 := by
  obtain ⟨i⟩ := Coarse.nonempty_fin_of_dot_one he
  have hiW := ((Coarse.integrable_energy h i v.toH1.gradMemL2).add
    (Coarse.integrable_energy h i u.toH1.gradMemL2)).div_const 2
  have hiP := (Coarse.integrable_energy h i
    (fun j => (v.toH1.gradMemL2 j).add (u.toH1.gradMemL2 j))).div_const 2
  change Integrable (fun x => (a x * vecDot (v.toH1.grad x) (v.toH1.grad x) +
    a x * vecDot (u.toH1.grad x) (u.toH1.grad x)) / 2)
    (volumeMeasureOn (U : Set (Vec d))) at hiW
  change Integrable (fun x => a x * vecNormSq (v.toH1.grad x + u.toH1.grad x) / 2)
    (volumeMeasureOn (U : Set (Vec d))) at hiP
  have heq : (fun x => a x * vecNormSq (v.toH1.grad x - u.toH1.grad x) / 2) =
      (fun x => 2 * ((a x * vecDot (v.toH1.grad x) (v.toH1.grad x) +
        a x * vecDot (u.toH1.grad x) (u.toH1.grad x)) / 2) -
        a x * vecNormSq (v.toH1.grad x + u.toH1.grad x) / 2) := by
    funext x
    have hh := vecNormSq_add_add_sub (v.toH1.grad x) (u.toH1.grad x)
    change a x * vecNormSq (v.toH1.grad x - u.toH1.grad x) / 2 =
      2 * ((a x * vecNormSq (v.toH1.grad x) + a x * vecNormSq (u.toH1.grad x)) / 2) - _
    linear_combination a x / 2 * hh
  rw [heq, Coarse.average_sub' (hiW.const_mul 2) hiP, Coarse.average_const_mul']
  have hw := average_old_even_weight h he hv hu
  have hp := average_old_sum_energy h hv hu
  have hw' : average U (fun x => (a x * vecDot (v.toH1.grad x) (v.toH1.grad x) +
      a x * vecDot (u.toH1.grad x) (u.toH1.grad x)) / 2) = responseJ U h.toCoeffOn e e + 1 := by
    convert hw using 1
    congr 1
    funext x
    unfold vecNormSq
    ring
  rw [hw', hp]
  ring

end GMCExplicitDelta.Insertion
