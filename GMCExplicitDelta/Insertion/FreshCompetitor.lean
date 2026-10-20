module

public import GMCExplicitDelta.Coarse.CompetitorsMain
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! # The old-competitor energy for insertion of an exponential field -/

@[expose] public section

open Homogenization Homogenization.Book.Ch02
open SubdiffusiveProcess.CoarseGrainingVocab (ScalarCoeffOnData)
open MeasureTheory hiding average
open Matrix

namespace GMCExplicitDelta.Insertion

/-- C12 expressed in the fresh exponential field. The gradients belong to the old
coefficient, and no maximizer for the new coefficient is selected. -/
theorem responseJ_le_exp_competitor {d : ℕ} {U : Domain d} {a a' T : Vec d → ℝ}
    (h : ScalarCoeffOnData U a) (h' : ScalarCoeffOnData U a')
    (ha' : ∀ x, a' x = a x * Real.exp (T x))
    {e : Vec d} (he : e ⬝ᵥ e = 1) {v u : Solution U h.toCoeffOn}
    (hv : IsResponseMaximizer U h.toCoeffOn e 0 v)
    (hu : IsResponseMaximizer U h.toCoeffOn 0 e u) :
    responseJ U h'.toCoeffOn e e ≤ (1 / 2) * average U (fun x =>
      a x * (Real.exp (T x) * vecNormSq (v.toH1.grad x) +
        Real.exp (-T x) * vecNormSq (u.toH1.grad x))) - 1 := by
  have hb := Coarse.responseJ_le_competitor h h' he hv hu
  refine hb.trans_eq ?_
  congr 2
  apply Coarse.average_congr_ae
  filter_upwards [Coarse.a_pos_ae h] with x hx
  rw [ha' x, _root_.mul_inv_rev, Real.exp_neg]
  unfold vecNormSq vecDot
  field_simp [hx.ne']

/-- The even and odd parts of the old energy at each spatial point. -/
theorem exp_energy_eq_even_add_odd (a V U t : ℝ) :
    a * (Real.exp t * V + Real.exp (-t) * U) / 2 =
      a * (V + U) / 2 + a * (V + U) / 2 * (Real.cosh t - 1) +
        a * (V - U) / 2 * Real.sinh t := by
  rw [Real.cosh_eq, Real.sinh_eq]
  ring

end GMCExplicitDelta.Insertion
