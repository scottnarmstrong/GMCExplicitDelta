module

public import GMCExplicitDelta.Insertion.FreshDifferenceEnergy
public import GMCExplicitDelta.Insertion.FreshIntegralLorentz
public import GMCExplicitDelta.Insertion.FreshSeedNorm

/-! # The sharp mass bound for the old odd weight -/

@[expose] public section

open Homogenization Homogenization.Book.Ch02
open SubdiffusiveProcess.CoarseGrainingVocab (ScalarCoeffOnData)
open MeasureTheory hiding average
open Matrix

namespace GMCExplicitDelta.Insertion

/-- I1's odd weight bound, obtained from the two gradient energies. -/
theorem average_abs_old_odd_weight {d : ℕ} {U : Domain d} {a : Vec d → ℝ}
    (h : ScalarCoeffOnData U a) {e : Vec d} (he : e ⬝ᵥ e = 1)
    {v u : Solution U h.toCoeffOn}
    (hv : IsResponseMaximizer U h.toCoeffOn e 0 v)
    (hu : IsResponseMaximizer U h.toCoeffOn 0 e u) :
    average U (fun x => |a x *
      (vecNormSq (v.toH1.grad x) - vecNormSq (u.toH1.grad x)) / 2|) ≤
      Real.sqrt (responseJ U h.toCoeffOn e e * (responseJ U h.toCoeffOn e e + 2)) := by
  obtain ⟨i⟩ := Coarse.nonempty_fin_of_dot_one he
  let ν := Assembly.domainProbability U
  have hi {f : Vec d → ℝ} (hf : Integrable f (volumeMeasureOn (U : Set (Vec d)))) :
      Integrable f ν :=
    (U.isDomain.toBoundedMeasurableDomain U.nonempty).integrable_normalizedVolume f hf
  have hae {p : Vec d → Prop} (hp : ∀ᵐ x ∂volumeMeasureOn (U : Set (Vec d)), p x) :
      ∀ᵐ x ∂ν, p x := by
    exact Measure.ae_smul_measure hp _
  have hz : Integrable (fun x => a x *
      (vecNormSq (v.toH1.grad x) - vecNormSq (u.toH1.grad x)) / 2) ν := by
    apply hi
    convert ((Coarse.integrable_energy h i v.toH1.gradMemL2).sub
      (Coarse.integrable_energy h i u.toH1.gradMemL2)).div_const 2 using 1
    funext x
    unfold vecNormSq
    simp only [Pi.sub_apply]
    ring
  have hf := hi ((Coarse.integrable_energy h i
    (fun j => (v.toH1.gradMemL2 j).add (u.toH1.gradMemL2 j))).div_const 2)
  have hg := hi ((Coarse.integrable_energy h i
    (fun j => (v.toH1.gradMemL2 j).sub (u.toH1.gradMemL2 j))).div_const 2)
  change Integrable (fun x => a x * vecNormSq (v.toH1.grad x + u.toH1.grad x) / 2) ν at hf
  change Integrable (fun x => a x * vecNormSq (v.toH1.grad x - u.toH1.grad x) / 2) ν at hg
  have ha := hae (Coarse.a_pos_ae h)
  have hnn (w : Vec d) {x : Vec d} (hx : 0 < a x) : 0 ≤ a x * vecNormSq w / 2 :=
    div_nonneg (mul_nonneg hx.le (vecNormSq_nonneg _)) (by norm_num)
  have hb := integral_abs_le_sqrt_integral_mul_sqrt_integral hz hf hg
    (ha.mono fun x hx => hnn (v.toH1.grad x + u.toH1.grad x) hx)
    (ha.mono fun x hx => hnn (v.toH1.grad x - u.toH1.grad x) hx)
    (ha.mono fun x hx => by
      have hh := abs_energy_difference_le (v.toH1.grad x) (u.toH1.grad x) hx.le
      rw [← Real.sqrt_mul (hnn (v.toH1.grad x + u.toH1.grad x) hx)] at hh
      exact (by simpa only [sq_abs] using
        ((Real.le_sqrt (abs_nonneg _) (mul_nonneg
          (hnn (v.toH1.grad x + u.toH1.grad x) hx)
          (hnn (v.toH1.grad x - u.toH1.grad x) hx))).mp hh)))
  dsimp only [ν] at hb
  rw [← Assembly.average_eq_integral_domainProbability U,
    ← Assembly.average_eq_integral_domainProbability U,
    ← Assembly.average_eq_integral_domainProbability U] at hb
  rw [average_old_sum_energy h hv hu, average_old_difference_energy h he hv hu] at hb
  rw [Real.sqrt_mul (responseJ_nonneg U h.toCoeffOn e e)]
  exact hb

end GMCExplicitDelta.Insertion
