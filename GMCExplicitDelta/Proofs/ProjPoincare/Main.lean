module

public import GMCExplicitDelta.Proofs.ProjPoincare.Tensor

/-! The sharp first-level projected triadic Poincaré inequality. -/
@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators

namespace GMCExplicitDelta.Localization

open ProjPoincare

variable {d : ℕ}

theorem projected_poincare_proof (hd : 1 ≤ d) (U : Homogenization.TriadicCube d)
    {v : Homogenization.Vec d → ℝ} {g : Fin d → Homogenization.Vec d → ℝ}
    (hv : Continuous v) (hg : ∀ i, Continuous (g i))
    (hder : ∀ (i : Fin d) (x : Homogenization.Vec d),
      HasDerivAt (fun t => v (Function.update x i t)) (g i x) (x i)) :
    Haar.energy U (cubeIncrement U 1 v) ≤
      5 / 54 * cubeScaleFactor U ^ 2 * ∑ i, Haar.energy U (g i) := by
  cases d with
  | zero => omega
  | succ n =>
    rw [firstIncrement_energy_digits U hv, Finset.mul_sum]
    refine (child_digits_conditional_variance n (fun a => cubeAverage (childCube U a) v)).trans ?_
    apply Finset.sum_le_sum
    intro i _
    let H : Vec n → ℝ := fun x => ∫ t, (g i (i.insertNth t x)) ^ 2 ∂coordMeasure U i
    have hH : Continuous H := continuous_slice_integral U i ((hg i).pow 2)
    have hmono : (∫ z, ∫ r,
        (cubeAverage (childCube U (i.insertNth r z)) v -
          ∫ s, cubeAverage (childCube U (i.insertNth s z)) v ∂digitMeasure) ^ 2
            ∂digitMeasure ∂(Measure.pi fun _ : Fin n => digitMeasure)) ≤
        ∫ z, (5 / 54 : ℝ) * cubeScaleFactor U ^ 2 *
          cubeAverage (childCube (faceCube U i) z) H
            ∂(Measure.pi fun _ : Fin n => digitMeasure) := by
      apply integral_mono (memLp_one_iff_integrable.mp MemLp.of_discrete)
        (memLp_one_iff_integrable.mp MemLp.of_discrete)
      intro z
      simp_rw [digit_integral]
      exact conditional_child_bound U i hv hg hder z
    refine hmono.trans_eq ?_
    rw [integral_const_mul, ← cubeAverage_eq_digit_average (faceCube U i) hH]
    have hint : Integrable (fun x => (g i x) ^ 2) (normalizedCubeMeasure U) :=
      memLp_one_iff_integrable.mp (continuous_memLp_cube U ((hg i).pow 2) 1)
    rw [← cubeAverage_peel U i hint]
    simp only [Haar.energy, Haar.pairing, pow_two]

end GMCExplicitDelta.Localization
