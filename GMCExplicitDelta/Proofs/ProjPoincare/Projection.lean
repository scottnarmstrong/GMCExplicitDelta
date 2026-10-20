module

public import GMCExplicitDelta.Proofs.ProjPoincare.Geometry
public import GMCExplicitDelta.Proofs.ProjPoincare.Digits
public import GMCExplicitDelta.Haar.PoincareCell

/-! Identification of the first Haar energy with the child-digit variance. -/
@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators

namespace GMCExplicitDelta.Localization.ProjPoincare

theorem childCube_injective {d : ℕ} (Q : TriadicCube d) :
    Function.Injective (childCube Q) := by
  intro a b h
  funext i
  apply Fin.ext
  have hi := congrFun (congrArg TriadicCube.index h) i
  dsimp only [childCube] at hi
  omega

theorem descendantsAverage_child {d : ℕ} (Q : TriadicCube d) (F : TriadicCube d → ℝ) :
    descendantsAverage Q 1 F = ((3 : ℝ) ^ d)⁻¹ * ∑ a, F (childCube Q a) := by
  classical
  unfold descendantsAverage
  dsimp only
  rw [descendantsAtDepth_one, childCubes_card]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  congr 1
  unfold childCubes
  rw [Finset.sum_image]
  · rfl
  · exact fun a _ b _ h => childCube_injective Q h

theorem firstIncrement_energy_child {d : ℕ} (Q : TriadicCube d) (v : Vec d → ℝ) :
    Haar.energy Q (cubeIncrement Q 1 v) =
      descendantsAverage Q 1 (fun R => (cubeAverage R v - cubeAverage Q v) ^ 2) := by
  rw [Haar.energy_eq_descendantsAverage Q 1 (Haar.increment_memLp Q 1 v)]
  unfold descendantsAverage
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro R hR
  unfold Haar.energy Haar.pairing
  calc
    cubeAverage R (fun x => cubeIncrement Q 1 v x * cubeIncrement Q 1 v x) =
        cubeAverage R (fun _ => (cubeAverage R v - cubeAverage Q v) ^ 2) := by
      apply cubeAverage_congr_on_cubeSet
      intro x hx
      rw [cubeIncrement_succ]
      dsimp only
      rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth v hR hx,
        cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth v
          (by simp : Q ∈ descendantsAtDepth Q 0)
          (cubeSet_subset_of_mem_descendantsAtDepth hR hx)]
      ring
    _ = _ := cubeAverage_const R _

theorem cubeAverage_eq_digit_average {d : ℕ} (Q : TriadicCube d) {v : Vec d → ℝ}
    (hv : Continuous v) : cubeAverage Q v = ∫ b, cubeAverage (childCube Q b) v
      ∂(Measure.pi fun _ : Fin d => digitMeasure) := by
  rw [digitPi_integral, ← descendantsAverage_child Q (fun R => cubeAverage R v)]
  exact cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q 1 v
    (integrableOn_of_integrable_normalizedCubeMeasure Q
      (memLp_one_iff_integrable.mp (continuous_memLp_cube Q hv 1)))

theorem firstIncrement_energy_digits {d : ℕ} (Q : TriadicCube d) {v : Vec d → ℝ}
    (hv : Continuous v) :
    Haar.energy Q (cubeIncrement Q 1 v) =
      ∫ a, (cubeAverage (childCube Q a) v -
        ∫ b, cubeAverage (childCube Q b) v ∂(Measure.pi fun _ => digitMeasure)) ^ 2
          ∂(Measure.pi fun _ : Fin d => digitMeasure) := by
  rw [firstIncrement_energy_child, descendantsAverage_child, digitPi_integral,
    cubeAverage_eq_digit_average Q hv]

end GMCExplicitDelta.Localization.ProjPoincare
