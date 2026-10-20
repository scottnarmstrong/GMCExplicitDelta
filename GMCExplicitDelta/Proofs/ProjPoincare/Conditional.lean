module

public import GMCExplicitDelta.Proofs.ProjPoincare.Slices
public import GMCExplicitDelta.Proofs.ProjPoincare.Finite

/-! Contraction of the conditional three-cell variance under spatial averaging. -/
@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators

namespace GMCExplicitDelta.Localization.ProjPoincare

theorem third_variance_average_le {d : ℕ} (Q : TriadicCube d)
    (f : Fin 3 → Vec d → ℝ) (hf : ∀ r, Continuous (f r)) :
    (1 / 3 : ℝ) * ∑ r,
      (cubeAverage Q (f r) - (1 / 3 : ℝ) * ∑ s, cubeAverage Q (f s)) ^ 2 ≤
    cubeAverage Q (fun x => (1 / 3 : ℝ) * ∑ r,
      (f r x - (1 / 3 : ℝ) * ∑ s, f s x) ^ 2) := by
  let m : Vec d → ℝ := fun x => (1 / 3 : ℝ) * ∑ s, f s x
  have hm : Continuous m := continuous_const.mul (continuous_finsetSum _ (fun s _ => hf s))
  have hint (r : Fin 3) : Integrable (f r) (normalizedCubeMeasure Q) :=
    memLp_one_iff_integrable.mp (continuous_memLp_cube Q (hf r) 1)
  have hm_int : Integrable m (normalizedCubeMeasure Q) :=
    memLp_one_iff_integrable.mp (continuous_memLp_cube Q hm 1)
  have hlin (r : Fin 3) : cubeAverage Q (fun x => f r x - m x) =
      cubeAverage Q (f r) - (1 / 3 : ℝ) * ∑ s, cubeAverage Q (f s) := by
    simp only [cubeAverage_eq_integral_normalizedCubeMeasure]
    rw [integral_sub (hint r) hm_int]
    dsimp only [m]
    rw [integral_const_mul, integral_finsetSum _ (fun s _ => hint s)]
  have hsq (r : Fin 3) : (cubeAverage Q (fun x => f r x - m x)) ^ 2 ≤
      cubeAverage Q (fun x => (f r x - m x) ^ 2) :=
    cubeAverage_sq_le Q (continuous_memLp_cube Q ((hf r).sub hm) 2)
  simp only [hlin] at hsq
  have hsum := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s := Finset.univ) (fun r _ => hsq r))
    (by norm_num : (0 : ℝ) ≤ 1 / 3)
  refine hsum.trans_eq ?_
  simp only [cubeAverage_eq_integral_normalizedCubeMeasure]
  have hint_sq (r : Fin 3) : Integrable (fun x => (f r x - m x) ^ 2) (normalizedCubeMeasure Q) :=
    memLp_one_iff_integrable.mp (continuous_memLp_cube Q (((hf r).sub hm).pow 2) 1)
  rw [integral_const_mul]
  change _ = (1 / 3 : ℝ) * ∫ x, ∑ r, (f r x - m x) ^ 2 ∂normalizedCubeMeasure Q
  rw [integral_finsetSum _ (fun r _ => hint_sq r)]

end GMCExplicitDelta.Localization.ProjPoincare
