module

public import GMCExplicitDelta.Proofs.ProjPoincare.Scale
public import GMCExplicitDelta.Proofs.ProjPoincare.Geometry

/-! The three interval averages appearing in a coordinate slice. -/
@[expose] public section

open MeasureTheory Homogenization
open scoped BigOperators

namespace GMCExplicitDelta.Localization.ProjPoincare

noncomputable def thirdAverage (a S : ℝ) (f : ℝ → ℝ) : Fin 3 → ℝ :=
  ![3 / S * ∫ t in a..(a + S / 3), f t,
    3 / S * ∫ t in (a + S / 3)..(a + 2 * S / 3), f t,
    3 / S * ∫ t in (a + 2 * S / 3)..(a + S), f t]

theorem thirdAverage_mean (a S : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    (1 / 3 : ℝ) * ∑ r, thirdAverage a S f r = S⁻¹ * ∫ t in a..(a + S), f t := by
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable a (a + S / 3))
    (hf.intervalIntegrable (a + S / 3) (a + 2 * S / 3))
  have hsplit' := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable a (a + 2 * S / 3))
    (hf.intervalIntegrable (a + 2 * S / 3) (a + S))
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, thirdAverage,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  rw [← hsplit', ← hsplit]
  ring

theorem thirdAverage_variance_le {v g : ℝ → ℝ} (hv : Continuous v) (hg : Continuous g)
    (hd : ∀ t, HasDerivAt v (g t) t) (a S : ℝ) (hS : 0 < S) :
    (1 / 3 : ℝ) * ∑ r,
      (thirdAverage a S v r - (1 / 3 : ℝ) * ∑ s, thirdAverage a S v s) ^ 2 ≤
      (5 / 54 : ℝ) * S ^ 2 * (S⁻¹ * ∫ t in a..(a + S), g t ^ 2) := by
  rw [thirdAverage_mean a S hv]
  have h := thirds_projected_poincare_interval hv hg hd a S hS
  dsimp only at h
  convert h using 1
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, thirdAverage,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  ring

theorem faceCube_child (n : ℕ) (Q : TriadicCube (n + 1)) (i : Fin (n + 1))
    (r : Fin 3) (z : Fin n → Fin 3) :
    faceCube (childCube Q (i.insertNth r z)) i = childCube (faceCube Q i) z := by
  simp only [faceCube, childCube, Fin.insertNth_apply_succAbove]

/-- A child average is an average, over its other coordinates, of a third-interval average. -/
theorem childAverage_slice (n : ℕ) (Q : TriadicCube (n + 1)) (i : Fin (n + 1))
    (r : Fin 3) (z : Fin n → Fin 3) {v : Vec (n + 1) → ℝ} (hv : Continuous v) :
    cubeAverage (childCube Q (i.insertNth r z)) v =
      cubeAverage (childCube (faceCube Q i) z) (fun x =>
        thirdAverage (((Q.index i : ℝ) - 1 / 2) * cubeScaleFactor Q)
          (cubeScaleFactor Q) (fun t => v (i.insertNth t x)) r) := by
  let R := childCube Q (i.insertNth r z)
  rw [cubeAverage_peel R i (memLp_one_iff_integrable.mp (continuous_memLp_cube R hv 1)),
    faceCube_child]
  congr 1
  funext x
  rw [coord_integral]
  have hscale : cubeScaleFactor R = cubeScaleFactor Q / 3 := cubeScaleFactor_childCube Q _
  have hlo : ((R.index i : ℝ) - 1 / 2) * cubeScaleFactor R =
      ((Q.index i : ℝ) - 1 / 2) * cubeScaleFactor Q + (r : ℝ) * cubeScaleFactor Q / 3 := by
    rw [hscale]
    dsimp [R, childCube]
    simp only [Fin.insertNth_apply_same, Int.cast_sub, Int.cast_add, Int.cast_mul,
      Int.cast_ofNat, Int.cast_one, Int.cast_natCast]
    ring
  have hhi : ((R.index i : ℝ) + 1 / 2) * cubeScaleFactor R =
      ((Q.index i : ℝ) - 1 / 2) * cubeScaleFactor Q + ((r : ℝ) + 1) * cubeScaleFactor Q / 3 := by
    rw [hscale]
    dsimp [R, childCube]
    simp only [Fin.insertNth_apply_same, Int.cast_sub, Int.cast_add, Int.cast_mul,
      Int.cast_ofNat, Int.cast_one, Int.cast_natCast]
    ring
  rw [hlo, hhi, hscale]
  have hthree : (3 : ℝ) * (cubeScaleFactor Q * (1 / 3)) = cubeScaleFactor Q := by ring
  fin_cases r <;> norm_num [thirdAverage, div_eq_mul_inv, mul_add, add_mul, mul_assoc, hthree]

end GMCExplicitDelta.Localization.ProjPoincare
