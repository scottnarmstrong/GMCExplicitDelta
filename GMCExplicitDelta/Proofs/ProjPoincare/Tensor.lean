module

public import GMCExplicitDelta.Proofs.ProjPoincare.Conditional
public import GMCExplicitDelta.Proofs.ProjPoincare.Projection

/-! Coordinate slices for tensorizing the sharp projected Poincaré estimate. -/
@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators

namespace GMCExplicitDelta.Localization.ProjPoincare

theorem continuous_thirdAverage {n : ℕ} (i : Fin (n + 1))
    {v : Vec (n + 1) → ℝ} (hv : Continuous v) (a S : ℝ) (r : Fin 3) :
    Continuous (fun x : Vec n => thirdAverage a S (fun t => v (i.insertNth t x)) r) := by
  have hc : Continuous (Function.uncurry (fun x : Vec n => fun t : ℝ => v (i.insertNth t x))) :=
    hv.comp (continuous_snd.finInsertNth (A := fun _ => ℝ) i continuous_fst)
  have hint (a b : ℝ) : Continuous (fun x : Vec n => ∫ t in a..b, v (i.insertNth t x)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hc a b
  fin_cases r <;> exact continuous_const.mul (hint _ _)

theorem continuous_slice_integral {n : ℕ} (Q : TriadicCube (n + 1)) (i : Fin (n + 1))
    {v : Vec (n + 1) → ℝ} (hv : Continuous v) :
    Continuous (fun x : Vec n => ∫ t, v (i.insertNth t x) ∂coordMeasure Q i) := by
  simp_rw [coord_integral]
  have hc : Continuous (Function.uncurry (fun x : Vec n => fun t : ℝ => v (i.insertNth t x))) :=
    hv.comp (continuous_snd.finInsertNth (A := fun _ => ℝ) i continuous_fst)
  exact continuous_const.mul
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hc _ _)

theorem coordinate_slice_bound {n : ℕ} (Q : TriadicCube (n + 1)) (i : Fin (n + 1))
    {v : Vec (n + 1) → ℝ} {g : Fin (n + 1) → Vec (n + 1) → ℝ}
    (hv : Continuous v) (hg : ∀ j, Continuous (g j))
    (hd : ∀ (j : Fin (n + 1)) (x : Vec (n + 1)),
      HasDerivAt (fun t => v (Function.update x j t)) (g j x) (x j)) (x : Vec n) :
    let a := ((Q.index i : ℝ) - 1 / 2) * cubeScaleFactor Q
    let S := cubeScaleFactor Q
    (1 / 3 : ℝ) * ∑ r,
      (thirdAverage a S (fun t => v (i.insertNth t x)) r -
        (1 / 3 : ℝ) * ∑ s, thirdAverage a S (fun t => v (i.insertNth t x)) s) ^ 2 ≤
      (5 / 54 : ℝ) * S ^ 2 * ∫ t, (g i (i.insertNth t x)) ^ 2 ∂coordMeasure Q i := by
  have hv' : Continuous (fun t : ℝ => v (i.insertNth t x)) :=
    hv.comp (continuous_id.finInsertNth (A := fun _ => ℝ) i continuous_const)
  have hg' : Continuous (fun t : ℝ => g i (i.insertNth t x)) :=
    (hg i).comp (continuous_id.finInsertNth (A := fun _ => ℝ) i continuous_const)
  have hd' (t : ℝ) : HasDerivAt (fun s => v (i.insertNth s x)) (g i (i.insertNth t x)) t := by
    simpa only [Fin.update_insertNth, Fin.insertNth_apply_same] using hd i (i.insertNth t x)
  have hS : 0 < cubeScaleFactor Q := by unfold cubeScaleFactor; positivity
  have h := thirdAverage_variance_le hv' hg' hd'
    (((Q.index i : ℝ) - 1 / 2) * cubeScaleFactor Q) (cubeScaleFactor Q) hS
  dsimp only
  rw [coord_integral]
  have he : ((Q.index i : ℝ) - 1 / 2) * cubeScaleFactor Q + cubeScaleFactor Q =
      ((Q.index i : ℝ) + 1 / 2) * cubeScaleFactor Q := by ring
  rwa [he] at h

theorem conditional_child_bound {n : ℕ} (Q : TriadicCube (n + 1)) (i : Fin (n + 1))
    {v : Vec (n + 1) → ℝ} {g : Fin (n + 1) → Vec (n + 1) → ℝ}
    (hv : Continuous v) (hg : ∀ j, Continuous (g j))
    (hd : ∀ (j : Fin (n + 1)) (x : Vec (n + 1)),
      HasDerivAt (fun t => v (Function.update x j t)) (g j x) (x j)) (z : Fin n → Fin 3) :
    (1 / 3 : ℝ) * ∑ r,
      (cubeAverage (childCube Q (i.insertNth r z)) v -
        (1 / 3 : ℝ) * ∑ s, cubeAverage (childCube Q (i.insertNth s z)) v) ^ 2 ≤
      (5 / 54 : ℝ) * cubeScaleFactor Q ^ 2 *
        cubeAverage (childCube (faceCube Q i) z)
          (fun x => ∫ t, (g i (i.insertNth t x)) ^ 2 ∂coordMeasure Q i) := by
  let R := childCube (faceCube Q i) z
  let a := ((Q.index i : ℝ) - 1 / 2) * cubeScaleFactor Q
  let S := cubeScaleFactor Q
  let f : Fin 3 → Vec n → ℝ := fun r x => thirdAverage a S (fun t => v (i.insertNth t x)) r
  have hf (r : Fin 3) : Continuous (f r) := continuous_thirdAverage i hv a S r
  have hmean : Continuous (fun x => (1 / 3 : ℝ) * ∑ s, f s x) :=
    continuous_const.mul (continuous_finsetSum _ (fun s _ => hf s))
  have hvar : Continuous (fun x => (1 / 3 : ℝ) * ∑ r,
      (f r x - (1 / 3 : ℝ) * ∑ s, f s x) ^ 2) :=
    continuous_const.mul (continuous_finsetSum _ (fun r _ => ((hf r).sub hmean).pow 2))
  have hG : Continuous (fun x : Vec n => ∫ t, (g i (i.insertNth t x)) ^ 2 ∂coordMeasure Q i) :=
    continuous_slice_integral Q i ((hg i).pow 2)
  have hRcont : Continuous (fun x : Vec n => (5 / 54 : ℝ) * cubeScaleFactor Q ^ 2 *
      ∫ t, (g i (i.insertNth t x)) ^ 2 ∂coordMeasure Q i) := continuous_const.mul hG
  have hbound := integral_mono
    (memLp_one_iff_integrable.mp (continuous_memLp_cube R hvar 1))
    (memLp_one_iff_integrable.mp (continuous_memLp_cube R hRcont 1))
    (fun x => coordinate_slice_bound Q i hv hg hd x)
  have hJ := third_variance_average_le R f hf
  have he (r : Fin 3) := childAverage_slice n Q i r z hv
  simp_rw [he]
  refine hJ.trans ?_
  simpa only [cubeAverage_eq_integral_normalizedCubeMeasure, integral_const_mul] using hbound

end GMCExplicitDelta.Localization.ProjPoincare
