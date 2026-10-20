module

public import GMCExplicitDelta.Proofs.PlanarBlock.ChildModes

/-! Child-average formulas for the first Haar increment. -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization

namespace GMCExplicitDelta.Localization

variable {d : ℕ}

theorem planarBlock_projection_sub (Q : TriadicCube d) (k : ℕ) {f g : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    cubeProjection Q k (fun x => f x - g x) =
      fun x => cubeProjection Q k f x - cubeProjection Q k g x := by
  have heq : (fun x => f x - g x) = fun x => f x + (-1) * g x := by
    funext x
    ring
  rw [heq, Haar.projection_add Q k hf (hg.const_mul (-1)), Haar.projection_smul]
  funext x
  ring

/-- The first increment is fixed by the child projection. -/
theorem planarBlock_projection_increment (Q : TriadicCube d) (f : Vec d → ℝ) :
    cubeProjection Q 1 (cubeIncrement Q 1 f) = cubeIncrement Q 1 f := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, cubeIncrement_succ,
    planarBlock_projection_sub Q 1 (Haar.projection_memLp Q 1 f 2) (Haar.projection_memLp Q 0 f 2),
    Haar.projection_idempotent, Haar.projection_projection_of_ge Q (by omega)]

/-- The first increment has mean zero. -/
theorem planarBlock_increment_mean (Q : TriadicCube d) {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    cubeAverage Q (cubeIncrement Q 1 f) = 0 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, cubeIncrement_succ,
    cubeAverage_eq_integral_normalizedCubeMeasure]
  rw [integral_sub ((Haar.projection_memLp Q 1 f 2).integrable one_le_two)
    ((Haar.projection_memLp Q 0 f 2).integrable one_le_two),
    ← cubeAverage_eq_integral_normalizedCubeMeasure,
    ← cubeAverage_eq_integral_normalizedCubeMeasure,
    cubeAverage_cubeProjection_eq_cubeAverage_of_memLp Q 1 f hf,
    cubeAverage_cubeProjection_eq_cubeAverage_of_memLp Q 0 f hf, sub_self]

/-- Pairing a first increment against a mode uses only the mode's child averages. -/
theorem planarBlock_increment_pairing (Q : TriadicCube d) (f : Vec d → ℝ) {m : Vec d → ℝ}
    (hm : MemLp m 2 (normalizedCubeMeasure Q)) :
    Haar.pairing Q (cubeIncrement Q 1 f) m =
      descendantsAverage Q 1 (fun R => cubeAverage R (cubeIncrement Q 1 f) * cubeAverage R m) := by
  calc
    _ = Haar.pairing Q (cubeProjection Q 1 (cubeIncrement Q 1 f)) m :=
      congrArg (fun g => Haar.pairing Q g m) (planarBlock_projection_increment Q f).symm
    _ = Haar.pairing Q (cubeIncrement Q 1 f) (cubeProjection Q 1 m) :=
      Haar.projection_selfAdjoint Q 1 (Haar.increment_memLp Q 1 f) hm
    _ = _ := Haar.pairing_projection_right Q 1 m (Haar.increment_memLp Q 1 f)

/-- The children are parametrized injectively by their ternary digits. -/
theorem planarBlock_child_injective (Q : TriadicCube d) : Function.Injective (planarBlock_child Q) := by
  intro b c h
  funext i
  apply Fin.ext
  have hi := congrArg (fun R : TriadicCube d => R.index i) h
  change 3 * Q.index i + (b i : ℤ) - 1 = 3 * Q.index i + (c i : ℤ) - 1 at hi
  have hcast : (b i : ℤ) = (c i : ℤ) := by omega
  exact_mod_cast hcast

/-- Descendant averaging at depth one is averaging over the ternary digits. -/
theorem planarBlock_children_average (Q : TriadicCube d) (A : TriadicCube d → ℝ) :
    descendantsAverage Q 1 A = (3 ^ d : ℝ)⁻¹ * ∑ b : Fin d → Fin 3, A (planarBlock_child Q b) := by
  classical
  unfold descendantsAverage
  simp only [descendantsAtDepth, Finset.singleton_biUnion]
  rw [childCubes_card]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  unfold childCubes
  rw [Finset.sum_image]
  · rfl
  · intro b _ c _ h
    exact planarBlock_child_injective Q h

/-- In the plane the digit average is a three-by-three array average. -/
theorem planarBlock_nine_average (Q : TriadicCube 2) (A : TriadicCube 2 → ℝ) :
    descendantsAverage Q 1 A = (1 / 9 : ℝ) *
      ∑ i : Fin 3, ∑ j : Fin 3, A (planarBlock_child Q ![i, j]) := by
  rw [planarBlock_children_average]
  norm_num only [pow_two, mul_inv_rev, one_div]
  congr 1
  rw [← (finTwoArrowEquiv (Fin 3)).symm.sum_comp (fun b => A (planarBlock_child Q b)),
    Fintype.sum_prod_type]
  rfl

end GMCExplicitDelta.Localization
