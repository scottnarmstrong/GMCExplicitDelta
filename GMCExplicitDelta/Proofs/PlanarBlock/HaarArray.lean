module

public import GMCExplicitDelta.Proofs.PlanarBlock.ChildPairing
public import GMCExplicitDelta.Proofs.PlanarBlock.CoefficientSymmetry

/-! Array representation of a planar first Haar increment. -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization

namespace GMCExplicitDelta.Localization

def planarBlock_haarArray (Q : TriadicCube 2) (f : Vec 2 → ℝ) (i j : Fin 3) : ℝ :=
  cubeAverage (planarBlock_child Q ![i, j]) (cubeIncrement Q 1 f)

theorem planarBlock_haarArray_mean (Q : TriadicCube 2) {f : Vec 2 → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    (∑ i, ∑ j, planarBlock_haarArray Q f i j) = 0 := by
  have h := cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q 1
    (cubeIncrement Q 1 f)
    (integrableOn_of_integrable_normalizedCubeMeasure Q
      ((Haar.increment_memLp Q 1 f).integrable one_le_two))
  rw [planarBlock_increment_mean Q hf, planarBlock_nine_average] at h
  change 0 = (1 / 9 : ℝ) * (∑ i, ∑ j, planarBlock_haarArray Q f i j) at h
  linarith only [h]

theorem planarBlock_haarArray_energy (Q : TriadicCube 2) (f : Vec 2 → ℝ) :
    Haar.energy Q (cubeIncrement Q 1 f) =
      (1 / 9 : ℝ) * ∑ i, ∑ j, planarBlock_haarArray Q f i j ^ 2 := by
  have hcell : ∀ R ∈ descendantsAtDepth Q 1,
      Haar.energy R (cubeIncrement Q 1 f) = cubeAverage R (cubeIncrement Q 1 f) ^ 2 := by
    intro R hR
    have heq : ∀ x ∈ cubeSet R,
        cubeIncrement Q 1 f x = cubeAverage R (cubeIncrement Q 1 f) := by
      intro x hx
      calc
        _ = cubeProjection Q 1 (cubeIncrement Q 1 f) x :=
          (congrFun (planarBlock_projection_increment Q f) x).symm
        _ = _ := cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth _ hR hx
    calc
      _ = Haar.energy R (fun _ => cubeAverage R (cubeIncrement Q 1 f)) := by
        unfold Haar.energy Haar.pairing
        apply cubeAverage_congr_on_cubeSet
        intro x hx
        rw [heq x hx]
      _ = _ := Haar.energy_const R _
  rw [Haar.energy_eq_descendantsAverage Q 1 (Haar.increment_memLp Q 1 f)]
  have heq : descendantsAverage Q 1 (fun R => Haar.energy R (cubeIncrement Q 1 f)) =
      descendantsAverage Q 1 (fun R => cubeAverage R (cubeIncrement Q 1 f) ^ 2) := by
    unfold descendantsAverage
    exact congrArg (fun t : ℝ => ((descendantsAtDepth Q 1).card : ℝ)⁻¹ * t)
      (Finset.sum_congr rfl hcell)
  rw [heq, planarBlock_nine_average]
  rfl

/-- Every mixed mode is in `L²` on a cube. -/
theorem planarBlock_cubeSin_memLp (Q : TriadicCube 2) (j : Fin 2) (p : Fin 2 → ℤ) :
    MemLp (Haar.cubeSin Q j p) 2 (normalizedCubeMeasure Q) := by
  apply MemLp.of_bound (Haar.Torus.continuous_boxMode _ _ _ _).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs] using
      Haar.Torus.abs_boxMode_le (Haar.cubeCorner Q) (cubeScaleFactor Q) {j} p x

/-- Fourier coefficients of a Haar increment are finite sums of child-mode averages. -/
theorem planarBlock_haarArray_coeff (Q : TriadicCube 2) (f : Vec 2 → ℝ) (j : Fin 2)
    (p : Fin 2 → ℤ) :
    planarBlock_sinCoeff Q j p (cubeIncrement Q 1 f) =
      (1 / 9 : ℝ) * ∑ a : Fin 3, ∑ b : Fin 3,
        planarBlock_haarArray Q f a b * cubeAverage (planarBlock_child Q ![a, b]) (Haar.cubeSin Q j p) := by
  have heq : planarBlock_sinCoeff Q j p (cubeIncrement Q 1 f) =
      Haar.pairing Q (cubeIncrement Q 1 f) (Haar.cubeSin Q j p) := by
    rw [planarBlock_sinCoeff, Haar.pairing, cubeAverage_eq_integral_normalizedCubeMeasure]
    congr 1
    funext x
    ring
  rw [heq, planarBlock_increment_pairing Q f (planarBlock_cubeSin_memLp Q j p), planarBlock_nine_average]
  rfl

end GMCExplicitDelta.Localization
