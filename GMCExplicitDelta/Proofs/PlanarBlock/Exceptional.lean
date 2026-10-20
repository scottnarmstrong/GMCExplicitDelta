module

public import GMCExplicitDelta.Proofs.PlanarBlock.PlanarSpectrum
public import GMCExplicitDelta.Proofs.PlanarBlock.CoefficientSymmetry

/-! Reduction of the finite exceptional square to three coefficients per component. -/

@[expose] public section

noncomputable section

open Homogenization

namespace GMCExplicitDelta.Localization

theorem planarBlock_lowModes_sum (f : (Fin 2 → ℤ) → ℝ) :
    (∑ p ∈ planarBlock_lowModes, f p) =
      ∑ n ∈ ({-2, -1, 0, 1, 2} : Finset ℤ),
        ∑ m ∈ ({-2, -1, 0, 1, 2} : Finset ℤ), f ![n, m] := by
  classical
  unfold planarBlock_lowModes
  rw [Finset.sum_image, Finset.sum_product]
  intro x _ y _ h
  apply Prod.ext
  · exact congrFun h 0
  · exact congrFun h 1

/-- Component zero has two axis coefficients and one mixed coefficient. -/
theorem planarBlock_exceptional_zero (Q : TriadicCube 2) (r : ℝ) (f : Vec 2 → ℝ) :
    (∑ p ∈ planarBlock_lowModes, planarBlock_lowWeight r p * planarBlock_sinCoeff Q 0 p f ^ 2) =
      8 / (5 * r) * planarBlock_sinCoeff Q 0 ![1, 0] f ^ 2 +
      1 / (10 * r) * planarBlock_sinCoeff Q 0 ![2, 0] f ^ 2 +
      6 / (5 * r) * planarBlock_sinCoeff Q 0 ![1, 1] f ^ 2 := by
  have hz1 : planarBlock_sinCoeff Q 0 ![0, 1] f = 0 := planarBlock_sinCoeff_zero Q 0 _ f rfl
  have hz2 : planarBlock_sinCoeff Q 0 ![0, 2] f = 0 := planarBlock_sinCoeff_zero Q 0 _ f rfl
  rw [planarBlock_lowModes_sum]
  norm_num [planarBlock_lowWeight, planarBlock_modeSize, planarBlock_sinCoeff_neg_first,
    planarBlock_sinCoeff_neg_second, planarBlock_sinCoeff_zero, hz1, hz2, Finset.sum_insert,
    Finset.sum_singleton]
  ring

/-- Component one has the transposed set of three coefficients. -/
theorem planarBlock_exceptional_one (Q : TriadicCube 2) (r : ℝ) (f : Vec 2 → ℝ) :
    (∑ p ∈ planarBlock_lowModes, planarBlock_lowWeight r p * planarBlock_sinCoeff Q 1 p f ^ 2) =
      8 / (5 * r) * planarBlock_sinCoeff Q 1 ![0, 1] f ^ 2 +
      1 / (10 * r) * planarBlock_sinCoeff Q 1 ![0, 2] f ^ 2 +
      6 / (5 * r) * planarBlock_sinCoeff Q 1 ![1, 1] f ^ 2 := by
  rw [planarBlock_lowModes_sum]
  norm_num [planarBlock_lowWeight, planarBlock_modeSize, planarBlock_sinCoeff_neg_first,
    planarBlock_sinCoeff_neg_second, planarBlock_sinCoeff_zero, Finset.sum_insert,
    Finset.sum_singleton]
  ring

end GMCExplicitDelta.Localization
