module

public import GMCExplicitDelta.Haar.NeumannSpectral

/-! Sign symmetries of the planar mixed Fourier coefficients. -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization

namespace GMCExplicitDelta.Localization

def planarBlock_sinCoeff (Q : TriadicCube 2) (j : Fin 2) (p : Fin 2 → ℤ) (f : Vec 2 → ℝ) : ℝ :=
  ∫ x, Haar.cubeSin Q j p x * f x ∂normalizedCubeMeasure Q

theorem planarBlock_cubeSin_zero (Q : TriadicCube 2) (j : Fin 2) (p : Fin 2 → ℤ)
    (hp : p j = 0) : Haar.cubeSin Q j p = fun _ => 0 := by
  funext x
  fin_cases j <;>
    simp_all [Haar.cubeSin, Haar.Torus.boxMode, Fin.prod_univ_two]

theorem planarBlock_sinCoeff_zero (Q : TriadicCube 2) (j : Fin 2) (p : Fin 2 → ℤ)
    (f : Vec 2 → ℝ) (hp : p j = 0) : planarBlock_sinCoeff Q j p f = 0 := by
  simp only [planarBlock_sinCoeff, planarBlock_cubeSin_zero Q j p hp, zero_mul, integral_zero]

theorem planarBlock_sinCoeff_neg_first (Q : TriadicCube 2) (j : Fin 2) (n m : ℤ)
    (f : Vec 2 → ℝ) :
    planarBlock_sinCoeff Q j ![-n, m] f =
      (if j = 0 then -planarBlock_sinCoeff Q j ![n, m] f else planarBlock_sinCoeff Q j ![n, m] f) := by
  have hfun : Haar.cubeSin Q j ![-n, m] =
      fun x => if j = 0 then -Haar.cubeSin Q j ![n, m] x else Haar.cubeSin Q j ![n, m] x := by
    funext x
    fin_cases j <;>
      simp [Haar.cubeSin, Haar.Torus.boxMode, Fin.prod_univ_two,
        mul_neg, neg_mul, neg_div, Real.sin_neg, Real.cos_neg]
  rw [planarBlock_sinCoeff, hfun]
  split_ifs with hj
  · simp only [neg_mul, integral_neg]
    rfl
  · rfl

theorem planarBlock_sinCoeff_neg_second (Q : TriadicCube 2) (j : Fin 2) (n m : ℤ)
    (f : Vec 2 → ℝ) :
    planarBlock_sinCoeff Q j ![n, -m] f =
      (if j = 1 then -planarBlock_sinCoeff Q j ![n, m] f else planarBlock_sinCoeff Q j ![n, m] f) := by
  have hfun : Haar.cubeSin Q j ![n, -m] =
      fun x => if j = 1 then -Haar.cubeSin Q j ![n, m] x else Haar.cubeSin Q j ![n, m] x := by
    funext x
    fin_cases j <;>
      simp [Haar.cubeSin, Haar.Torus.boxMode, Fin.prod_univ_two,
        mul_neg, neg_mul, neg_div, Real.sin_neg, Real.cos_neg]
  rw [planarBlock_sinCoeff, hfun]
  split_ifs with hj
  · simp only [neg_mul, integral_neg]
    rfl
  · rfl

end GMCExplicitDelta.Localization
