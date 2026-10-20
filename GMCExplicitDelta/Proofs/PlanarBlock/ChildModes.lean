module

public import GMCExplicitDelta.Proofs.PlanarBlock.CellIntegrals
public import GMCExplicitDelta.Haar.NeumannSpectral

/-! Rescaling the exact mode averages to the children of an arbitrary triadic cube. -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization

namespace GMCExplicitDelta.Localization

/-- A digit-indexed child cube. -/
def planarBlock_child {d : ℕ} (Q : TriadicCube d) (b : Fin d → Fin 3) : TriadicCube d :=
  { scale := Q.scale - 1, index := fun i => 3 * Q.index i + (b i : ℤ) - 1 }

theorem planarBlock_child_scale {d : ℕ} (Q : TriadicCube d) (b : Fin d → Fin 3) :
    cubeScaleFactor (planarBlock_child Q b) = cubeScaleFactor Q / 3 :=
  cubeScaleFactor_childCube Q b

theorem planarBlock_child_corner {d : ℕ} (Q : TriadicCube d) (b : Fin d → Fin 3) (i : Fin d) :
    Haar.cubeCorner (planarBlock_child Q b) i =
      Haar.cubeCorner Q i + cubeScaleFactor Q * (b i : ℝ) / 3 := by
  simp only [Haar.cubeCorner, planarBlock_child, cubeScaleFactor_childCube,
    Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
  ring

/-- Affine rescaling of a normalized third-interval integral. -/
theorem planarBlock_third_affine (f : ℝ → ℝ) (a ℓ : ℝ) (hℓ : 0 < ℓ) (i : Fin 3) :
    (ℓ / 3)⁻¹ * (∫ t in a + ℓ * (i : ℝ) / 3..a + ℓ * ((i : ℝ) + 1) / 3,
      f ((t - a) / ℓ)) =
      3 * (∫ t in (i : ℝ) / 3..((i : ℝ) + 1) / 3, f t) := by
  have heq : (fun t => f ((t - a) / ℓ)) = fun t => f (t / ℓ + (-a / ℓ)) := by
    funext t
    congr 1
    ring
  rw [heq, intervalIntegral.integral_comp_div_add _ hℓ.ne' (-a / ℓ)]
  have hlo : (a + ℓ * (i : ℝ) / 3) / ℓ + -a / ℓ = (i : ℝ) / 3 := by
    field_simp [hℓ.ne']
    ring
  have hhi : (a + ℓ * ((i : ℝ) + 1) / 3) / ℓ + -a / ℓ = ((i : ℝ) + 1) / 3 := by
    field_simp [hℓ.ne']
    ring
  rw [hlo, hhi, smul_eq_mul]
  have hfactor : (ℓ / 3)⁻¹ * ℓ = 3 := by field_simp [hℓ.ne']
  rw [← mul_assoc, hfactor]

/-- The same rescaling for the normalized half-open interval measure. -/
theorem planarBlock_third_measure (f : ℝ → ℝ) (a ℓ : ℝ) (hℓ : 0 < ℓ) (i : Fin 3) :
    (∫ t, f ((t - a) / ℓ) ∂(ENNReal.ofReal (ℓ / 3)⁻¹ •
      volume.restrict (Set.Ico (a + ℓ * (i : ℝ) / 3)
        (a + ℓ * ((i : ℝ) + 1) / 3)))) =
      3 * (∫ t in (i : ℝ) / 3..((i : ℝ) + 1) / 3, f t) := by
  rw [integral_smul_measure, ENNReal.toReal_ofReal (by positivity), smul_eq_mul,
    integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le]
  · exact planarBlock_third_affine f a ℓ hℓ i
  · nlinarith only [hℓ]

/-- Each coordinate mode average on a child is its corresponding third-interval average. -/
theorem planarBlock_child_modeFactor {d : ℕ} (Q : TriadicCube d) (b : Fin d → Fin 3)
    (O : Finset (Fin d)) (p : Fin d → ℤ) (j : Fin d) :
    (∫ t, Haar.Torus.modeFactor (Haar.cubeCorner Q) (cubeScaleFactor Q) O p j t
      ∂(ENNReal.ofReal (cubeScaleFactor (planarBlock_child Q b))⁻¹ •
        volume.restrict (Set.Ico (Haar.cubeCorner (planarBlock_child Q b) j)
          (Haar.cubeCorner (planarBlock_child Q b) j + cubeScaleFactor (planarBlock_child Q b))))) =
      3 * (∫ t in (b j : ℝ) / 3..((b j : ℝ) + 1) / 3,
        if j ∈ O then Real.sin (Real.pi * p j * t) else Real.cos (Real.pi * p j * t)) := by
  classical
  have hfun : Haar.Torus.modeFactor (Haar.cubeCorner Q) (cubeScaleFactor Q) O p j =
      fun t => (if j ∈ O then
        Real.sin (Real.pi * p j * ((t - Haar.cubeCorner Q j) / cubeScaleFactor Q))
        else Real.cos (Real.pi * p j * ((t - Haar.cubeCorner Q j) / cubeScaleFactor Q))) := by
    funext t
    unfold Haar.Torus.modeFactor
    split_ifs <;> congr 1 <;> ring
  rw [hfun, planarBlock_child_scale, planarBlock_child_corner]
  rw [show Haar.cubeCorner Q j + cubeScaleFactor Q * (b j : ℝ) / 3 + cubeScaleFactor Q / 3 =
    Haar.cubeCorner Q j + cubeScaleFactor Q * ((b j : ℝ) + 1) / 3 by ring]
  exact planarBlock_third_measure
    (fun t => if j ∈ O then Real.sin (Real.pi * p j * t) else Real.cos (Real.pi * p j * t))
    (Haar.cubeCorner Q j) (cubeScaleFactor Q) (Haar.cubeScaleFactor_pos' Q) (b j)

/-- Tensor-product formula for a mode average on a child cube. -/
theorem planarBlock_child_modeAverage {d : ℕ} (Q : TriadicCube d) (b : Fin d → Fin 3)
    (O : Finset (Fin d)) (p : Fin d → ℤ) :
    cubeAverage (planarBlock_child Q b) (Haar.Torus.boxMode (Haar.cubeCorner Q) (cubeScaleFactor Q) O p) =
      ∏ j, (3 * (∫ t in (b j : ℝ) / 3..((b j : ℝ) + 1) / 3,
        if j ∈ O then Real.sin (Real.pi * p j * t) else Real.cos (Real.pi * p j * t))) := by
  classical
  rw [cubeAverage_eq_integral_normalizedCubeMeasure,
    ← Haar.boxMeasure_eq_normalizedCubeMeasure]
  simp_rw [Haar.Torus.boxMode_eq_prod_modeFactor]
  rw [Haar.Torus.boxMeasure, integral_fintype_prod_eq_prod]
  exact Finset.prod_congr rfl fun j _ => planarBlock_child_modeFactor Q b O p j

end GMCExplicitDelta.Localization
