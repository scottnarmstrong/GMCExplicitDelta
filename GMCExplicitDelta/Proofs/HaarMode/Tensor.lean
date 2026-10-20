module

public import GMCExplicitDelta.Localization.HaarDefs
public import GMCExplicitDelta.Haar.CutoffIntegrals
public import Mathlib.MeasureTheory.Integral.Pi

/-! # Normalized cube integration of coordinate products -/

@[expose] public section

open MeasureTheory Homogenization Set
open scoped ENNReal

namespace GMCExplicitDelta.Localization

variable {d : ℕ}

/-- The normalized cube measure is a product of normalized interval measures. -/
theorem haarMode_normalizedCubeMeasure_pi (Q : Homogenization.TriadicCube d) :
    Measure.pi (fun i : Fin d => ENNReal.ofReal (cubeScaleFactor Q)⁻¹ •
      volume.restrict (Ico (((Q.index i : ℝ) - 1 / 2) * cubeScaleFactor Q)
        (((Q.index i : ℝ) + 1 / 2) * cubeScaleFactor Q))) = normalizedCubeMeasure Q := by
  have hℓ : 0 < cubeScaleFactor Q := by unfold cubeScaleFactor; positivity
  let (i : Fin d) : IsFiniteMeasure (ENNReal.ofReal (cubeScaleFactor Q)⁻¹ •
      volume.restrict (Ico (((Q.index i : ℝ) - 1 / 2) * cubeScaleFactor Q)
        (((Q.index i : ℝ) + 1 / 2) * cubeScaleFactor Q))) :=
    (volume.restrict _).smul_finite ENNReal.ofReal_ne_top
  refine Measure.pi_eq fun s hs => ?_
  rw [normalizedCubeMeasure, cubeMeasure, Measure.smul_apply,
    Measure.restrict_apply (MeasurableSet.univ_pi hs), cubeSet_eq_pi_Ico,
    ← Set.pi_inter_distrib, volume_pi_pi, smul_eq_mul]
  simp only [Measure.smul_apply, Measure.restrict_apply (hs _), smul_eq_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    cubeVolume, ← inv_pow, ENNReal.ofReal_pow (inv_nonneg.2 hℓ.le)]

/-- Fubini on a normalized cube; no integrability premise is needed for the product identity. -/
theorem haarMode_cubeAverage_prod (Q : Homogenization.TriadicCube d) (f : Fin d → ℝ → ℝ) :
    cubeAverage Q (fun x => ∏ i, f i (x i)) =
      ∏ i, (cubeScaleFactor Q)⁻¹ *
        ∫ t in (((Q.index i : ℝ) - 1 / 2) * cubeScaleFactor Q)..
          (((Q.index i : ℝ) + 1 / 2) * cubeScaleFactor Q), f i t := by
  have hℓ : 0 < cubeScaleFactor Q := by unfold cubeScaleFactor; positivity
  let (i : Fin d) : IsFiniteMeasure (ENNReal.ofReal (cubeScaleFactor Q)⁻¹ •
      volume.restrict (Ico (((Q.index i : ℝ) - 1 / 2) * cubeScaleFactor Q)
        (((Q.index i : ℝ) + 1 / 2) * cubeScaleFactor Q))) :=
    (volume.restrict _).smul_finite ENNReal.ofReal_ne_top
  rw [cubeAverage_eq_integral_normalizedCubeMeasure, ← haarMode_normalizedCubeMeasure_pi,
    integral_fintype_prod_eq_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.2 hℓ.le), smul_eq_mul,
    integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le]
  exact mul_le_mul_of_nonneg_right (by linarith) hℓ.le

/-- Tensor products commute with dilation to the unit centered cube. -/
theorem haarMode_cubeAverage_scaled_prod (n : ℕ) (f : Fin d → ℝ → ℝ) :
    cubeAverage (originCube d (n : ℤ)) (fun x => ∏ i, f i (x i / (3 : ℝ) ^ n)) =
      ∏ i, ∫ t in -(1 / 2 : ℝ)..1 / 2, f i t := by
  rw [haarMode_cubeAverage_prod _ (fun i t => f i (t / (3 : ℝ) ^ n))]
  apply Finset.prod_congr rfl
  intro i _
  simp only [originCube, cubeScaleFactor, zpow_natCast, Pi.zero_apply, Int.cast_zero,
    zero_sub, zero_add]
  rw [intervalIntegral.integral_comp_div (f := f i) (by positivity : (3 : ℝ) ^ n ≠ 0)]
  simp only [smul_eq_mul]
  have hl : (3 : ℝ) ^ n ≠ 0 := by positivity
  rw [mul_div_cancel_right₀ _ hl, mul_div_cancel_right₀ _ hl]
  field_simp

/-- Insert one coordinate factor into a tensor product. -/
theorem haarMode_prod_insert (f : Fin d → ℝ → ℝ) (g : ℝ → ℝ) (i : Fin d) (x : Homogenization.Vec d) :
    (∏ j, (if j = i then fun t => g t * f j t else f j) (x j)) =
      g (x i) * ∏ j, f j (x j) := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ (fun j => (if j = i then fun t => g t * f j t else f j) (x j))
    (Finset.mem_univ i), ← Finset.mul_prod_erase Finset.univ (fun j => f j (x j)) (Finset.mem_univ i)]
  simp only [ite_true]
  rw [mul_assoc]
  congr 2
  apply Finset.prod_congr rfl
  intro j hj
  rw [ite_eq_right (Finset.ne_of_mem_erase hj)]

/-- A coordinate moment of a tensor product factors into one-dimensional moments. -/
theorem haarMode_cubeAverage_scaled_moment (n : ℕ) (f : Fin d → ℝ → ℝ) (g : ℝ → ℝ) (i : Fin d) :
    cubeAverage (originCube d (n : ℤ))
      (fun x => g (x i / (3 : ℝ) ^ n) * ∏ j, f j (x j / (3 : ℝ) ^ n)) =
      (∫ t in -(1 / 2 : ℝ)..1 / 2, g t * f i t) *
        ∏ j ∈ Finset.univ.erase i, ∫ t in -(1 / 2 : ℝ)..1 / 2, f j t := by
  classical
  have heq : (fun x : Homogenization.Vec d => g (x i / (3 : ℝ) ^ n) * ∏ j, f j (x j / (3 : ℝ) ^ n)) =
      fun x => ∏ j, (if j = i then fun t => g t * f j t else f j) (x j / (3 : ℝ) ^ n) := by
    funext x
    exact (haarMode_prod_insert f g i (fun j => x j / (3 : ℝ) ^ n)).symm
  rw [heq, haarMode_cubeAverage_scaled_prod, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [ite_true]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [ite_eq_right (Finset.ne_of_mem_erase hj)]

end GMCExplicitDelta.Localization
