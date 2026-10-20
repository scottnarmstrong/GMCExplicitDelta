module

public import GMCExplicitDelta.Haar.MultiplierIdentification
public import GMCExplicitDelta.Localization.HaarDefs

/-! The Sobolev multiplier bound H7 on the actual triadic cube. -/
@[expose] public section

open Homogenization MeasureTheory
open scoped Topology ENNReal BigOperators

namespace GMCExplicitDelta.Localization.Multiplier

open Haar
variable {d : ℕ}

theorem originCube_coord_bound (n : ℕ) {x : Vec d} (hx : x ∈ cubeSet (originCube d (n : ℤ)))
    (j : Fin d) : |x j / (3 : ℝ) ^ n| ≤ 1 / 2 := by
  have h := (mem_cubeSet_originCube_iff.mp hx) j
  rw [zpow_natCast] at h
  have hS : 0 < (3 : ℝ) ^ n := by positivity
  apply abs_le.mpr
  constructor
  · apply (le_div_iff₀ hS).mpr
    linarith only [h.1]
  · exact (div_le_iff₀ hS).mpr h.2.le

theorem normalizedCubeMeasure_ae_mem (Q : TriadicCube d) :
    ∀ᵐ x ∂(normalizedCubeMeasure Q), x ∈ cubeSet Q := by
  unfold normalizedCubeMeasure cubeMeasure
  exact Measure.ae_smul_measure (ae_restrict_mem (measurableSet_cubeSet Q)) _

theorem vecEnergy_eq_integral (Q : TriadicCube d) (G : Vec d → Vec d)
    (hG : ∀ j, MemLp (fun x => G x j) 2 (normalizedCubeMeasure Q)) :
    vecEnergy Q G = ∫ x, ∑ j, G x j ^ 2 ∂(normalizedCubeMeasure Q) := by
  unfold vecEnergy Haar.energy Haar.pairing
  simp only [cubeAverage_eq_integral_normalizedCubeMeasure, ← pow_two]
  rw [integral_finsetSum Finset.univ (fun j _ => (hG j).integrable_sq)]

theorem cutoffComponent_value (ω S : ℝ) (i : Fin d) (x : Vec d) :
    tensorMultiplier (cutoffComponentFactors ω S i) x =
      cutoffGradient ω (fun k => x k / S) i / S := by
  classical
  have hF (j : Fin d) : cutoffComponentFactors ω S i j (x j) =
      if j = i then 1 * (cutoffSlope ω (x j / S) / S) else cutoffProfile ω (x j / S) := by
    simp only [cutoffComponentFactors, multiplierFactor, decide_eq_true_eq, one_mul]
  rw [tensorMultiplier_component _ _ _ x i 1 hF]
  unfold productGradient cutoffGradient
  ring

/-- H7 for an arbitrary Sobolev function, before centering. -/
theorem exists_cutoffGradientH1 (row : Contract.Row d) (hω0 : 0 < row.omegaEff)
    (hω1 : row.omegaEff ≤ 1 / 2) (n : ℕ)
    (u : H1Function (openCubeSet (originCube d (n : ℤ)))) :
    ∃ H : Fin d → H1Function (openCubeSet (originCube d (n : ℤ))),
      (∀ i, (H i).toFun = fun x => u.toFun x * cubeCutoffGrad row n x i) ∧
      (∑ i, vecEnergy (originCube d (n : ℤ)) (H i).grad) ≤
        row.kappaOmega ^ 2 / ((3 : ℝ) ^ n) ^ 2 * vecEnergy (originCube d (n : ℤ)) u.grad +
          (d : ℝ) * row.kappaOmega ^ 4 / ((3 : ℝ) ^ n) ^ 4 * Haar.energy (originCube d (n : ℤ)) u.toFun := by
  classical
  let Q := originCube d (n : ℤ)
  let S := (3 : ℝ) ^ n
  let μ := normalizedCubeMeasure Q
  have hS : S ≠ 0 := by dsimp only [S]; positivity
  have hU : ∀ᵐ x ∂(volume.restrict (openCubeSet Q)), ∀ j, |x j / S| ≤ 1 := by
    filter_upwards [ae_restrict_mem (isOpen_openCubeSet Q).measurableSet] with x hx
    intro j
    exact (originCube_coord_bound n (openCubeSet_subset_cubeSet Q hx) j).trans (by norm_num)
  choose H hH hDH using fun i => exists_mul_cutoffComponent u hω1 S hU i
  refine ⟨H, ?_, ?_⟩
  · intro i
    rw [hH i]
    funext x
    rw [cutoffComponent_value]
    exact mul_comm _ _
  · have hi (i j : Fin d) : Integrable (fun x => (H i).grad x j ^ 2) μ :=
      ((H i).grad_memL2_normalizedCubeMeasure j).integrable_sq
    have hu (j : Fin d) : Integrable (fun x => u.grad x j ^ 2) μ :=
      (u.grad_memL2_normalizedCubeMeasure j).integrable_sq
    have he : (∑ i, vecEnergy Q (H i).grad) = ∫ x, ∑ i, ∑ j, (H i).grad x j ^ 2 ∂μ := by
      simp_rw [vecEnergy_eq_integral Q _ (fun j => (H _).grad_memL2_normalizedCubeMeasure j)]
      rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
    have hR : Integrable (fun x => row.kappaOmega ^ 2 / S ^ 2 * (∑ j, u.grad x j ^ 2) +
        (d : ℝ) * row.kappaOmega ^ 4 / S ^ 4 * u.toFun x ^ 2) μ :=
      ((integrable_finsetSum _ (fun j _ => hu j)).const_mul _).add
        (u.memL2_normalizedCubeMeasure.integrable_sq.const_mul _)
    rw [he]
    calc
      _ ≤ ∫ x, row.kappaOmega ^ 2 / S ^ 2 * (∑ j, u.grad x j ^ 2) +
          (d : ℝ) * row.kappaOmega ^ 4 / S ^ 4 * u.toFun x ^ 2 ∂μ := by
        apply integral_mono_ae (integrable_finsetSum _ (fun i _ =>
          integrable_finsetSum _ (fun j _ => hi i j))) hR
        filter_upwards [normalizedCubeMeasure_ae_mem Q] with x hx
        simp_rw [hDH]
        exact cutoffComponent_gradient_sq_le hω0 hω1 hS x
          (fun j => originCube_coord_bound n hx j) (u.toFun x) (u.grad x)
      _ = _ := by
        rw [integral_add ((integrable_finsetSum _ (fun j _ => hu j)).const_mul _)
          (u.memL2_normalizedCubeMeasure.integrable_sq.const_mul _), integral_const_mul, integral_const_mul,
          ← vecEnergy_eq_integral Q u.grad (fun j => u.grad_memL2_normalizedCubeMeasure j)]
        simp only [Haar.energy, Haar.pairing, cubeAverage_eq_integral_normalizedCubeMeasure, pow_two]
        rfl

end GMCExplicitDelta.Localization.Multiplier
