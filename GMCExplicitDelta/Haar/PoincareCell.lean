module

public import GMCExplicitDelta.Haar.PoincareCoeff
public import GMCExplicitDelta.Haar.TriadicProjection
public import Homogenization.Sobolev.H1.Definitions
public import Homogenization.Besov.Localization
public import Homogenization.Besov.Duality.ProjectionLimit
public import Homogenization.Besov.Duality.ProjectedPairing.Integrability
public import Homogenization.Geometry.CubeMeasure

/-!
# Sharp cell Poincaré inequality (H8)

On a triadic cube `R` of side `ℓ`, for `u` with weak gradient `G` (all in `L²`):
`‖u - ⨍_R u‖² ≤ (ℓ/π)² ‖G‖²` (normalized norms). The proof expands `u` in the Neumann cosine
basis (`Torus.hasSum_sq_boxCoeff_cos`), identifies the mixed sine coefficients of `∂ᵢu` with
`-(π nᵢ/ℓ)` times the cosine coefficients (`Torus.integral_weakDeriv_mul_boxMode`), and uses the
mixed Bessel inequality (`Torus.tsum_sq_boxCoeff_le`) together with `|n|² ≥ 1` for `n ≠ 0`.
Summing over the depth-`j` cells gives `‖u - E_j u‖² ≤ 9^{-j}(ℓ/π)²‖G‖²`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open Homogenization

namespace GMCExplicitDelta.Haar

variable {d : ℕ}

/-- The lower corner of a triadic cube. -/
def cubeCorner (R : TriadicCube d) : Fin d → ℝ :=
  fun i => ((R.index i : ℝ) - 1 / 2) * cubeScaleFactor R

theorem cubeScaleFactor_pos' (R : TriadicCube d) : 0 < cubeScaleFactor R := by
  simpa [cubeScaleFactor] using (zpow_pos (show (0 : ℝ) < 3 by norm_num) R.scale)

theorem cubeSet_eq_box (R : TriadicCube d) :
    cubeSet R = Set.pi univ fun i =>
      Ico (cubeCorner R i) (cubeCorner R i + cubeScaleFactor R) := by
  rw [cubeSet_eq_pi_Ico]
  congr 1
  funext i
  unfold cubeCorner
  congr 1
  ring

theorem openCubeSet_eq_box (R : TriadicCube d) :
    openCubeSet R = Set.pi univ fun i =>
      Ioo (cubeCorner R i) (cubeCorner R i + cubeScaleFactor R) := by
  rw [openCubeSet_eq_pi_Ioo]
  congr 1
  funext i
  unfold cubeCorner
  congr 1
  ring

theorem boxMeasure_eq_normalizedCubeMeasure (R : TriadicCube d) :
    Torus.boxMeasure (cubeCorner R) (cubeScaleFactor R) = normalizedCubeMeasure R := by
  have hℓ := cubeScaleFactor_pos' R
  refine Measure.pi_eq fun s hs => ?_
  rw [normalizedCubeMeasure, cubeMeasure, Measure.smul_apply,
    Measure.restrict_apply (MeasurableSet.univ_pi hs), cubeSet_eq_box, ← Set.pi_inter_distrib,
    volume_pi_pi, smul_eq_mul]
  simp only [Measure.smul_apply, Measure.restrict_apply (hs _), smul_eq_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    cubeVolume, ← inv_pow, ENNReal.ofReal_pow (inv_nonneg.2 hℓ.le)]

theorem memLp_normalized_of_memL2On {R : TriadicCube d} {f : Vec d → ℝ}
    (hf : MemL2On (openCubeSet R) f) : MemLp f 2 (normalizedCubeMeasure R) := by
  unfold MemL2On at hf
  rw [← volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] at hf
  exact hf.smul_measure ENNReal.ofReal_ne_top

theorem integrableOn_open_of_memLp {R : TriadicCube d} {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure R)) : IntegrableOn f (openCubeSet R) volume :=
  (integrableOn_of_integrable_normalizedCubeMeasure R (hf.integrable one_le_two)).mono_set
    (openCubeSet_subset_cubeSet R)

theorem integral_normalized_eq_open (R : TriadicCube d) (f : Vec d → ℝ) :
    ∫ x, f x ∂normalizedCubeMeasure R = (cubeVolume R)⁻¹ * ∫ x in openCubeSet R, f x := by
  rw [← cubeAverage_eq_integral_normalizedCubeMeasure, cubeAverage,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]

theorem energy_eq_integral_sq (R : TriadicCube d) (f : Vec d → ℝ) :
    energy R f = ∫ x, f x ^ 2 ∂normalizedCubeMeasure R := by
  unfold energy pairing
  rw [cubeAverage_eq_integral_normalizedCubeMeasure]
  simp only [pow_two]

/-! ### One cube -/

/-- **Sharp Poincaré inequality on one cube.** -/
theorem cube_poincare (R : TriadicCube d) {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : MemLp u 2 (normalizedCubeMeasure R))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure R))
    (hw : HasWeakGradientOn (openCubeSet R) u G) :
    energy R (fun x => u x - cubeAverage R u) ≤
      (cubeScaleFactor R / Real.pi) ^ 2 * ∑ i, energy R (fun x => G x i) := by
  classical
  set a := cubeCorner R
  set ℓ := cubeScaleFactor R
  have hℓ : 0 < ℓ := cubeScaleFactor_pos' R
  have hμ : Torus.boxMeasure a ℓ = normalizedCubeMeasure R := boxMeasure_eq_normalizedCubeMeasure R
  set c : (Fin d → ℤ) → ℝ := fun n => ∫ x, Torus.boxMode a ℓ ∅ n x * u x ∂normalizedCubeMeasure R
  set s : Fin d → (Fin d → ℤ) → ℝ := fun i n => ∫ x, Torus.boxMode a ℓ {i} n x * G x i ∂normalizedCubeMeasure R
  have huB : MemLp u 2 (Torus.boxMeasure a ℓ) := by rw [hμ]; exact hu
  have hGB : ∀ i, MemLp (fun x => G x i) 2 (Torus.boxMeasure a ℓ) := fun i => by
    rw [hμ]; exact hG i
  -- Parseval for `u`
  have hP : HasSum (fun n => c n ^ 2) (∫ x, u x ^ 2 ∂normalizedCubeMeasure R) := by
    have := Torus.hasSum_sq_boxCoeff_cos a hℓ huB
    rw [hμ] at this
    exact this
  -- Bessel for the mixed coefficients of `Gᵢ`
  have hS : ∀ i, Summable (fun n => s i n ^ 2) := fun i => by
    have := Torus.summable_sq_boxCoeff a hℓ {i} (hGB i)
    rw [hμ] at this
    exact this
  have hSle : ∀ i, ∑' n, s i n ^ 2 ≤ ∫ x, G x i ^ 2 ∂normalizedCubeMeasure R := fun i => by
    have := Torus.tsum_sq_boxCoeff_le a hℓ {i} (hGB i)
    rw [hμ] at this
    exact this
  -- the coefficient identity
  have hU : openCubeSet R = Set.pi univ fun j => Ioo (a j) (a j + ℓ) := openCubeSet_eq_box R
  have hcoef : ∀ i n, s i n = -(Real.pi * n i / ℓ) * c n := by
    intro i n
    have h := Torus.integral_weakDeriv_mul_boxMode a hℓ i n (g := u) (gi := fun x => G x i)
      (by rw [← hU]; exact hw i) (by rw [← hU]; exact integrableOn_open_of_memLp hu)
      (by rw [← hU]; exact integrableOn_open_of_memLp (hG i))
    have e1 : ∫ x in Set.pi univ (fun j => Ioo (a j) (a j + ℓ)), Torus.boxMode a ℓ {i} n x * G x i =
        ∫ x in Set.pi univ (fun j => Ioo (a j) (a j + ℓ)), G x i * Torus.boxMode a ℓ {i} n x := by
      congr 1
      funext x
      ring
    have e2 : ∫ x in Set.pi univ (fun j => Ioo (a j) (a j + ℓ)), Torus.boxMode a ℓ ∅ n x * u x =
        ∫ x in Set.pi univ (fun j => Ioo (a j) (a j + ℓ)), u x * Torus.boxMode a ℓ ∅ n x := by
      congr 1
      funext x
      ring
    show ∫ x, Torus.boxMode a ℓ {i} n x * G x i ∂normalizedCubeMeasure R =
      -(Real.pi * n i / ℓ) * ∫ x, Torus.boxMode a ℓ ∅ n x * u x ∂normalizedCubeMeasure R
    rw [integral_normalized_eq_open, integral_normalized_eq_open, hU, e1, e2, h]
    ring
  -- the mean
  have hc0 : c 0 = cubeAverage R u := by
    show ∫ x, Torus.boxMode a ℓ ∅ 0 x * u x ∂normalizedCubeMeasure R = cubeAverage R u
    simp only [Torus.boxMode, Pi.zero_apply, Int.cast_zero, mul_zero, zero_mul, zero_div,
      Real.cos_zero, Finset.notMem_empty, ite_false, Finset.prod_const_one, one_mul]
    rw [cubeAverage_eq_integral_normalizedCubeMeasure]
  have henergy : energy R (fun x => u x - cubeAverage R u) =
      ∫ x, u x ^ 2 ∂normalizedCubeMeasure R - c 0 ^ 2 := by
    rw [energy_sub R hu (memLp_const _), pairing_const_right, energy_const, hc0,
      energy_eq_integral_sq]
    ring
  -- termwise comparison
  have hterm : ∀ n : Fin d → ℤ, c n ^ 2 - (if n = 0 then c 0 ^ 2 else 0) ≤
      ∑ i, ((n i : ℝ) ^ 2 * c n ^ 2) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      simp
    · rw [ite_eq_right hn, sub_zero, ← Finset.sum_mul]
      obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
        by_contra h
        exact hn (funext fun i => by_contra fun h' => h ⟨i, h'⟩)
      have h1 : (1 : ℝ) ≤ (n i : ℝ) ^ 2 := by
        have : (1 : ℤ) ≤ n i ^ 2 := by
          have := Int.one_le_abs hi
          nlinarith [abs_mul_abs_self (n i), sq_abs (n i)]
        exact_mod_cast this
      have h2 : (n i : ℝ) ^ 2 ≤ ∑ j, (n j : ℝ) ^ 2 :=
        Finset.single_le_sum (fun j _ => sq_nonneg (n j : ℝ)) (Finset.mem_univ i)
      nlinarith [sq_nonneg (c n)]
  have hL : HasSum (fun n : Fin d → ℤ => c n ^ 2 - (if n = 0 then c 0 ^ 2 else 0))
      (∫ x, u x ^ 2 ∂normalizedCubeMeasure R - c 0 ^ 2) := hP.sub (hasSum_ite_eq 0 (c 0 ^ 2))
  have hRi : ∀ i, HasSum (fun n : Fin d → ℤ => (n i : ℝ) ^ 2 * c n ^ 2)
      ((ℓ / Real.pi) ^ 2 * ∑' n, s i n ^ 2) := by
    intro i
    refine ((hS i).hasSum.mul_left ((ℓ / Real.pi) ^ 2)).congr_fun fun n => ?_
    rw [hcoef]
    have h1 : (ℓ / Real.pi) * (Real.pi / ℓ) = 1 := by field_simp
    calc (n i : ℝ) ^ 2 * c n ^ 2 =
        ((ℓ / Real.pi) * (Real.pi / ℓ)) ^ 2 * ((n i : ℝ) ^ 2 * c n ^ 2) := by rw [h1]; ring
      _ = (ℓ / Real.pi) ^ 2 * (-(Real.pi * n i / ℓ) * c n) ^ 2 := by ring
  have hR : HasSum (fun n : Fin d → ℤ => ∑ i, ((n i : ℝ) ^ 2 * c n ^ 2))
      (∑ i, (ℓ / Real.pi) ^ 2 * ∑' n, s i n ^ 2) := hasSum_sum fun i _ => hRi i
  have hmain := hasSum_le hterm hL hR
  rw [henergy]
  refine hmain.trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (sq_nonneg _)
  rw [energy_eq_integral_sq]
  exact hSle i

/-! ### Depth-`j` cells -/

theorem hasWeakGradientOn_mono {U V : Set (Vec d)} (hUV : U ⊆ V) (hV : MeasurableSet V)
    {u : Vec d → ℝ} {G : Vec d → Vec d} (hw : HasWeakGradientOn V u G) :
    HasWeakGradientOn U u G := by
  intro i φ hφ hφc hφU
  have h := hw i φ hφ hφc (hφU.trans hUV)
  have hzero : ∀ x ∉ tsupport φ, φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hdzero : ∀ x ∉ tsupport φ, fderiv ℝ φ x = 0 := fun x hx =>
    fderiv_of_notMem_tsupport ℝ hx
  have e1 : ∫ x in V, u x * (fderiv ℝ φ x) (basisVec i) =
      ∫ x in U, u x * (fderiv ℝ φ x) (basisVec i) := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hV hUV fun x hx => ?_
    have : x ∉ tsupport φ := fun h' => hx.2 (hφU h')
    simp [hdzero x this]
  have e2 : ∫ x in V, G x i * φ x = ∫ x in U, G x i * φ x := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hV hUV fun x hx => ?_
    have : x ∉ tsupport φ := fun h' => hx.2 (hφU h')
    simp [hzero x this]
  rw [← e1, ← e2]
  exact h

theorem descendantsAverage_le {Q : TriadicCube d} {j : ℕ} {F H : TriadicCube d → ℝ}
    (h : ∀ R ∈ descendantsAtDepth Q j, F R ≤ H R) :
    descendantsAverage Q j F ≤ descendantsAverage Q j H := by
  unfold descendantsAverage
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum h)
    (inv_nonneg.2 (Nat.cast_nonneg _))

theorem descendantsAverage_sum {Q : TriadicCube d} {j : ℕ} (F : Fin d → TriadicCube d → ℝ) :
    descendantsAverage Q j (fun R => ∑ i, F i R) = ∑ i, descendantsAverage Q j (F i) := by
  show (((descendantsAtDepth Q j).card : ℝ)⁻¹ * ∑ R ∈ descendantsAtDepth Q j, ∑ i, F i R) =
    ∑ i, ((descendantsAtDepth Q j).card : ℝ)⁻¹ * ∑ R ∈ descendantsAtDepth Q j, F i R
  rw [Finset.sum_comm, Finset.mul_sum]

theorem energy_eq_descendantsAverage (Q : TriadicCube d) (j : ℕ) {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    energy Q f = descendantsAverage Q j (fun R => energy R f) := by
  unfold energy pairing
  exact cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q j _
    (integrableOn_of_integrable_normalizedCubeMeasure Q (hf.integrable_mul hf))

/-- **H8 (cell Poincaré inequality, sharp constant).** -/
theorem cell_poincare_of_weakGradient (Q : TriadicCube d) (j : ℕ) {u : Vec d → ℝ}
    {G : Vec d → Vec d} (hu : MemL2On (openCubeSet Q) u) (hG : GradMemL2On (openCubeSet Q) G)
    (hw : HasWeakGradientOn (openCubeSet Q) u G) :
    energy Q (fun x => u x - cubeProjection Q j u x) ≤
      cubeScaleFactor Q ^ 2 / (9 ^ j * Real.pi ^ 2) * ∑ i, energy Q (fun x => G x i) := by
  have huQ : MemLp u 2 (normalizedCubeMeasure Q) := memLp_normalized_of_memL2On hu
  have hGQ : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q) := fun i =>
    memLp_normalized_of_memL2On (hG i)
  have hres : MemLp (fun x => u x - cubeProjection Q j u x) 2 (normalizedCubeMeasure Q) :=
    huQ.sub (projection_memLp Q j u 2)
  rw [energy_eq_descendantsAverage Q j hres]
  have hcell : ∀ R ∈ descendantsAtDepth Q j,
      energy R (fun x => u x - cubeProjection Q j u x) ≤
        cubeScaleFactor Q ^ 2 / (9 ^ j * Real.pi ^ 2) * ∑ i, energy R (fun x => G x i) := by
    intro R hR
    have heq : energy R (fun x => u x - cubeProjection Q j u x) =
        energy R (fun x => u x - cubeAverage R u) := by
      unfold energy pairing
      refine cubeAverage_congr_on_cubeSet fun x hx => ?_
      beta_reduce
      rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth u hR hx]
    have hside : cubeScaleFactor R = cubeScaleFactor Q / 3 ^ j :=
      cubeScaleFactor_descendant_eq_div_pow hR
    have hwR : HasWeakGradientOn (openCubeSet R) u G :=
      hasWeakGradientOn_mono (openCubeSet_subset_of_mem_descendantsAtDepth hR)
        (by rw [openCubeSet_eq_box]; exact MeasurableSet.univ_pi fun _ => measurableSet_Ioo) hw
    rw [heq]
    refine (cube_poincare R (memLp_on_descendant_of_memLp hR huQ)
      (fun i => memLp_on_descendant_of_memLp hR (hGQ i)) hwR).trans (le_of_eq ?_)
    rw [hside]
    congr 1
    have h9 : (9 : ℝ) ^ j = ((3 : ℝ) ^ j) ^ 2 := by
      rw [← pow_mul, mul_comm j 2, pow_mul]
      norm_num
    rw [div_pow, div_pow, h9]
    field_simp
  refine (descendantsAverage_le hcell).trans (le_of_eq ?_)
  rw [descendantsAverage_mul_left, descendantsAverage_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (energy_eq_descendantsAverage Q j (hGQ i)).symm

end GMCExplicitDelta.Haar
