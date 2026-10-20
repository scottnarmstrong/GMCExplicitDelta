module

public import GMCExplicitDelta.Steps.LocalizationHaar
public import GMCExplicitDelta.Localization.ProbLemmas

/-!
# Localization lane: lemmas for the H11 assembly

Vector-field `L²` calculus on a triadic cube (`vecEnergy` as a cube average, Cauchy–Schwarz, the
energy estimate of a weak Neumann equation), Minkowski for finite sums of `P_s` (from
`haarPrimal_add_le`), and `L²` bounds for fields multiplied by the scaled cutoff gradient.
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open scoped ENNReal

namespace GMCExplicitDelta.Localization

open Assembly Contract

variable {d : ℕ}

section VectorCalculus

variable (Q : Homogenization.TriadicCube d)

theorem vecEnergy_nonneg (G : Homogenization.Vec d → Homogenization.Vec d) : 0 ≤ vecEnergy Q G :=
  Finset.sum_nonneg fun _ _ => Haar.energy_nonneg Q _

theorem incNorm_sq (k : ℕ) (G : Homogenization.Vec d → Homogenization.Vec d) :
    incNorm Q k G ^ 2 = vecEnergy Q (vecIncrement Q k G) := by
  rw [incNorm]
  exact Real.sq_sqrt (vecEnergy_nonneg Q (vecIncrement Q k G))

theorem integrable_vecDot {G H : Homogenization.Vec d → Homogenization.Vec d}
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q))
    (hH : ∀ i, MemLp (fun x => H x i) 2 (normalizedCubeMeasure Q)) :
    Integrable (fun x => vecDot (G x) (H x)) (normalizedCubeMeasure Q) := by
  simp only [vecDot]
  exact integrable_finsetSum _ fun i _ => (hG i).integrable_mul (hH i)

theorem vecEnergy_eq_cubeAverage {G : Homogenization.Vec d → Homogenization.Vec d}
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q)) :
    vecEnergy Q G = cubeAverage Q (fun x => vecNormSq (G x)) := by
  rw [cubeAverage_eq_integral_normalizedCubeMeasure]
  simp only [vecNormSq, vecDot]
  rw [integral_finsetSum (f := fun i x => G x i * G x i) _
    fun i _ => (hG i).integrable_mul (hG i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Haar.energy, Haar.pairing, cubeAverage_eq_integral_normalizedCubeMeasure]

theorem vecDot_le_sqrt (a b : Homogenization.Vec d) :
    vecDot a b ≤ Real.sqrt (vecNormSq a * vecNormSq b) :=
  (le_abs_self _).trans (Real.abs_le_sqrt (sq_vecDot_le_vecNormSq_mul_vecNormSq a b))

/-- **Cauchy–Schwarz** for vector fields on `Q`: `⨍G·H ≤ ‖G‖‖H‖`. -/
theorem cubeAverage_vecDot_le {G H : Homogenization.Vec d → Homogenization.Vec d}
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q))
    (hH : ∀ i, MemLp (fun x => H x i) 2 (normalizedCubeMeasure Q)) :
    cubeAverage Q (fun x => vecDot (G x) (H x)) ≤
      Real.sqrt (vecEnergy Q G) * Real.sqrt (vecEnergy Q H) := by
  have hGG := integrable_vecDot Q hG hG
  have hHH := integrable_vecDot Q hH hH
  rw [vecEnergy_eq_cubeAverage Q hG, vecEnergy_eq_cubeAverage Q hH,
    cubeAverage_eq_integral_normalizedCubeMeasure, cubeAverage_eq_integral_normalizedCubeMeasure,
    cubeAverage_eq_integral_normalizedCubeMeasure]
  calc ∫ x, vecDot (G x) (H x) ∂normalizedCubeMeasure Q ≤
      ∫ x, Real.sqrt (vecNormSq (G x) * vecNormSq (H x)) ∂normalizedCubeMeasure Q :=
        integral_mono (integrable_vecDot Q hG hH)
          (integrable_sqrt_mul hGG hHH (fun x => vecNormSq_nonneg _)
            (fun x => vecNormSq_nonneg _))
          (fun x => vecDot_le_sqrt _ _)
    _ ≤ _ := integral_sqrt_mul_le hGG hHH (fun x => vecNormSq_nonneg _)
        (fun x => vecNormSq_nonneg _)

/-- **Energy estimate** of a weak Neumann equation: if `⨍∇w·∇φ = ⨍G·∇φ` for all `φ ∈ H¹(Q)`, then
`‖∇w‖² ≤ ‖G‖²`. -/
theorem vecEnergy_grad_le_of_weak {G : Homogenization.Vec d → Homogenization.Vec d}
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q))
    (w : H1Function (openCubeSet Q))
    (hw : ∀ φ : H1Function (openCubeSet Q),
      cubeAverage Q (fun x => vecDot (w.grad x) (φ.grad x)) =
        cubeAverage Q (fun x => vecDot (G x) (φ.grad x))) :
    vecEnergy Q w.grad ≤ vecEnergy Q G := by
  have hw' : ∀ i, MemLp (fun x => w.grad x i) 2 (normalizedCubeMeasure Q) := fun i =>
    H1Function.grad_memL2_normalizedCubeMeasure w i
  have h1 := hw w
  have hEeq : vecEnergy Q w.grad = cubeAverage Q (fun x => vecDot (w.grad x) (w.grad x)) :=
    vecEnergy_eq_cubeAverage Q hw'
  rw [← hEeq] at h1
  have h2 := cubeAverage_vecDot_le Q hG hw'
  rw [← h1] at h2
  set E := vecEnergy Q w.grad with hE
  set A := vecEnergy Q G with hA
  have hE0 : 0 ≤ E := vecEnergy_nonneg Q _
  have hA0 : 0 ≤ A := vecEnergy_nonneg Q _
  have hsE := Real.sq_sqrt hE0
  have hsA := Real.sq_sqrt hA0
  have hle : Real.sqrt E ≤ Real.sqrt A := by
    rcases (Real.sqrt_nonneg E).lt_or_eq with hpos | hzero
    · have : Real.sqrt E * Real.sqrt E ≤ Real.sqrt A * Real.sqrt E := by nlinarith
      exact le_of_mul_le_mul_right this hpos
    · rw [← hzero]; exact Real.sqrt_nonneg _
  nlinarith [Real.sqrt_nonneg E, Real.sqrt_nonneg A]

end VectorCalculus

/-! ### Minkowski for finite sums -/

theorem cubeIncrement_zero_fun (Q : Homogenization.TriadicCube d) (k : ℕ) :
    cubeIncrement Q k (fun _ => (0 : ℝ)) = fun _ => 0 := by
  funext x
  cases k with
  | zero =>
    by_cases hx : x ∈ cubeSet Q
    · exact cubeIncrement_zero_const_of_mem_cubeSet Q 0 hx
    · exact cubeIncrement_zero_const_of_not_mem_cubeSet Q 0 hx
  | succ k => exact cubeIncrement_succ_const Q k 0 x

theorem haarPrimal_zero (Q : Homogenization.TriadicCube d) (q : ℝ) :
    haarPrimal Q q 0 = 0 := by
  unfold haarPrimal
  have h : ∀ k : ℕ, ∑ i : Fin d, Haar.energy Q
      (cubeIncrement Q k fun x => (0 : Homogenization.Vec d → Homogenization.Vec d) x i) = 0 := by
    intro k
    refine Finset.sum_eq_zero fun i _ => ?_
    simp only [Pi.zero_apply]
    rw [cubeIncrement_zero_fun, Haar.energy_const]
    ring
  simp only [h, mul_zero, ENNReal.ofReal_zero, tsum_zero]

/-- **Minkowski for `P_s`, finite sums.** -/
theorem haarPrimal_sum_le (Q : Homogenization.TriadicCube d) {q : ℝ} (hq : 0 < q) {ι : Type*}
    (s : Finset ι) (h : ι → Homogenization.Vec d → Homogenization.Vec d) (c : ι → ℝ)
    (hh : ∀ j ∈ s, ∀ i, MemLp (fun x => h j x i) 2 (normalizedCubeMeasure Q))
    (hc : ∀ j ∈ s, 0 ≤ c j)
    (hle : ∀ j ∈ s, haarPrimal Q q (h j) ≤ ENNReal.ofReal (c j ^ 2)) :
    haarPrimal Q q (∑ j ∈ s, h j) ≤ ENNReal.ofReal ((∑ j ∈ s, c j) ^ 2) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [haarPrimal_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hs : ∀ i, MemLp (fun x => (∑ j ∈ s, h j) x i) 2 (normalizedCubeMeasure Q) := by
      intro i
      have : (fun x => (∑ j ∈ s, h j) x i) = fun x => ∑ j ∈ s, h j x i := by
        funext x
        simp only [Finset.sum_apply]
      rw [this]
      exact memLp_finsetSum _ fun j hj => hh j (Finset.mem_insert_of_mem hj) i
    exact haarPrimal_add_le Q hq (hh a (Finset.mem_insert_self a s)) hs
      (hc a (Finset.mem_insert_self a s))
      (Finset.sum_nonneg fun j hj => hc j (Finset.mem_insert_of_mem hj))
      (hle a (Finset.mem_insert_self a s))
      (ih (fun j hj => hh j (Finset.mem_insert_of_mem hj))
        (fun j hj => hc j (Finset.mem_insert_of_mem hj))
        (fun j hj => hle j (Finset.mem_insert_of_mem hj)))

/-! ### The cutoff gradient -/

theorem omegaEff_pos (row : Row d) (hO : row.Obligations) : 0 < row.omegaEff := by
  unfold Row.omegaEff
  split_ifs with h
  · norm_num
  · exact_mod_cast (hO.par2.2.2.2.2.2 h).2.1

theorem omegaEff_le (row : Row d) (hO : row.Obligations) : row.omegaEff ≤ 1 / 2 := by
  unfold Row.omegaEff
  split_ifs with h
  · norm_num
  · have hw := (hO.par2.2.2.2.2.2 h).2.2
    have hw' : (row.width : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr hw
    simpa using hw'

theorem ae_mem_cubeSet (Q : Homogenization.TriadicCube d) :
    ∀ᵐ x ∂normalizedCubeMeasure Q, x ∈ cubeSet Q := by
  have hrestrict : ∀ᵐ x ∂volume.restrict (cubeSet Q), x ∈ cubeSet Q :=
    ae_restrict_mem (measurableSet_cubeSet Q)
  simpa [normalizedCubeMeasure, cubeMeasure] using
    Measure.ae_smul_measure hrestrict (ENNReal.ofReal ((cubeVolume Q)⁻¹))

theorem abs_cubeCutoffGrad_le (row : Row d) (hO : row.Obligations) (n : ℕ)
    {x : Homogenization.Vec d} (hx : x ∈ cubeSet (originCube d (n : ℤ))) (i : Fin d) :
    |cubeCutoffGrad row n x i| ≤ row.kappaOmega / (3 : ℝ) ^ n := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hy : ∀ j, |x j / (3 : ℝ) ^ n| ≤ 1 / 2 := by
    intro j
    have hj := (mem_cubeSet_originCube_iff.mp hx) j
    rw [abs_div, abs_of_pos h3, div_le_iff₀ h3, abs_le]
    simp only [zpow_natCast] at hj
    constructor <;> linarith [hj.1, hj.2]
  have hsum := Haar.cutoffGradient_sq_sum_le_kappaOmega row (omegaEff_pos row hO)
    (omegaEff_le row hO) (fun j => x j / (3 : ℝ) ^ n) hy
  have hk : 0 ≤ row.kappaOmega := by
    unfold Row.kappaOmega; have := omegaEff_pos row hO; positivity
  have hsq : Haar.cutoffGradient row.omegaEff (fun j => x j / (3 : ℝ) ^ n) i ^ 2 ≤
      row.kappaOmega ^ 2 :=
    (Finset.single_le_sum (f := fun j => Haar.cutoffGradient row.omegaEff
      (fun j => x j / (3 : ℝ) ^ n) j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)).trans hsum
  have habs := abs_le_of_sq_le_sq' hsq hk
  rw [cubeCutoffGrad, abs_div, abs_of_pos h3]
  exact div_le_div_of_nonneg_right (abs_le.mpr habs) h3.le

theorem continuous_cubeCutoffGrad (row : Row d) (hO : row.Obligations) (n : ℕ) (i : Fin d) :
    Continuous fun x => cubeCutoffGrad row n x i := by
  have hω := omegaEff_le row hO
  have hs := Haar.cutoffSlope_continuous hω
  have hp := (Haar.cutoffProfile_contDiff hω).continuous
  unfold cubeCutoffGrad Haar.cutoffGradient
  refine Continuous.div_const ?_ _
  exact (hs.comp ((continuous_apply i).div_const _)).mul
    (continuous_finsetProd _ fun j _ => hp.comp ((continuous_apply j).div_const _))

/-- `L²` fields stay `L²` after multiplication by the cutoff gradient. -/
theorem memLp_smul_cutoffGrad (row : Row d) (hO : row.Obligations) (n : ℕ)
    {f : Homogenization.Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure (originCube d (n : ℤ)))) (i : Fin d) :
    MemLp (fun x => (f x • cubeCutoffGrad row n x) i) 2
      (normalizedCubeMeasure (originCube d (n : ℤ))) := by
  set C := row.kappaOmega / (3 : ℝ) ^ n with hC
  have hC0 : 0 ≤ C := by
    rw [hC]; unfold Row.kappaOmega; have := omegaEff_pos row hO; positivity
  refine MemLp.of_le (hf.const_mul C)
    (hf.aestronglyMeasurable.mul (continuous_cubeCutoffGrad row hO n i).aestronglyMeasurable) ?_
  filter_upwards [ae_mem_cubeSet (originCube d (n : ℤ))] with x hx
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg hC0]
  rw [mul_comm C]
  exact mul_le_mul_of_nonneg_left (abs_cubeCutoffGrad_le row hO n hx i) (abs_nonneg _)

end GMCExplicitDelta.Localization
