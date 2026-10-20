module

public import GMCExplicitDelta.Localization.H11Lemmas
public import GMCExplicitDelta.Proofs.Contraction.Haar
public import GMCExplicitDelta.Localization.Basic

/-!
# H11 assembly, step 1: the decomposition at a fixed depth `N`

For `u ∈ H¹(Q_n)`, `𝐅 = ∇u`, `a = E_0𝐅` and Neumann primitives `w_k = T D_k𝐅` (`1 ≤ k ≤ N`), the
remainder `R = u - a·x - ∑_k w_k` satisfies the weak Neumann equation with data `𝐅 - E_N𝐅`; hence
`P_s((u - ū)𝐠) ≤ b_0|a| + ∑_{k=1}^N b_k‖D_k𝐅‖ + 𝖻(η_ω)‖𝐅 - E_N𝐅‖` (H10, H9 + H5/H6, H9 + H8,
Minkowski).
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open scoped ENNReal

namespace GMCExplicitDelta.Localization

open Assembly Contract

variable {d : ℕ}

/-! ### Sums of `H¹` functions -/

theorem H1Function.sum_toFun' {U : Set (Homogenization.Vec d)} {ι : Type*} (s : Finset ι)
    (f : ι → H1Function U) (x : Homogenization.Vec d) :
    (∑ j ∈ s, f j).toFun x = ∑ j ∈ s, (f j).toFun x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, H1Function.add_toFun]
    simp only
    rw [← ih]

theorem H1Function.sum_grad' {U : Set (Homogenization.Vec d)} {ι : Type*} (s : Finset ι)
    (f : ι → H1Function U) (x : Homogenization.Vec d) :
    (∑ j ∈ s, f j).grad x = ∑ j ∈ s, (f j).grad x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, H1Function.add_grad]
    simp only
    rw [ih]

/-! ### Linearity of cube averages -/

section Linear

variable (Q : Homogenization.TriadicCube d)

theorem cubeAverage_sub' {f g : Homogenization.Vec d → ℝ}
    (hf : Integrable f (normalizedCubeMeasure Q)) (hg : Integrable g (normalizedCubeMeasure Q)) :
    cubeAverage Q (fun x => f x - g x) = cubeAverage Q f - cubeAverage Q g := by
  simp only [cubeAverage_eq_integral_normalizedCubeMeasure]
  exact integral_sub hf hg

theorem cubeAverage_finsetSum {ι : Type*} (s : Finset ι) {f : ι → Homogenization.Vec d → ℝ}
    (hf : ∀ j ∈ s, Integrable (f j) (normalizedCubeMeasure Q)) :
    cubeAverage Q (fun x => ∑ j ∈ s, f j x) = ∑ j ∈ s, cubeAverage Q (f j) := by
  simp only [cubeAverage_eq_integral_normalizedCubeMeasure]
  exact integral_finsetSum s hf

theorem vecDot_sub_sub_sum {ι : Type*} (s : Finset ι) (P a : Homogenization.Vec d)
    (A : ι → Homogenization.Vec d) (H : Homogenization.Vec d) :
    vecDot (P - a - ∑ j ∈ s, A j) H = vecDot P H - vecDot a H - ∑ j ∈ s, vecDot (A j) H := by
  simp only [vecDot, Pi.sub_apply, Finset.sum_apply, sub_mul, Finset.sum_sub_distrib,
    Finset.sum_mul]
  rw [Finset.sum_comm]

/-- `⨍(P - a - ∑_k A_k)·H = ⨍P·H - ⨍a·H - ∑_k ⨍A_k·H` for `L²` fields. -/
theorem cubeAverage_vecDot_sub_sub_sum {ι : Type*} (s : Finset ι)
    {P H : Homogenization.Vec d → Homogenization.Vec d} (a : Homogenization.Vec d)
    {A : ι → Homogenization.Vec d → Homogenization.Vec d}
    (hP : ∀ i, MemLp (fun x => P x i) 2 (normalizedCubeMeasure Q))
    (hH : ∀ i, MemLp (fun x => H x i) 2 (normalizedCubeMeasure Q))
    (hA : ∀ j ∈ s, ∀ i, MemLp (fun x => A j x i) 2 (normalizedCubeMeasure Q)) :
    cubeAverage Q (fun x => vecDot (P x - a - ∑ j ∈ s, A j x) (H x)) =
      cubeAverage Q (fun x => vecDot (P x) (H x)) - cubeAverage Q (fun x => vecDot a (H x)) -
        ∑ j ∈ s, cubeAverage Q (fun x => vecDot (A j x) (H x)) := by
  have ha : ∀ i, MemLp (fun _ : Homogenization.Vec d => a i) 2 (normalizedCubeMeasure Q) :=
    fun i => memLp_const _
  simp only [vecDot_sub_sub_sum]
  rw [cubeAverage_sub' Q (f := fun x => vecDot (P x) (H x) - vecDot a (H x))
      (g := fun x => ∑ j ∈ s, vecDot (A j x) (H x))
      ((integrable_vecDot Q hP hH).sub (integrable_vecDot Q ha hH))
      (integrable_finsetSum _ fun j hj => integrable_vecDot Q (hA j hj) hH),
    cubeAverage_sub' Q (f := fun x => vecDot (P x) (H x)) (g := fun x => vecDot a (H x))
      (integrable_vecDot Q hP hH) (integrable_vecDot Q ha hH),
    cubeAverage_finsetSum Q s (f := fun j x => vecDot (A j x) (H x))
      fun j hj => integrable_vecDot Q (hA j hj) hH]

end Linear

/-! ### Row constants -/

theorem etaOmega_div_kappaOmega_sq (row : Row d) (hO : row.Obligations) :
    row.etaOmega / row.kappaOmega ^ 2 = 1 / Real.pi ^ 2 := by
  have hω := omegaEff_pos row hO
  unfold Row.etaOmega Row.kappaOmega
  field_simp
  norm_num

theorem minSeries_nonneg {q Λ H : ℝ} (hq : 0 ≤ q) (hΛ : 0 ≤ Λ) (hH : 0 ≤ H) :
    0 ≤ minSeries q Λ H :=
  tsum_nonneg fun j => mul_nonneg (pow_nonneg hq j) (le_min hΛ (by positivity))

theorem qs_pos (row : Row d) : 0 < row.qs := Real.rpow_pos_of_pos (by norm_num) _

theorem multSq_nonneg (row : Row d) (hO : row.Obligations) {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    0 ≤ multSq row Λ := by
  have hq1 := (haar_majorants row hO).1.1
  have hη : 0 ≤ row.etaOmega := by unfold Row.etaOmega; positivity
  unfold multSq
  have := minSeries_nonneg (qs_pos row).le hΛ (mul_nonneg hη (by positivity) :
    0 ≤ row.etaOmega * (1 + (d : ℝ) * Λ))
  have : 0 ≤ (row.qs - 1) * minSeries row.qs Λ (row.etaOmega * (1 + (d : ℝ) * Λ)) :=
    mul_nonneg (by linarith) this
  linarith

theorem haarB_sq_eq_multSq (row : Row d) (hO : row.Obligations) {k : ℕ} (hk : 1 ≤ k) :
    row.haarB k ^ 2 = multSq row (row.haarL k) := by
  have hne : k ≠ 0 := by omega
  rw [Row.haarB, ite_eq_right hne]
  exact Real.sq_sqrt (multSq_nonneg row hO (Haar.haarL_nonneg row k))

end GMCExplicitDelta.Localization
