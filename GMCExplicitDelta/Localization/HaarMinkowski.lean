module

public import GMCExplicitDelta.Localization.HaarDefs
public import Mathlib.Analysis.Real.Sqrt

/-!
# Minkowski's inequality for the Haar norm `P_s` (H1)

`haarPrimal_add_le_proof`: for `L²` fields, `P_s(h₁)² ≤ c₁²`, `P_s(h₂)² ≤ c₂²` imply
`P_s(h₁ + h₂)² ≤ (c₁ + c₂)²`. Proof: additivity of the Haar increments, the `L²` triangle inequality
for each component, Cauchy–Schwarz over the components and over the scales (on partial sums).
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open scoped ENNReal

namespace GMCExplicitDelta.Localization

variable {d : ℕ}

/-- `∑(√u + √v)² ≤ (√∑u + √∑v)²` for nonnegative families (Cauchy–Schwarz). -/
theorem sum_sqrt_add_sq_le {ι : Type*} (s : Finset ι) {u v : ι → ℝ} (hu : ∀ i, 0 ≤ u i)
    (hv : ∀ i, 0 ≤ v i) :
    ∑ i ∈ s, (Real.sqrt (u i) + Real.sqrt (v i)) ^ 2 ≤
      (Real.sqrt (∑ i ∈ s, u i) + Real.sqrt (∑ i ∈ s, v i)) ^ 2 := by
  have hcs := Real.sum_sqrt_mul_sqrt_le s hu hv
  have hU : 0 ≤ ∑ i ∈ s, u i := Finset.sum_nonneg fun i _ => hu i
  have hV : 0 ≤ ∑ i ∈ s, v i := Finset.sum_nonneg fun i _ => hv i
  have hexp : ∑ i ∈ s, (Real.sqrt (u i) + Real.sqrt (v i)) ^ 2 =
      ∑ i ∈ s, u i + 2 * ∑ i ∈ s, Real.sqrt (u i) * Real.sqrt (v i) + ∑ i ∈ s, v i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [add_sq, Real.sq_sqrt (hu i), Real.sq_sqrt (hv i)]
    ring
  rw [hexp, add_sq, Real.sq_sqrt hU, Real.sq_sqrt hV]
  nlinarith [hcs]

theorem cubeIncrement_add (Q : Homogenization.TriadicCube d) (k : ℕ) {f g : Homogenization.Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    cubeIncrement Q k (fun x => f x + g x) =
      fun x => cubeIncrement Q k f x + cubeIncrement Q k g x := by
  cases k with
  | zero => exact Haar.projection_add Q 0 hf hg
  | succ k =>
    funext x
    simp only [cubeIncrement_succ]
    rw [Haar.projection_add Q (k + 1) hf hg, Haar.projection_add Q k hf hg]
    ring

theorem energy_add_le (Q : Homogenization.TriadicCube d) {f g : Homogenization.Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    Haar.energy Q (fun x => f x + g x) ≤
      (Real.sqrt (Haar.energy Q f) + Real.sqrt (Haar.energy Q g)) ^ 2 := by
  have hpair := Haar.abs_pairing_le Q hf hg
  have hexp : Haar.energy Q (fun x => f x + g x) =
      Haar.energy Q f + 2 * Haar.pairing Q f g + Haar.energy Q g := by
    simp only [Haar.energy, Haar.pairing, cubeAverage_eq_integral_normalizedCubeMeasure]
    have h1 := hf.integrable_mul hf
    have h2 := hf.integrable_mul hg
    have h3 := hg.integrable_mul hg
    have e : (fun x => (f x + g x) * (f x + g x)) =
        fun x => (f x * f x + 2 * (f x * g x)) + g x * g x := by
      funext x; ring
    rw [e, integral_add (f := fun x => f x * f x + 2 * (f x * g x)) (g := fun x => g x * g x)
      (h1.add (h2.const_mul 2)) h3,
      integral_add (f := fun x => f x * f x) (g := fun x => 2 * (f x * g x)) h1 (h2.const_mul 2),
      integral_const_mul]
  rw [hexp, add_sq, Real.sq_sqrt (Haar.energy_nonneg Q f), Real.sq_sqrt (Haar.energy_nonneg Q g)]
  have : Haar.pairing Q f g ≤ Real.sqrt (Haar.energy Q f) * Real.sqrt (Haar.energy Q g) :=
    (le_abs_self _).trans hpair
  nlinarith [this]

/-- The squared `k`-th Haar block of a field: `‖D_k h‖² = ∑_i ‖D_k h_i‖²`. -/
noncomputable def blockSq (Q : Homogenization.TriadicCube d) (k : ℕ)
    (h : Homogenization.Vec d → Homogenization.Vec d) : ℝ :=
  ∑ i, Haar.energy Q (cubeIncrement Q k fun x => h x i)

theorem blockSq_nonneg (Q : Homogenization.TriadicCube d) (k : ℕ)
    (h : Homogenization.Vec d → Homogenization.Vec d) : 0 ≤ blockSq Q k h :=
  Finset.sum_nonneg fun _ _ => Haar.energy_nonneg Q _

theorem blockSq_add_le (Q : Homogenization.TriadicCube d) (k : ℕ)
    {h₁ h₂ : Homogenization.Vec d → Homogenization.Vec d}
    (hh₁ : ∀ i, MemLp (fun x => h₁ x i) 2 (normalizedCubeMeasure Q))
    (hh₂ : ∀ i, MemLp (fun x => h₂ x i) 2 (normalizedCubeMeasure Q)) :
    blockSq Q k (h₁ + h₂) ≤
      (Real.sqrt (blockSq Q k h₁) + Real.sqrt (blockSq Q k h₂)) ^ 2 := by
  unfold blockSq
  calc ∑ i, Haar.energy Q (cubeIncrement Q k fun x => (h₁ + h₂) x i) ≤
      ∑ i, (Real.sqrt (Haar.energy Q (cubeIncrement Q k fun x => h₁ x i)) +
        Real.sqrt (Haar.energy Q (cubeIncrement Q k fun x => h₂ x i))) ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have e : (fun x => (h₁ + h₂) x i) = fun x => h₁ x i + h₂ x i := rfl
        rw [e, cubeIncrement_add Q k (hh₁ i) (hh₂ i)]
        exact energy_add_le Q (Haar.increment_memLp Q k _) (Haar.increment_memLp Q k _)
    _ ≤ _ := sum_sqrt_add_sq_le _ (fun i => Haar.energy_nonneg Q _)
        (fun i => Haar.energy_nonneg Q _)

/-- **H1 (Minkowski for `P_s`).** -/
theorem haarPrimal_add_le_proof (Q : Homogenization.TriadicCube d) {q : ℝ} (hq : 0 < q)
    {h₁ h₂ : Homogenization.Vec d → Homogenization.Vec d}
    (hh₁ : ∀ i, MemLp (fun x => h₁ x i) 2 (normalizedCubeMeasure Q))
    (hh₂ : ∀ i, MemLp (fun x => h₂ x i) 2 (normalizedCubeMeasure Q))
    {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (h₁le : haarPrimal Q q h₁ ≤ ENNReal.ofReal (c₁ ^ 2))
    (h₂le : haarPrimal Q q h₂ ≤ ENNReal.ofReal (c₂ ^ 2)) :
    haarPrimal Q q (h₁ + h₂) ≤ ENNReal.ofReal ((c₁ + c₂) ^ 2) := by
  -- partial sums of the two given series
  have hpart : ∀ (h : Homogenization.Vec d → Homogenization.Vec d) (c : ℝ),
      haarPrimal Q q h ≤ ENNReal.ofReal (c ^ 2) →
      ∀ N, ∑ k ∈ Finset.range N, q ^ k * blockSq Q k h ≤ c ^ 2 := by
    intro h c hle N
    have hnn : ∀ k ∈ Finset.range N, 0 ≤ q ^ k * blockSq Q k h := fun k _ =>
      mul_nonneg (pow_nonneg hq.le k) (blockSq_nonneg Q k h)
    have h1 : ENNReal.ofReal (∑ k ∈ Finset.range N, q ^ k * blockSq Q k h) ≤
        ENNReal.ofReal (c ^ 2) := by
      rw [ENNReal.ofReal_sum_of_nonneg hnn]
      exact (ENNReal.sum_le_tsum _).trans hle
    exact (ENNReal.ofReal_le_ofReal_iff (sq_nonneg c)).mp h1
  unfold haarPrimal
  refine ENNReal.tsum_le_of_sum_range_le fun N => ?_
  have hnn : ∀ k ∈ Finset.range N, 0 ≤ q ^ k * blockSq Q k (h₁ + h₂) := fun k _ =>
    mul_nonneg (pow_nonneg hq.le k) (blockSq_nonneg Q k _)
  show ∑ k ∈ Finset.range N, ENNReal.ofReal (q ^ k * blockSq Q k (h₁ + h₂)) ≤ _
  rw [← ENNReal.ofReal_sum_of_nonneg hnn]
  refine ENNReal.ofReal_le_ofReal ?_
  set u : ℕ → ℝ := fun k => q ^ k * blockSq Q k h₁ with hu
  set v : ℕ → ℝ := fun k => q ^ k * blockSq Q k h₂ with hv
  have hu0 : ∀ k, 0 ≤ u k := fun k => mul_nonneg (pow_nonneg hq.le k) (blockSq_nonneg Q k _)
  have hv0 : ∀ k, 0 ≤ v k := fun k => mul_nonneg (pow_nonneg hq.le k) (blockSq_nonneg Q k _)
  have hterm : ∀ k, q ^ k * blockSq Q k (h₁ + h₂) ≤ (Real.sqrt (u k) + Real.sqrt (v k)) ^ 2 := by
    intro k
    have hqk : 0 ≤ q ^ k := pow_nonneg hq.le k
    calc q ^ k * blockSq Q k (h₁ + h₂) ≤
        q ^ k * (Real.sqrt (blockSq Q k h₁) + Real.sqrt (blockSq Q k h₂)) ^ 2 :=
          mul_le_mul_of_nonneg_left (blockSq_add_le Q k hh₁ hh₂) hqk
      _ = (Real.sqrt (u k) + Real.sqrt (v k)) ^ 2 := by
          rw [hu, hv]
          simp only
          rw [Real.sqrt_mul hqk, Real.sqrt_mul hqk, ← mul_add, mul_pow, Real.sq_sqrt hqk]
  calc ∑ k ∈ Finset.range N, q ^ k * blockSq Q k (h₁ + h₂) ≤
      ∑ k ∈ Finset.range N, (Real.sqrt (u k) + Real.sqrt (v k)) ^ 2 :=
        Finset.sum_le_sum fun k _ => hterm k
    _ ≤ (Real.sqrt (∑ k ∈ Finset.range N, u k) + Real.sqrt (∑ k ∈ Finset.range N, v k)) ^ 2 :=
        sum_sqrt_add_sq_le _ hu0 hv0
    _ ≤ (c₁ + c₂) ^ 2 := by
        have h1 : Real.sqrt (∑ k ∈ Finset.range N, u k) ≤ c₁ := by
          rw [Real.sqrt_le_left hc₁]
          exact hpart h₁ c₁ h₁le N
        have h2 : Real.sqrt (∑ k ∈ Finset.range N, v k) ≤ c₂ := by
          rw [Real.sqrt_le_left hc₂]
          exact hpart h₂ c₂ h₂le N
        exact pow_le_pow_left₀ (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
          (add_le_add h1 h2) 2

end GMCExplicitDelta.Localization
