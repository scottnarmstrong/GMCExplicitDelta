module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Localization lane: elementary integral inequalities

* `sqrt_mul_le_add_half`, `integrable_sqrt_mul`, `integral_sqrt_mul_le`: the Cauchy–Schwarz inequality
  `∫√(fg) ≤ √(∫f)√(∫g)` for nonnegative integrable `f, g` (proved by the AM-GM bound
  `√(fg) ≤ (tf + g/t)/2` and optimization in `t`, without `L^p` spaces).
* `integral_le_of_pointwise_bound`: the expectation step of L4. If `S ≤ a√A ∑_k b_k(√D_k + √G_k) + Z`
  on a measurable event `G` (and the right side is nonnegative everywhere), then
  `∫S ≤ a√(∫A) ∑_k b_k(√(∫D_k) + √(∫G_k)) + ∫Z + ∫_{Gᶜ} S`.
-/

@[expose] public section

open MeasureTheory

namespace GMCExplicitDelta.Localization

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem sqrt_mul_le_add_half {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x * y) ≤ (x + y) / 2 := by
  rw [Real.sqrt_mul hx]
  have h1 := Real.sq_sqrt hx
  have h2 := Real.sq_sqrt hy
  nlinarith [sq_nonneg (Real.sqrt x - Real.sqrt y)]

/-- AM-GM with a parameter: `√(xy) ≤ (tx + y/t)/2` for `t > 0`. -/
theorem sqrt_mul_le_param {x y t : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (ht : 0 < t) :
    Real.sqrt (x * y) ≤ (t * x + y / t) / 2 := by
  have h : x * y = (t * x) * (y / t) := by field_simp
  rw [h]
  exact sqrt_mul_le_add_half (by positivity) (by positivity)

theorem integrable_sqrt_mul {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω) :
    Integrable (fun ω => Real.sqrt (f ω * g ω)) μ := by
  refine Integrable.mono' ((hf.add hg).div_const 2) ?_ ?_
  · exact Real.continuous_sqrt.comp_aestronglyMeasurable
      (hf.aestronglyMeasurable.mul hg.aestronglyMeasurable)
  · refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact sqrt_mul_le_add_half (hf0 ω) (hg0 ω)

/-- A real `X` with `X ≤ (ta + b/t)/2` for every `t > 0` (and `a, b ≥ 0`) satisfies `X ≤ √a√b`. -/
theorem le_sqrt_mul_sqrt_of_forall {X a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ t : ℝ, 0 < t → X ≤ (t * a + b / t) / 2) : X ≤ Real.sqrt a * Real.sqrt b := by
  rcases le_or_gt X 0 with hX | hX
  · exact hX.trans (by positivity)
  rcases ha.lt_or_eq with ha' | ha'
  · have key := h (X / a) (div_pos hX ha')
    have hsq : X ^ 2 ≤ a * b := by
      have e : (X / a * a + b / (X / a)) / 2 = (X + a * b / X) / 2 := by
        field_simp
      rw [e] at key
      have : X ≤ a * b / X := by linarith
      rw [le_div_iff₀ hX] at this
      nlinarith
    rw [← Real.sqrt_mul ha]
    calc X = Real.sqrt (X ^ 2) := (Real.sqrt_sq hX.le).symm
      _ ≤ Real.sqrt (a * b) := Real.sqrt_le_sqrt hsq
  · subst ha'
    exfalso
    have key := h ((b + 1) / X) (by positivity)
    rw [mul_zero, zero_add, div_div_eq_mul_div] at key
    have hlt : b * X / (b + 1) < 2 * X := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    linarith

/-- **Cauchy–Schwarz** `∫√(fg) ≤ √(∫f)√(∫g)` for nonnegative integrable `f, g`. -/
theorem integral_sqrt_mul_le {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω) :
    ∫ ω, Real.sqrt (f ω * g ω) ∂μ ≤
      Real.sqrt (∫ ω, f ω ∂μ) * Real.sqrt (∫ ω, g ω ∂μ) := by
  apply le_sqrt_mul_sqrt_of_forall (integral_nonneg hf0) (integral_nonneg hg0)
  intro t ht
  calc ∫ ω, Real.sqrt (f ω * g ω) ∂μ ≤ ∫ ω, (t * f ω + g ω / t) / 2 ∂μ :=
        integral_mono (integrable_sqrt_mul hf hg hf0 hg0)
          (((hf.const_mul t).add (hg.div_const t)).div_const 2)
          (fun ω => sqrt_mul_le_param (hf0 ω) (hg0 ω) ht)
    _ = (t * ∫ ω, f ω ∂μ + (∫ ω, g ω ∂μ) / t) / 2 := by
        rw [integral_div, integral_add (hf.const_mul t) (hg.div_const t), integral_const_mul,
          integral_div]

/-- **The expectation step of L4.** Let `G` be measurable. If, on `G`,
`S ≤ a√A ∑_{k∈s} b_k(√D_k + √G_k) + Z`, with all functions integrable, `A, D_k, G_k, Z ≥ 0`,
`a, b_k ≥ 0`, then `∫S ≤ a√(∫A) ∑_{k∈s} b_k(√(∫D_k) + √(∫G_k)) + ∫Z + ∫_{Gᶜ} S`. -/
theorem integral_le_of_pointwise_bound {G : Set Ω} (hG : MeasurableSet G)
    {S A Z : Ω → ℝ} {Dk Gk : ℕ → Ω → ℝ} {s : Finset ℕ} {b : ℕ → ℝ} {a : ℝ}
    (hS : Integrable S μ) (hA : Integrable A μ) (hZ : Integrable Z μ)
    (hD : ∀ k ∈ s, Integrable (Dk k) μ) (hGk : ∀ k ∈ s, Integrable (Gk k) μ)
    (hA0 : ∀ ω, 0 ≤ A ω) (hZ0 : ∀ ω, 0 ≤ Z ω) (hD0 : ∀ k ∈ s, ∀ ω, 0 ≤ Dk k ω)
    (hG0 : ∀ k ∈ s, ∀ ω, 0 ≤ Gk k ω) (hb : ∀ k ∈ s, 0 ≤ b k) (ha : 0 ≤ a)
    (hpt : ∀ ω ∈ G, S ω ≤
      a * (Real.sqrt (A ω) * ∑ k ∈ s, b k * (Real.sqrt (Dk k ω) + Real.sqrt (Gk k ω))) + Z ω) :
    ∫ ω, S ω ∂μ ≤
      a * (Real.sqrt (∫ ω, A ω ∂μ) * ∑ k ∈ s, b k *
        (Real.sqrt (∫ ω, Dk k ω ∂μ) + Real.sqrt (∫ ω, Gk k ω ∂μ))) +
        ∫ ω, Z ω ∂μ + ∫ ω in Gᶜ, S ω ∂μ := by
  -- the pointwise main term as a finite sum of square roots of products
  let T : Ω → ℝ := fun ω => ∑ k ∈ s, b k *
    (Real.sqrt (A ω * Dk k ω) + Real.sqrt (A ω * Gk k ω))
  have hTeq : ∀ ω, Real.sqrt (A ω) * ∑ k ∈ s, b k * (Real.sqrt (Dk k ω) + Real.sqrt (Gk k ω)) =
      T ω := by
    intro ω
    simp only [T, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Real.sqrt_mul (hA0 ω), Real.sqrt_mul (hA0 ω)]
    ring
  have hT0 : ∀ ω, 0 ≤ T ω := fun ω =>
    Finset.sum_nonneg fun k hk => mul_nonneg (hb k hk) (by positivity)
  have hterm : ∀ k ∈ s, Integrable
      (fun ω => b k * (Real.sqrt (A ω * Dk k ω) + Real.sqrt (A ω * Gk k ω))) μ := fun k hk =>
    ((integrable_sqrt_mul hA (hD k hk) hA0 (hD0 k hk)).add
      (integrable_sqrt_mul hA (hGk k hk) hA0 (hG0 k hk))).const_mul (b k)
  have hTint : Integrable T μ := integrable_finsetSum _ hterm
  have hTle : ∫ ω, T ω ∂μ ≤ Real.sqrt (∫ ω, A ω ∂μ) * ∑ k ∈ s, b k *
      (Real.sqrt (∫ ω, Dk k ω ∂μ) + Real.sqrt (∫ ω, Gk k ω ∂μ)) := by
    rw [integral_finsetSum s hterm, Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    rw [integral_const_mul, integral_add (integrable_sqrt_mul hA (hD k hk) hA0 (hD0 k hk))
      (integrable_sqrt_mul hA (hGk k hk) hA0 (hG0 k hk))]
    have h1 := integral_sqrt_mul_le hA (hD k hk) hA0 (hD0 k hk)
    have h2 := integral_sqrt_mul_le hA (hGk k hk) hA0 (hG0 k hk)
    calc b k * (∫ ω, Real.sqrt (A ω * Dk k ω) ∂μ + ∫ ω, Real.sqrt (A ω * Gk k ω) ∂μ) ≤
        b k * (Real.sqrt (∫ ω, A ω ∂μ) * Real.sqrt (∫ ω, Dk k ω ∂μ) +
          Real.sqrt (∫ ω, A ω ∂μ) * Real.sqrt (∫ ω, Gk k ω ∂μ)) :=
          mul_le_mul_of_nonneg_left (add_le_add h1 h2) (hb k hk)
      _ = Real.sqrt (∫ ω, A ω ∂μ) * (b k *
          (Real.sqrt (∫ ω, Dk k ω ∂μ) + Real.sqrt (∫ ω, Gk k ω ∂μ))) := by ring
  -- pointwise domination including the bad event
  have hpt' : ∀ ω, S ω ≤ a * T ω + Z ω + Gᶜ.indicator S ω := by
    intro ω
    by_cases hω : ω ∈ G
    · have hn : ω ∉ Gᶜ := fun h => h hω
      rw [Set.indicator_of_notMem hn, add_zero, ← hTeq]
      exact hpt ω hω
    · rw [Set.indicator_of_mem (show ω ∈ Gᶜ from hω)]
      have : 0 ≤ a * T ω + Z ω := add_nonneg (mul_nonneg ha (hT0 ω)) (hZ0 ω)
      linarith
  have hind : Integrable (Gᶜ.indicator S) μ := hS.indicator hG.compl
  have hmain : Integrable (fun ω => a * T ω + Z ω) μ := (hTint.const_mul a).add hZ
  calc ∫ ω, S ω ∂μ ≤ ∫ ω, (a * T ω + Z ω + Gᶜ.indicator S ω) ∂μ :=
        integral_mono hS (hmain.add hind) hpt'
    _ = a * ∫ ω, T ω ∂μ + ∫ ω, Z ω ∂μ + ∫ ω in Gᶜ, S ω ∂μ := by
        rw [integral_add (f := fun ω => a * T ω + Z ω) hmain hind,
          integral_add (f := fun ω => a * T ω) (hTint.const_mul a) hZ,
          integral_const_mul, integral_indicator hG.compl]
    _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left hTle ha
        linarith

end GMCExplicitDelta.Localization
