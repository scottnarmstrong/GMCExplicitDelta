module

public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Reflected Fourier series on a box (cosine Parseval, mixed sine Bessel)

On the box `∏ᵢ [aᵢ, aᵢ + ℓ)` with normalized Lebesgue measure `boxMeasure a ℓ`, the reflection of a
function `φ` to the unit torus (even in every coordinate, odd in the coordinates of a finite set
`O`) has Fourier coefficients `(-i)^{|O|} ⨍ φ · boxMode a ℓ O n`, where
`boxMode a ℓ O n x = ∏ᵢ (sin or cos)(π nᵢ (xᵢ - aᵢ)/ℓ)` (sine exactly for `i ∈ O`).
Parseval on the torus (Mathlib's `UnitAddTorus.hasSum_sq_mFourierCoeff`) then gives

* `hasSum_sq_boxCoeff_cos`: `∑_{n ∈ ℤ^d} (⨍ φ ∏ cos)^2 = ⨍ φ²` (the cosine Parseval identity);
* `tsum_sq_boxCoeff_le`: `∑_{n ∈ ℤ^d} (⨍ φ · boxMode O n)^2 ≤ ⨍ φ²` for every `O`.

The torus and its Haar measure are internal to this file; the public statements only involve
`boxMeasure`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

namespace GMCExplicitDelta.Haar.Torus

noncomputable local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : (volume : Measure UnitAddCircle).Regular :=
  inferInstanceAs ((Measure.addHaarMeasure ⊤ : Measure UnitAddCircle).Regular)

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : (volume : Measure UnitAddCircle).IsNegInvariant :=
  Measure.IsAddHaarMeasure.isNegInvariant_of_regular _

/-! ### The representative in `(-1/2, 1/2]` -/

/-- The representative of a point of `ℝ/ℤ` in `(-1/2, 1/2]`. -/
def rep (s : UnitAddCircle) : ℝ := (AddCircle.equivIoc 1 (-(1 / 2 : ℝ)) s : ℝ)

theorem rep_mem (s : UnitAddCircle) : rep s ∈ Ioc (-(1 / 2 : ℝ)) (1 / 2) := by
  have h := (AddCircle.equivIoc 1 (-(1 / 2 : ℝ)) s).2
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  norm_num at h2
  exact h2

theorem coe_rep (s : UnitAddCircle) : ((rep s : ℝ) : UnitAddCircle) = s :=
  AddCircle.coe_equivIoc

theorem rep_coe {x : ℝ} (hx : x ∈ Ioc (-(1 / 2 : ℝ)) (1 / 2)) : rep (x : UnitAddCircle) = x := by
  unfold rep
  rw [AddCircle.equivIoc_coe_of_mem]
  refine ⟨hx.1, ?_⟩
  norm_num
  exact hx.2

theorem measurable_rep : Measurable rep :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIoc 1 (-(1 / 2 : ℝ))).measurable

theorem rep_neg_of_lt {s : UnitAddCircle} (h : rep s < 1 / 2) : rep (-s) = -rep s := by
  conv_lhs => rw [← coe_rep s, ← AddCircle.coe_neg]
  have hm := rep_mem s
  exact rep_coe ⟨by linarith, by linarith [hm.1]⟩

theorem rep_neg_of_eq {s : UnitAddCircle} (h : rep s = 1 / 2) : rep (-s) = 1 / 2 := by
  have hs : s = ((1 / 2 : ℝ) : UnitAddCircle) := by rw [← h, coe_rep]
  have hneg : -s = ((1 / 2 : ℝ) : UnitAddCircle) := by
    rw [hs, ← AddCircle.coe_neg]
    have e : (((-(1 / 2 : ℝ)) : ℝ) : UnitAddCircle) = ((-(1 / 2 : ℝ) + 1 : ℝ) : UnitAddCircle) :=
      (AddCircle.coe_add_period (p := (1 : ℝ)) _).symm
    rw [e]
    norm_num
  rw [hneg]
  exact rep_coe ⟨by norm_num, le_rfl⟩

theorem abs_rep_neg (s : UnitAddCircle) : |rep (-s)| = |rep s| := by
  rcases (rep_mem s).2.lt_or_eq with h | h
  · rw [rep_neg_of_lt h, abs_neg]
  · rw [rep_neg_of_eq h, h]

/-- Fourier characters in terms of the representative. -/
theorem fourier_eq (n : ℤ) (s : UnitAddCircle) :
    fourier n s = Complex.exp (2 * Real.pi * Complex.I * n * rep s) := by
  conv_lhs => rw [← coe_rep s]
  rw [fourier_coe_apply]
  simp

theorem fourier_neg_arg (n : ℤ) (s : UnitAddCircle) :
    fourier n (-s) = Complex.exp (-(2 * Real.pi * Complex.I * n * rep s)) := by
  conv_lhs => rw [← coe_rep s, ← AddCircle.coe_neg]
  rw [fourier_coe_apply]
  simp only [Complex.ofReal_neg, Complex.ofReal_one, div_one]
  ring_nf

/-! ### The odd sign -/

/-- The odd sign of `s`: `1` on `(0, 1/2)`, `-1` on `(-1/2, 0)`, `0` at `0` and `1/2`. -/
def oddSign (s : UnitAddCircle) : ℝ :=
  if 0 < rep s ∧ rep s < 1 / 2 then 1 else if rep s < 0 then -1 else 0

theorem measurable_oddSign : Measurable oddSign := by
  unfold oddSign
  refine Measurable.ite ?_ measurable_const (Measurable.ite ?_ measurable_const measurable_const)
  · exact (measurableSet_lt measurable_const measurable_rep).inter
      (measurableSet_lt measurable_rep measurable_const)
  · exact measurableSet_lt measurable_rep measurable_const

theorem oddSign_neg (s : UnitAddCircle) : oddSign (-s) = -oddSign s := by
  have hm := rep_mem s
  rcases hm.2.lt_or_eq with h | h
  · have hr := rep_neg_of_lt h
    have hm1 := hm.1
    unfold oddSign
    rw [hr]
    rcases lt_trichotomy (rep s) 0 with h0 | h0 | h0
    · rw [ite_eq_left (show 0 < -rep s ∧ -rep s < 1 / 2 from ⟨by linarith, by linarith⟩),
        ite_eq_right (show ¬(0 < rep s ∧ rep s < 1 / 2) from fun h' => by linarith [h'.1]),
        ite_eq_left h0]
      norm_num
    · rw [h0]
      norm_num
    · rw [ite_eq_right (show ¬(0 < -rep s ∧ -rep s < 1 / 2) from fun h' => by linarith [h'.1]),
        ite_eq_left (show -rep s < 0 by linarith), ite_eq_left (show 0 < rep s ∧ rep s < 1 / 2 from
          ⟨h0, h⟩)]
  · unfold oddSign
    rw [rep_neg_of_eq h, h]
    norm_num

theorem abs_oddSign_le (s : UnitAddCircle) : |oddSign s| ≤ 1 := by
  unfold oddSign
  split_ifs <;> norm_num

theorem oddSign_mul_sin (n : ℤ) (s : UnitAddCircle) :
    oddSign s * Real.sin (2 * Real.pi * n * rep s) =
      Real.sin (Real.pi * n * (2 * |rep s|)) := by
  have hm := rep_mem s
  unfold oddSign
  by_cases h1 : 0 < rep s ∧ rep s < 1 / 2
  · rw [ite_eq_left h1, abs_of_pos h1.1]
    ring_nf
  · rw [ite_eq_right h1]
    by_cases h2 : rep s < 0
    · rw [ite_eq_left h2, abs_of_neg h2,
        show Real.pi * n * (2 * -rep s) = -(2 * Real.pi * n * rep s) by ring, Real.sin_neg]
      ring
    · rw [ite_eq_right h2]
      have h3 : 0 ≤ rep s := not_lt.mp h2
      rcases h3.lt_or_eq with h4 | h4
      · have h5 : rep s = 1 / 2 := le_antisymm hm.2 (not_lt.mp fun h6 => h1 ⟨h4, h6⟩)
        rw [h5]
        have : Real.pi * n * (2 * |(1 / 2 : ℝ)|) = (n : ℝ) * Real.pi := by
          rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          ring
        rw [this, Real.sin_int_mul_pi]
        ring
      · rw [← h4]
        simp

theorem cos_rep_eq (n : ℤ) (s : UnitAddCircle) :
    Real.cos (2 * Real.pi * n * rep s) = Real.cos (Real.pi * n * (2 * |rep s|)) := by
  rcases abs_choice (rep s) with h | h
  · rw [h]
    ring_nf
  · rw [h, ← Real.cos_neg]
    ring_nf

/-- The two-point sum of a character over `±s`. -/
theorem fourier_add_fourier_neg (n : ℤ) (s : UnitAddCircle) :
    fourier (-n) s + fourier (-n) (-s) =
      2 * (Real.cos (Real.pi * n * (2 * |rep s|)) : ℂ) := by
  rw [fourier_eq, fourier_neg_arg, ← cos_rep_eq, Complex.ofReal_cos, Complex.two_cos]
  push_cast
  ring_nf

/-- The two-point odd difference of a character over `±s`, multiplied by the odd sign. -/
theorem oddSign_mul_fourier_sub (n : ℤ) (s : UnitAddCircle) :
    (oddSign s : ℂ) * (fourier (-n) s - fourier (-n) (-s)) =
      2 * (-Complex.I) * (Real.sin (Real.pi * n * (2 * |rep s|)) : ℂ) := by
  rw [fourier_eq, fourier_neg_arg, ← oddSign_mul_sin]
  set θ : ℝ := 2 * Real.pi * n * rep s with hθ
  have e1 : (2 * Real.pi * Complex.I * ((-n : ℤ) : ℂ) * (rep s : ℂ)) =
      -((θ : ℂ) * Complex.I) := by
    rw [hθ]
    push_cast
    ring
  rw [e1, neg_neg, ← neg_mul]
  have h2 : Complex.exp (-(θ : ℂ) * Complex.I) - Complex.exp ((θ : ℂ) * Complex.I) =
      -Complex.I * (2 * Complex.sin θ) := by
    have := Complex.two_sin (θ : ℂ)
    linear_combination Complex.I * this +
      (Complex.exp (-(θ : ℂ) * Complex.I) - Complex.exp ((θ : ℂ) * Complex.I)) * Complex.I_sq
  rw [h2]
  push_cast
  ring

/-! ### The tent map and the box measure -/

/-- The tent map `s ↦ a + 2ℓ|s|` from `ℝ/ℤ` onto `[a, a + ℓ]`. -/
def tent (a ℓ : ℝ) (s : UnitAddCircle) : ℝ := a + 2 * ℓ * |rep s|

theorem measurable_tent (a ℓ : ℝ) : Measurable (tent a ℓ) := by
  unfold tent
  exact measurable_const.add (measurable_const.mul (continuous_abs.measurable.comp measurable_rep))

theorem tent_neg (a ℓ : ℝ) (s : UnitAddCircle) : tent a ℓ (-s) = tent a ℓ s := by
  simp only [tent, abs_rep_neg]

/-- The pushforward of Lebesgue measure on `(-1/2, 1/2]` under `x ↦ a + 2ℓ|x|`. -/
theorem map_abs_restrict_Ioc {a ℓ : ℝ} (hℓ : 0 < ℓ) :
    Measure.map (fun x : ℝ => a + 2 * ℓ * |x|) (volume.restrict (Ioc (-(1 / 2 : ℝ)) (1 / 2))) =
      ENNReal.ofReal ℓ⁻¹ • volume.restrict (Ico a (a + ℓ)) := by
  have hmeas : Measurable (fun x : ℝ => a + 2 * ℓ * |x|) := by fun_prop
  have : IsFiniteMeasure (volume.restrict (Ioc (-(1 / 2 : ℝ)) (1 / 2))) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  refine Measure.ext_of_Iic _ _ fun y => ?_
  rw [Measure.map_apply hmeas measurableSet_Iic, Measure.restrict_apply (hmeas measurableSet_Iic),
    Measure.smul_apply, Measure.restrict_apply measurableSet_Iic, smul_eq_mul]
  set c := (y - a) / (2 * ℓ) with hc
  have hpre : (fun x : ℝ => a + 2 * ℓ * |x|) ⁻¹' Iic y = Icc (-c) c := by
    ext x
    simp only [mem_preimage, mem_Iic, mem_Icc, hc]
    rw [← abs_le, le_div_iff₀ (by positivity)]
    constructor <;> intro h <;> linarith
  rw [hpre]
  rcases lt_or_ge y a with hy | hy
  · have h1 : Icc (-c) c = ∅ := Icc_eq_empty (by
      have : c < 0 := div_neg_of_neg_of_pos (by linarith) (by positivity)
      linarith)
    have h2 : Iic y ∩ Ico a (a + ℓ) = ∅ := by
      ext x; simp only [mem_inter_iff, mem_Iic, mem_Ico, mem_empty_iff_false, iff_false]
      intro h; linarith [h.1, h.2.1]
    simp [h1, h2]
  rcases lt_or_ge y (a + ℓ) with hy2 | hy2
  · have hc0 : 0 ≤ c := div_nonneg (by linarith) (by positivity)
    have hc1 : c < 1 / 2 := by
      rw [hc, div_lt_iff₀ (by positivity)]
      linarith
    have h1 : Icc (-c) c ∩ Ioc (-(1 / 2 : ℝ)) (1 / 2) = Icc (-c) c := by
      apply inter_eq_left.2
      intro x hx
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have h2 : Iic y ∩ Ico a (a + ℓ) = Icc a y := by
      ext x; simp only [mem_inter_iff, mem_Iic, mem_Ico, mem_Icc]
      constructor
      · intro h; exact ⟨h.2.1, h.1⟩
      · intro h; exact ⟨h.2, h.1, by linarith [h.2]⟩
    rw [h1, h2, Real.volume_Icc, Real.volume_Icc, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [hc]
    field_simp
    ring
  · have hc1 : 1 / 2 ≤ c := by
      rw [hc, le_div_iff₀ (by positivity)]
      linarith
    have h1 : Icc (-c) c ∩ Ioc (-(1 / 2 : ℝ)) (1 / 2) = Ioc (-(1 / 2 : ℝ)) (1 / 2) := by
      apply inter_eq_right.2
      intro x hx
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have h2 : Iic y ∩ Ico a (a + ℓ) = Ico a (a + ℓ) := by
      apply inter_eq_right.2
      intro x hx
      simp only [mem_Iic]
      linarith [hx.2]
    rw [h1, h2, Real.volume_Ioc, Real.volume_Ico, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
    ring

/-- The Haar measure of `ℝ/ℤ` is the image of Lebesgue measure on `(-1/2, 1/2]`. -/
theorem map_coe_restrict_Ioc :
    Measure.map ((↑) : ℝ → UnitAddCircle) (volume.restrict (Ioc (-(1 / 2 : ℝ)) (1 / 2))) =
      (volume : Measure UnitAddCircle) := by
  have h := (UnitAddCircle.measurePreserving_mk (-(1 / 2 : ℝ))).map_eq
  rw [AddCircle.volume_eq_smul_haarAddCircle] at h
  norm_num at h
  exact h

/-- The tent map pushes the Haar measure of `ℝ/ℤ` to normalized Lebesgue measure on
`[a, a + ℓ)`. -/
theorem map_tent {a ℓ : ℝ} (hℓ : 0 < ℓ) :
    Measure.map (tent a ℓ) (volume : Measure UnitAddCircle) =
      ENNReal.ofReal ℓ⁻¹ • volume.restrict (Ico a (a + ℓ)) := by
  rw [← map_coe_restrict_Ioc, Measure.map_map (measurable_tent a ℓ) AddCircle.measurable_mk',
    ← map_abs_restrict_Ioc hℓ]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  simp only [Function.comp_apply, tent, rep_coe hx]

/-! ### The box measure and the box map -/

variable {d : ℕ}

instance isFiniteMeasure_smul_restrict_Ico (a ℓ : ℝ) :
    IsFiniteMeasure (ENNReal.ofReal ℓ⁻¹ • volume.restrict (Ico a (a + ℓ))) :=
  ⟨by
    rw [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_Ico_lt_top⟩

/-- Normalized Lebesgue measure on the box `∏ᵢ [aᵢ, aᵢ + ℓ)`. -/
def boxMeasure (a : Fin d → ℝ) (ℓ : ℝ) : Measure (Fin d → ℝ) :=
  Measure.pi fun i => ENNReal.ofReal ℓ⁻¹ • volume.restrict (Ico (a i) (a i + ℓ))

/-- The coordinatewise tent map from the torus onto the box. -/
def boxMap (a : Fin d → ℝ) (ℓ : ℝ) (t : UnitAddTorus (Fin d)) : Fin d → ℝ :=
  fun i => tent (a i) ℓ (t i)

theorem measurePreserving_boxMap (a : Fin d → ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    MeasurePreserving (boxMap a ℓ) (volume : Measure (UnitAddTorus (Fin d)))
      (boxMeasure a ℓ) :=
  measurePreserving_pi (fun _ : Fin d => (volume : Measure UnitAddCircle))
    (fun i => ENNReal.ofReal ℓ⁻¹ • volume.restrict (Ico (a i) (a i + ℓ)))
    (f := fun i => tent (a i) ℓ) (fun _ => ⟨measurable_tent _ _, map_tent hℓ⟩)

theorem integral_boxMap (a : Fin d → ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) {f : (Fin d → ℝ) → ℝ}
    (hf : AEStronglyMeasurable f (boxMeasure a ℓ)) :
    ∫ t, f (boxMap a ℓ t) = ∫ x, f x ∂boxMeasure a ℓ := by
  have hmp := measurePreserving_boxMap a hℓ
  rw [← hmp.map_eq] at hf ⊢
  exact (integral_map hmp.measurable.aemeasurable hf).symm

/-- The box modes `∏ᵢ (sin or cos)(π nᵢ (xᵢ - aᵢ)/ℓ)`, with a sine exactly in the coordinates
of `O`. -/
def boxMode (a : Fin d → ℝ) (ℓ : ℝ) (O : Finset (Fin d)) (n : Fin d → ℤ) (x : Fin d → ℝ) : ℝ :=
  ∏ i, if i ∈ O then Real.sin (Real.pi * n i * (x i - a i) / ℓ)
    else Real.cos (Real.pi * n i * (x i - a i) / ℓ)

theorem continuous_boxMode (a : Fin d → ℝ) (ℓ : ℝ) (O : Finset (Fin d)) (n : Fin d → ℤ) :
    Continuous (boxMode a ℓ O n) := by
  show Continuous (fun x : Fin d → ℝ => ∏ i, if i ∈ O then
    Real.sin (Real.pi * n i * (x i - a i) / ℓ) else Real.cos (Real.pi * n i * (x i - a i) / ℓ))
  refine continuous_finsetProd _ fun i _ => ?_
  by_cases hi : i ∈ O
  · simp only [hi, ite_true]
    fun_prop
  · simp only [hi, ite_false]
    fun_prop

theorem abs_boxMode_le (a : Fin d → ℝ) (ℓ : ℝ) (O : Finset (Fin d)) (n : Fin d → ℤ)
    (x : Fin d → ℝ) : |boxMode a ℓ O n x| ≤ 1 := by
  unfold boxMode
  rw [Finset.abs_prod]
  refine Finset.prod_le_one₀ (fun i _ => abs_nonneg _) fun i _ => ?_
  split_ifs
  · exact Real.abs_sin_le_one _
  · exact Real.abs_cos_le_one _

theorem boxMode_boxMap (a : Fin d → ℝ) {ℓ : ℝ} (hℓ : ℓ ≠ 0) (O : Finset (Fin d))
    (n : Fin d → ℤ) (t : UnitAddTorus (Fin d)) :
    boxMode a ℓ O n (boxMap a ℓ t) =
      ∏ i, if i ∈ O then Real.sin (Real.pi * n i * (2 * |rep (t i)|))
        else Real.cos (Real.pi * n i * (2 * |rep (t i)|)) := by
  unfold boxMode boxMap tent
  refine Finset.prod_congr rfl fun i _ => ?_
  have : Real.pi * n i * (a i + 2 * ℓ * |rep (t i)| - a i) / ℓ =
      Real.pi * n i * (2 * |rep (t i)|) := by
    field_simp
    ring
  rw [this]

/-! ### Coordinate reflections of the torus -/

/-- Reflection of the coordinates in `s`. -/
def flip (s : Finset (Fin d)) (t : UnitAddTorus (Fin d)) : UnitAddTorus (Fin d) :=
  fun i => if i ∈ s then -t i else t i

theorem flip_flip (s : Finset (Fin d)) (t : UnitAddTorus (Fin d)) : flip s (flip s t) = t := by
  funext i
  unfold flip
  split_ifs <;> simp

theorem measurable_flip (s : Finset (Fin d)) : Measurable (flip s) := by
  refine measurable_pi_iff.2 fun i => ?_
  unfold flip
  by_cases hi : i ∈ s
  · simp only [hi, ite_true]
    exact (measurable_pi_apply i).neg
  · simp only [hi, ite_false]
    exact measurable_pi_apply i

/-- `flip s` as a measurable equivalence. -/
def flipEquiv (s : Finset (Fin d)) : UnitAddTorus (Fin d) ≃ᵐ UnitAddTorus (Fin d) where
  toFun := flip s
  invFun := flip s
  left_inv := flip_flip s
  right_inv := flip_flip s
  measurable_toFun := measurable_flip s
  measurable_invFun := measurable_flip s

theorem measurePreserving_flip (s : Finset (Fin d)) :
    MeasurePreserving (flipEquiv s) (volume : Measure (UnitAddTorus (Fin d))) volume := by
  have h := measurePreserving_pi (fun _ : Fin d => (volume : Measure UnitAddCircle))
    (fun _ => volume)
    (f := fun i => if i ∈ s then (Neg.neg : UnitAddCircle → UnitAddCircle) else id)
    (fun i => by
      split_ifs
      · exact Measure.measurePreserving_neg _
      · exact MeasurePreserving.id _)
  convert h using 1
  funext t i
  change flip s t i = _
  unfold flip
  split_ifs <;> rfl

theorem boxMap_flip (a : Fin d → ℝ) (ℓ : ℝ) (s : Finset (Fin d)) (t : UnitAddTorus (Fin d)) :
    boxMap a ℓ (flip s t) = boxMap a ℓ t := by
  funext i
  unfold boxMap flip
  split_ifs
  · exact tent_neg _ _ _
  · rfl

/-! ### The reflected function and its Fourier coefficients -/

/-- The reflection of `φ` to the torus, odd in the coordinates of `O`. -/
def reflect (a : Fin d → ℝ) (ℓ : ℝ) (O : Finset (Fin d)) (φ : (Fin d → ℝ) → ℝ)
    (t : UnitAddTorus (Fin d)) : ℂ :=
  (((∏ i ∈ O, oddSign (t i)) * φ (boxMap a ℓ t) : ℝ) : ℂ)

theorem abs_prod_oddSign_le (O : Finset (Fin d)) (t : UnitAddTorus (Fin d)) :
    |∏ i ∈ O, oddSign (t i)| ≤ 1 := by
  rw [Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun i _ => abs_nonneg _) fun i _ => abs_oddSign_le _

theorem measurable_prod_oddSign (O : Finset (Fin d)) :
    Measurable fun t : UnitAddTorus (Fin d) => ∏ i ∈ O, oddSign (t i) :=
  Finset.measurable_prod O fun i _ => measurable_oddSign.comp (measurable_pi_apply i)

theorem memLp_reflect_re (a : Fin d → ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) (O : Finset (Fin d))
    {φ : (Fin d → ℝ) → ℝ} (hφ : MemLp φ 2 (boxMeasure a ℓ)) :
    MemLp (fun t => (∏ i ∈ O, oddSign (t i)) * φ (boxMap a ℓ t))
      2 (volume : Measure (UnitAddTorus (Fin d))) := by
  have hc : MemLp (fun t => φ (boxMap a ℓ t)) 2 (volume : Measure (UnitAddTorus (Fin d))) :=
    hφ.comp_measurePreserving (measurePreserving_boxMap a hℓ)
  refine hc.of_le ((measurable_prod_oddSign O).aestronglyMeasurable.mul hc.aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun t => ?_
  simp only [Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) (abs_prod_oddSign_le O t)

theorem memLp_reflect (a : Fin d → ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) (O : Finset (Fin d))
    {φ : (Fin d → ℝ) → ℝ} (hφ : MemLp φ 2 (boxMeasure a ℓ)) :
    MemLp (reflect a ℓ O φ) 2 (volume : Measure (UnitAddTorus (Fin d))) :=
  (memLp_reflect_re a hℓ O hφ).ofReal

/-- The symmetrized character: summing `mFourier (-n) • reflect` over all coordinate
reflections. -/
theorem sum_flip_mFourier_smul_reflect (a : Fin d → ℝ) {ℓ : ℝ} (hℓ : ℓ ≠ 0)
    (O : Finset (Fin d)) (φ : (Fin d → ℝ) → ℝ) (n : Fin d → ℤ) (t : UnitAddTorus (Fin d)) :
    ∑ s ∈ (Finset.univ : Finset (Fin d)).powerset,
        UnitAddTorus.mFourier (-n) (flip s t) • reflect a ℓ O φ (flip s t) =
      2 ^ d * (-Complex.I) ^ O.card *
        ((boxMode a ℓ O n (boxMap a ℓ t) * φ (boxMap a ℓ t) : ℝ) : ℂ) := by
  classical
  set σ : Fin d → ℂ := fun i => (oddSign (t i) : ℂ) with hσ
  set P : Fin d → ℂ := fun i =>
    fourier (-n i) (-t i) * (if i ∈ O then -σ i else 1) with hP
  set Qf : Fin d → ℂ := fun i => fourier (-n i) (t i) * (if i ∈ O then σ i else 1) with hQ
  have hterm : ∀ s ∈ (Finset.univ : Finset (Fin d)).powerset,
      UnitAddTorus.mFourier (-n) (flip s t) • reflect a ℓ O φ (flip s t) =
        ((∏ i ∈ s, P i) * ∏ i ∈ Finset.univ \ s, Qf i) * (φ (boxMap a ℓ t) : ℂ) := by
    intro s _
    have hL : UnitAddTorus.mFourier (-n) (flip s t) • reflect a ℓ O φ (flip s t) =
        (∏ i, fourier ((-n) i) (flip s t i) *
          (if i ∈ O then (oddSign (flip s t i) : ℂ) else 1)) * (φ (boxMap a ℓ t) : ℂ) := by
      rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter]
      simp only [reflect, boxMap_flip, smul_eq_mul, UnitAddTorus.mFourier, ContinuousMap.coe_mk]
      push_cast
      ring
    have h1 : ∀ i, fourier ((-n) i) (flip s t i) *
        (if i ∈ O then (oddSign (flip s t i) : ℂ) else 1) = if i ∈ s then P i else Qf i := by
      intro i
      by_cases hs : i ∈ s
      · have hf : flip s t i = -t i := by simp [flip, hs]
        rw [hf, ite_eq_left hs, hP, Pi.neg_apply]
        by_cases hO : i ∈ O
        · simp only [hσ, hO, ite_true, oddSign_neg, Complex.ofReal_neg, mul_neg]
        · simp only [hO, ite_false]
      · have hf : flip s t i = t i := by simp [flip, hs]
        rw [hf, ite_eq_right hs, hQ, Pi.neg_apply]
    have h2 : (∏ i, if i ∈ s then P i else Qf i) =
        (∏ i ∈ s, P i) * ∏ i ∈ Finset.univ \ s, Qf i := by
      rw [Finset.prod_ite]
      congr 1
      · congr 1
        ext i
        simp
      · congr 1
        ext i
        simp
    rw [hL, Finset.prod_congr rfl (fun i _ => h1 i), h2]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← Finset.prod_add]
  have hPQ : ∀ i, P i + Qf i = 2 * (if i ∈ O then -Complex.I *
      (Real.sin (Real.pi * n i * (2 * |rep (t i)|)) : ℂ)
      else (Real.cos (Real.pi * n i * (2 * |rep (t i)|)) : ℂ)) := by
    intro i
    by_cases hO : i ∈ O
    · simp only [hP, hQ, hσ, hO, ite_true]
      rw [show fourier (-n i) (-t i) * -(oddSign (t i) : ℂ) +
          fourier (-n i) (t i) * (oddSign (t i) : ℂ) =
          (oddSign (t i) : ℂ) * (fourier (-n i) (t i) - fourier (-n i) (-t i)) by ring,
        oddSign_mul_fourier_sub]
      ring
    · simp only [hP, hQ, hO, ite_false, mul_one]
      rw [add_comm, fourier_add_fourier_neg]
  simp only [hPQ, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  have h3 : (∏ i, if i ∈ O then -Complex.I *
      (Real.sin (Real.pi * n i * (2 * |rep (t i)|)) : ℂ)
      else (Real.cos (Real.pi * n i * (2 * |rep (t i)|)) : ℂ)) =
      (-Complex.I) ^ O.card * ((boxMode a ℓ O n (boxMap a ℓ t) : ℝ) : ℂ) := by
    rw [boxMode_boxMap a hℓ, Complex.ofReal_prod]
    have : ∀ i, (if i ∈ O then -Complex.I *
        (Real.sin (Real.pi * n i * (2 * |rep (t i)|)) : ℂ)
        else (Real.cos (Real.pi * n i * (2 * |rep (t i)|)) : ℂ)) =
        (if i ∈ O then -Complex.I else 1) *
          (((if i ∈ O then Real.sin (Real.pi * n i * (2 * |rep (t i)|))
            else Real.cos (Real.pi * n i * (2 * |rep (t i)|)) : ℝ) : ℂ)) := by
      intro i
      split_ifs <;> simp
    simp only [this, Finset.prod_mul_distrib]
    rw [Finset.prod_ite_mem Finset.univ O, Finset.univ_inter, Finset.prod_const]
  rw [h3]
  push_cast
  ring

theorem integrable_mFourier_smul_reflect (a : Fin d → ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (O : Finset (Fin d)) {φ : (Fin d → ℝ) → ℝ} (hφ : MemLp φ 2 (boxMeasure a ℓ))
    (n : Fin d → ℤ) :
    Integrable (fun t => UnitAddTorus.mFourier (-n) t • reflect a ℓ O φ t)
      (volume : Measure (UnitAddTorus (Fin d))) := by
  have hR := (memLp_reflect a hℓ O hφ).integrable one_le_two
  refine hR.bdd_mul (c := ‖UnitAddTorus.mFourier (-n)‖)
    (UnitAddTorus.mFourier (-n)).continuous.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun t => ContinuousMap.norm_coe_le_norm _ t

/-- The Fourier coefficients of the reflected function. -/
theorem mFourierCoeff_reflect (a : Fin d → ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) (O : Finset (Fin d))
    {φ : (Fin d → ℝ) → ℝ} (hφ : MemLp φ 2 (boxMeasure a ℓ)) (n : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff (reflect a ℓ O φ) n =
      (-Complex.I) ^ O.card * ((∫ x, boxMode a ℓ O n x * φ x ∂boxMeasure a ℓ : ℝ) : ℂ) := by
  classical
  set H : UnitAddTorus (Fin d) → ℂ := fun t => UnitAddTorus.mFourier (-n) t • reflect a ℓ O φ t
  have hH : Integrable H volume := integrable_mFourier_smul_reflect a hℓ O hφ n
  have hflip : ∀ s : Finset (Fin d), ∫ t, H (flip s t) = ∫ t, H t := fun s =>
    (measurePreserving_flip s).integral_comp' H
  have hflipInt : ∀ s : Finset (Fin d), Integrable (fun t => H (flip s t)) volume := fun s =>
    ((measurePreserving_flip s).integrable_comp_emb (flipEquiv s).measurableEmbedding).2 hH
  have hsum : ∫ t, ∑ s ∈ (Finset.univ : Finset (Fin d)).powerset, H (flip s t) =
      (2 : ℂ) ^ d * ∫ t, H t := by
    rw [integral_finsetSum _ fun s _ => hflipInt s, Finset.sum_congr rfl fun s _ => hflip s,
      Finset.sum_const, Finset.card_powerset, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_pow, Nat.cast_ofNat]
  have hpt : ∀ t, ∑ s ∈ (Finset.univ : Finset (Fin d)).powerset, H (flip s t) =
      2 ^ d * (-Complex.I) ^ O.card *
        ((boxMode a ℓ O n (boxMap a ℓ t) * φ (boxMap a ℓ t) : ℝ) : ℂ) :=
    sum_flip_mFourier_smul_reflect a hℓ.ne' O φ n
  have hmap : ∫ t, ((boxMode a ℓ O n (boxMap a ℓ t) * φ (boxMap a ℓ t) : ℝ) : ℂ) =
      ((∫ x, boxMode a ℓ O n x * φ x ∂boxMeasure a ℓ : ℝ) : ℂ) := by
    rw [integral_complex_ofReal, integral_boxMap a hℓ
      (f := fun x => boxMode a ℓ O n x * φ x)
      ((continuous_boxMode a ℓ O n).aestronglyMeasurable.mul hφ.aestronglyMeasurable)]
  have key : (2 : ℂ) ^ d * ∫ t, H t =
      (2 : ℂ) ^ d * ((-Complex.I) ^ O.card *
        ((∫ x, boxMode a ℓ O n x * φ x ∂boxMeasure a ℓ : ℝ) : ℂ)) := by
    rw [← hsum, integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul, hmap]
    ring
  have h2 : (2 : ℂ) ^ d ≠ 0 := pow_ne_zero _ two_ne_zero
  exact mul_left_cancel₀ h2 key

/-! ### Parseval for reflected functions -/

theorem hasSum_sq_boxCoeff (a : Fin d → ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) (O : Finset (Fin d))
    {φ : (Fin d → ℝ) → ℝ} (hφ : MemLp φ 2 (boxMeasure a ℓ)) :
    HasSum (fun n : Fin d → ℤ => (∫ x, boxMode a ℓ O n x * φ x ∂boxMeasure a ℓ) ^ 2)
      (∫ t, ((∏ i ∈ O, oddSign (t i)) * φ (boxMap a ℓ t)) ^ 2) := by
  have hR := memLp_reflect a hℓ O hφ
  have h := UnitAddTorus.hasSum_sq_mFourierCoeff (hR.toLp (reflect a ℓ O φ))
  have hcoef : ∀ n, UnitAddTorus.mFourierCoeff (⇑(hR.toLp (reflect a ℓ O φ))) n =
      UnitAddTorus.mFourierCoeff (reflect a ℓ O φ) n := by
    intro n
    unfold UnitAddTorus.mFourierCoeff
    refine integral_congr_ae ?_
    filter_upwards [hR.coeFn_toLp] with t ht
    rw [ht]
  have hnorm : ∫ t, ‖(hR.toLp (reflect a ℓ O φ)) t‖ ^ 2 =
      ∫ t, ((∏ i ∈ O, oddSign (t i)) * φ (boxMap a ℓ t)) ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [hR.coeFn_toLp] with t ht
    rw [ht, reflect, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hnorm] at h
  refine h.congr_fun fun n => ?_
  rw [hcoef, mFourierCoeff_reflect a hℓ O hφ n, norm_mul, norm_pow, norm_neg, Complex.norm_I,
    one_pow, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **Cosine Parseval identity** on the box. -/
theorem hasSum_sq_boxCoeff_cos (a : Fin d → ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {φ : (Fin d → ℝ) → ℝ} (hφ : MemLp φ 2 (boxMeasure a ℓ)) :
    HasSum (fun n : Fin d → ℤ => (∫ x, boxMode a ℓ ∅ n x * φ x ∂boxMeasure a ℓ) ^ 2)
      (∫ x, φ x ^ 2 ∂boxMeasure a ℓ) := by
  have h := hasSum_sq_boxCoeff a hℓ ∅ hφ
  simp only [Finset.prod_empty, one_mul] at h
  convert h using 1
  exact (integral_boxMap a hℓ (f := fun x => φ x ^ 2) (hφ.aestronglyMeasurable.pow 2)).symm

/-- **Bessel inequality** for the mixed modes on the box. -/
theorem summable_sq_boxCoeff (a : Fin d → ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) (O : Finset (Fin d))
    {φ : (Fin d → ℝ) → ℝ} (hφ : MemLp φ 2 (boxMeasure a ℓ)) :
    Summable (fun n : Fin d → ℤ => (∫ x, boxMode a ℓ O n x * φ x ∂boxMeasure a ℓ) ^ 2) :=
  (hasSum_sq_boxCoeff a hℓ O hφ).summable

theorem tsum_sq_boxCoeff_le (a : Fin d → ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) (O : Finset (Fin d))
    {φ : (Fin d → ℝ) → ℝ} (hφ : MemLp φ 2 (boxMeasure a ℓ)) :
    ∑' n : Fin d → ℤ, (∫ x, boxMode a ℓ O n x * φ x ∂boxMeasure a ℓ) ^ 2 ≤
      ∫ x, φ x ^ 2 ∂boxMeasure a ℓ := by
  rw [(hasSum_sq_boxCoeff a hℓ O hφ).tsum_eq]
  have hc : MemLp (fun t => φ (boxMap a ℓ t)) 2 (volume : Measure (UnitAddTorus (Fin d))) :=
    hφ.comp_measurePreserving (measurePreserving_boxMap a hℓ)
  have hrhs : ∫ x, φ x ^ 2 ∂boxMeasure a ℓ = ∫ t, φ (boxMap a ℓ t) ^ 2 :=
    (integral_boxMap a hℓ (f := fun x => φ x ^ 2) (hφ.aestronglyMeasurable.pow 2)).symm
  rw [hrhs]
  refine integral_mono (memLp_reflect_re a hℓ O hφ).integrable_sq hc.integrable_sq fun t => ?_
  rw [mul_pow]
  have h1 : (∏ i ∈ O, oddSign (t i)) ^ 2 ≤ 1 := by
    rw [← sq_abs]
    exact pow_le_one₀ (abs_nonneg _) (abs_prod_oddSign_le O t)
  exact mul_le_of_le_one_left (sq_nonneg _) h1

end GMCExplicitDelta.Haar.Torus
