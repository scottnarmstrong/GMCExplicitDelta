module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Jensen without conditional expectation, by truncation

If a convex `C¹` function `φ` is truncated by its tangent line at `N`, the resulting `ψ_N`
has a bounded measurable subgradient, so a centering identity `E[h(X,Y) Z] = 0` for bounded
measurable `h` gives `E ψ_N(m + K|Y-X|) ≤ E ψ_N(m + K|Y-X-rZ|)`.  Fatou's lemma then removes
the truncation.
-/

@[expose] public section

namespace GMCExplicitDelta.Source

open MeasureTheory

section Trunc

variable {φ φ' : ℝ → ℝ}

theorem tangent_le (hc : ConvexOn ℝ Set.univ φ) (hd : ∀ x, HasDerivAt φ (φ' x) x) (x y : ℝ) :
    φ x + φ' x * (y - x) ≤ φ y := by
  rcases lt_trichotomy x y with h | h | h
  · have := hc.le_slope_of_hasDerivAt (Set.mem_univ x) (Set.mem_univ y) h (hd x)
    rw [slope_def_field, le_div_iff₀ (sub_pos.2 h)] at this
    linarith
  · subst h; simp
  · have := hc.slope_le_of_hasDerivAt (Set.mem_univ y) (Set.mem_univ x) h (hd x)
    rw [slope_def_field, div_le_iff₀ (sub_pos.2 h)] at this
    linarith

theorem deriv_mono_of_convex (hc : ConvexOn ℝ Set.univ φ) (hd : ∀ x, HasDerivAt φ (φ' x) x) :
    Monotone φ' := by
  intro x y hxy
  rcases eq_or_lt_of_le hxy with rfl | h
  · exact le_rfl
  · exact (hc.le_slope_of_hasDerivAt (Set.mem_univ x) (Set.mem_univ y) h (hd x)).trans
      (hc.slope_le_of_hasDerivAt (Set.mem_univ x) (Set.mem_univ y) h (hd y))

/-- Truncation of `φ` by its tangent line at `N`. -/
noncomputable def truncFn (φ φ' : ℝ → ℝ) (N t : ℝ) : ℝ :=
  φ (min t N) + φ' N * max (t - N) 0

theorem truncFn_of_le {N t : ℝ} (h : t ≤ N) : truncFn φ φ' N t = φ t := by
  simp [truncFn, min_eq_left h, max_eq_right (sub_nonpos.2 h)]

theorem truncFn_of_ge {N t : ℝ} (h : N ≤ t) :
    truncFn φ φ' N t = φ N + φ' N * (t - N) := by
  simp [truncFn, min_eq_right h, max_eq_left (sub_nonneg.2 h)]

theorem truncFn_le (hc : ConvexOn ℝ Set.univ φ) (hd : ∀ x, HasDerivAt φ (φ' x) x) (N t : ℝ) :
    truncFn φ φ' N t ≤ φ t := by
  rcases le_total t N with h | h
  · rw [truncFn_of_le h]
  · rw [truncFn_of_ge h]; exact tangent_le hc hd N t

theorem continuous_truncFn (hφ : Continuous φ) (N : ℝ) : Continuous (truncFn φ φ' N) := by
  unfold truncFn; fun_prop

theorem truncFn_tangent (hc : ConvexOn ℝ Set.univ φ) (hd : ∀ x, HasDerivAt φ (φ' x) x)
    (N t0 t : ℝ) :
    truncFn φ φ' N t0 + φ' (min t0 N) * (t - t0) ≤ truncFn φ φ' N t := by
  have hm := deriv_mono_of_convex hc hd
  rcases le_total t0 N with h0 | h0
  · rw [truncFn_of_le h0, min_eq_left h0]
    rcases le_total t N with h | h
    · rw [truncFn_of_le h]; exact tangent_le hc hd t0 t
    · rw [truncFn_of_ge h]
      have h1 := tangent_le hc hd t0 N
      have h2 := hm h0
      nlinarith [mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h)]
  · rw [truncFn_of_ge h0, min_eq_right h0]
    rcases le_total t N with h | h
    · rw [truncFn_of_le h]
      have := tangent_le hc hd N t
      linarith
    · rw [truncFn_of_ge h]; linarith

theorem truncFn_nonneg (hφ0 : ∀ t, 0 ≤ φ t) (hφ'0 : ∀ t, 0 ≤ t → 0 ≤ φ' t) {N : ℝ}
    (hN : 0 ≤ N) (t : ℝ) : 0 ≤ truncFn φ φ' N t :=
  add_nonneg (hφ0 _) (mul_nonneg (hφ'0 N hN) (le_max_right _ _))

theorem truncFn_mono (hmono : MonotoneOn φ (Set.Ici 0)) (hφ'0 : ∀ t, 0 ≤ t → 0 ≤ φ' t) {N : ℝ}
    (hN : 0 ≤ N) {t w : ℝ} (ht : 0 ≤ t) (htw : t ≤ w) :
    truncFn φ φ' N t ≤ truncFn φ φ' N w := by
  unfold truncFn
  have h1 : φ (min t N) ≤ φ (min w N) :=
    hmono (le_min ht hN) (le_min (ht.trans htw) hN) (min_le_min htw le_rfl)
  have h2 : max (t - N) 0 ≤ max (w - N) 0 := max_le_max (by linarith) le_rfl
  have := mul_le_mul_of_nonneg_left h2 (hφ'0 N hN)
  linarith

theorem truncFn_le_lin (hmono : MonotoneOn φ (Set.Ici 0)) (hφ'0 : ∀ t, 0 ≤ t → 0 ≤ φ' t)
    {N : ℝ} (hN : 0 ≤ N) {t : ℝ} (ht : 0 ≤ t) :
    truncFn φ φ' N t ≤ φ N + φ' N * t := by
  unfold truncFn
  have h1 : φ (min t N) ≤ φ N := hmono (le_min ht hN) hN (min_le_right _ _)
  have h2 : max (t - N) 0 ≤ t := max_le (by linarith) ht
  have := mul_le_mul_of_nonneg_left h2 (hφ'0 N hN)
  linarith

end Trunc

/-- A sign function, measurable. -/
noncomputable def sgn (a : ℝ) : ℝ := if 0 < a then 1 else if a < 0 then -1 else 0

theorem measurable_sgn : Measurable sgn :=
  Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
    (Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
      measurable_const)

theorem abs_sgn_le (a : ℝ) : |sgn a| ≤ 1 := by
  unfold sgn; split_ifs <;> simp

/-- `|Δ - ρ| - |Δ| ≥ -sgn(Δ) ρ`. -/
theorem abs_sub_ge_sgn (Δ ρ : ℝ) : -(sgn Δ * ρ) ≤ |Δ - ρ| - |Δ| := by
  unfold sgn
  rcases lt_trichotomy Δ 0 with h | h | h
  · have h1 : ¬ (0 < Δ) := not_lt.2 h.le
    simp only [h1, ite_false, h, ite_true]
    have := neg_le_abs (Δ - ρ)
    rw [abs_of_neg h]; linarith
  · subst h; simp
  · simp only [h, ite_true]
    have := le_abs_self (Δ - ρ)
    rw [abs_of_pos h]; linarith

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {φ φ' : ℝ → ℝ}

/-- Jensen's inequality for the endpoint strip, in lintegral form. -/
theorem jensen_trunc (hc : ConvexOn ℝ Set.univ φ) (hd : ∀ x, HasDerivAt φ (φ' x) x)
    (hφ0 : ∀ t, 0 ≤ φ t) (hmono : MonotoneOn φ (Set.Ici 0))
    (hφ'0 : ∀ t, 0 ≤ t → 0 ≤ φ' t)
    {X Y Z w : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hXi : Integrable X μ) (hYi : Integrable Y μ) (hZi : Integrable Z μ)
    {K r : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r)
    (hcenter : ∀ h : ℝ → ℝ → ℝ, Measurable (Function.uncurry h) →
      (∃ C, ∀ x y, |h x y| ≤ C) → ∫ ω, h (X ω) (Y ω) * Z ω ∂μ = 0)
    (hw : ∀ ω, max |X ω| |Y ω| + K * |(Y ω - X ω) - r * Z ω| ≤ w ω) :
    ∫⁻ ω, ENNReal.ofReal (φ (max |X ω| |Y ω| + K * |Y ω - X ω|)) ∂μ ≤
      ∫⁻ ω, ENNReal.ofReal (φ (w ω)) ∂μ := by
  set T : Ω → ℝ := fun ω => max |X ω| |Y ω| + K * |Y ω - X ω| with hT
  have hTm : Measurable T := by rw [hT]; fun_prop
  have hT0 : ∀ ω, 0 ≤ T ω := fun ω => by
    rw [hT]; exact add_nonneg ((abs_nonneg _).trans (le_max_left _ _)) (by positivity)
  have hφcont : Continuous φ := continuous_iff_continuousAt.2 fun x => (hd x).continuousAt
  have hφ'm : Measurable φ' := (deriv_mono_of_convex hc hd).measurable
  have hTint : Integrable T μ := by
    refine Integrable.mono' (g := fun ω => (1 + K) * (|X ω| + |Y ω|))
      (((hXi.abs.add hYi.abs).const_mul _)) hTm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hT0 ω), hT]
    have h1 : max |X ω| |Y ω| ≤ |X ω| + |Y ω| :=
      max_le (by linarith [abs_nonneg (Y ω)]) (by linarith [abs_nonneg (X ω)])
    have h2 : |Y ω - X ω| ≤ |X ω| + |Y ω| := by
      have := abs_sub (Y ω) (X ω); linarith
    nlinarith [mul_le_mul_of_nonneg_left h2 hK]
  have key : ∀ N : ℕ, ∫⁻ ω, ENNReal.ofReal (truncFn φ φ' N (T ω)) ∂μ ≤
      ∫⁻ ω, ENNReal.ofReal (φ (w ω)) ∂μ := by
    intro N
    set Nr : ℝ := (N : ℝ) with hNr
    have hN : 0 ≤ Nr := Nat.cast_nonneg N
    set h : ℝ → ℝ → ℝ := fun x y =>
      -(φ' (min (max |x| |y| + K * |y - x|) Nr)) * (K * r) * sgn (y - x) with hh
    have hmeas : Measurable (Function.uncurry h) := by
      have : Measurable (fun p : ℝ × ℝ => φ' (min (max |p.1| |p.2| + K * |p.2 - p.1|) Nr)) :=
        hφ'm.comp (by fun_prop)
      simp only [hh]
      exact ((this.neg).mul_const _).mul (measurable_sgn.comp (by fun_prop))
    have hbdd : ∃ C, ∀ x y, |h x y| ≤ C := by
      refine ⟨φ' Nr * (K * r), fun x y => ?_⟩
      have hm0 : 0 ≤ min (max |x| |y| + K * |y - x|) Nr :=
        le_min (add_nonneg ((abs_nonneg _).trans (le_max_left _ _)) (by positivity)) hN
      have h1 : 0 ≤ φ' (min (max |x| |y| + K * |y - x|) Nr) := hφ'0 _ hm0
      have h2 : φ' (min (max |x| |y| + K * |y - x|) Nr) ≤ φ' Nr :=
        deriv_mono_of_convex hc hd (min_le_right _ _)
      simp only [hh, abs_mul, abs_neg]
      rw [abs_of_nonneg h1, abs_of_nonneg hK, abs_of_nonneg hr]
      calc _ ≤ φ' Nr * (K * r) * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_right h2 (mul_nonneg hK hr)) (abs_sgn_le _)
              (abs_nonneg _) (mul_nonneg (hφ'0 Nr hN) (mul_nonneg hK hr))
        _ = _ := by ring
    have hzero := hcenter h hmeas hbdd
    set ψ := truncFn φ φ' Nr with hψ
    have hψc : Continuous ψ := continuous_truncFn hφcont _
    have hψ0 : ∀ t, 0 ≤ ψ t := truncFn_nonneg hφ0 hφ'0 hN
    have hpt : ∀ ω, ψ (T ω) + h (X ω) (Y ω) * Z ω ≤ φ (w ω) := by
      intro ω
      set t := max |X ω| |Y ω| + K * |(Y ω - X ω) - r * Z ω| with ht
      have ht0 : 0 ≤ t := add_nonneg ((abs_nonneg _).trans (le_max_left _ _)) (by positivity)
      have htw : t ≤ w ω := hw ω
      have hm0 : 0 ≤ min (T ω) Nr := le_min (hT0 ω) hN
      have hd0 : 0 ≤ φ' (min (T ω) Nr) := hφ'0 _ hm0
      have htan := truncFn_tangent hc hd Nr (T ω) t
      have hsg := abs_sub_ge_sgn (Y ω - X ω) (r * Z ω)
      have hdiff : -(K * r * (sgn (Y ω - X ω) * Z ω)) ≤ t - T ω := by
        have : t - T ω = K * (|(Y ω - X ω) - r * Z ω| - |Y ω - X ω|) := by
          rw [ht, hT]; ring
        rw [this]
        have := mul_le_mul_of_nonneg_left hsg hK
        nlinarith
      have h3 : h (X ω) (Y ω) * Z ω ≤ φ' (min (T ω) Nr) * (t - T ω) := by
        have := mul_le_mul_of_nonneg_left hdiff hd0
        simp only [hh, hT]
        nlinarith
      have h4 : ψ t ≤ ψ (w ω) := truncFn_mono hmono hφ'0 hN ht0 htw
      have h5 : ψ (w ω) ≤ φ (w ω) := truncFn_le hc hd _ _
      linarith
    -- integrability
    have hψT : Integrable (fun ω => ψ (T ω)) μ := by
      refine Integrable.mono' (g := fun ω => φ Nr + φ' Nr * T ω)
        ((integrable_const _).add (hTint.const_mul _))
        (hψc.measurable.comp hTm).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hψ0 _)]
      exact truncFn_le_lin hmono hφ'0 hN (hT0 ω)
    have hhZ : Integrable (fun ω => h (X ω) (Y ω) * Z ω) μ := by
      obtain ⟨C, hC⟩ := hbdd
      refine Integrable.mono' (g := fun ω => C * |Z ω|) (hZi.abs.const_mul _)
        ((hmeas.comp (hX.prodMk hY)).mul hZ).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hC _ _) (abs_nonneg _)
    have hsum : Integrable (fun ω => ψ (T ω) + h (X ω) (Y ω) * Z ω) μ := hψT.add hhZ
    have hint0 : ∫ ω, ψ (T ω) ∂μ = ∫ ω, (ψ (T ω) + h (X ω) (Y ω) * Z ω) ∂μ := by
      rw [integral_add hψT hhZ, hzero, add_zero]
    calc ∫⁻ ω, ENNReal.ofReal (ψ (T ω)) ∂μ
        = ENNReal.ofReal (∫ ω, ψ (T ω) ∂μ) :=
          (ofReal_integral_eq_lintegral_ofReal hψT (Filter.Eventually.of_forall fun ω => hψ0 (T ω))).symm
      _ ≤ ∫⁻ ω, ENNReal.ofReal (ψ (T ω) + h (X ω) (Y ω) * Z ω) ∂μ := by
          rw [hint0]
          have hpos : Integrable (fun ω => max (ψ (T ω) + h (X ω) (Y ω) * Z ω) 0) μ :=
            hsum.pos_part
          calc ENNReal.ofReal (∫ ω, (ψ (T ω) + h (X ω) (Y ω) * Z ω) ∂μ)
              ≤ ENNReal.ofReal (∫ ω, max (ψ (T ω) + h (X ω) (Y ω) * Z ω) 0 ∂μ) :=
                ENNReal.ofReal_le_ofReal
                  (integral_mono hsum hpos (fun ω => le_max_left _ _))
            _ = ∫⁻ ω, ENNReal.ofReal (max (ψ (T ω) + h (X ω) (Y ω) * Z ω) 0) ∂μ :=
                ofReal_integral_eq_lintegral_ofReal hpos
                  (Filter.Eventually.of_forall fun ω => le_max_right _ _)
            _ = _ := by
                congr 1; ext ω
                rw [ENNReal.ofReal_max]; simp
      _ ≤ _ := lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hpt ω)
  -- Fatou
  have hlim : ∀ ω, Filter.Tendsto (fun N : ℕ => ENNReal.ofReal (truncFn φ φ' N (T ω)))
      Filter.atTop (nhds (ENNReal.ofReal (φ (T ω)))) := by
    intro ω
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop ⌈T ω⌉₊] with N hN
    have : T ω ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hN)
    rw [truncFn_of_le this]
  calc ∫⁻ ω, ENNReal.ofReal (φ (T ω)) ∂μ
      = ∫⁻ ω, Filter.liminf (fun N : ℕ => ENNReal.ofReal (truncFn φ φ' N (T ω)))
          Filter.atTop ∂μ := by
        congr 1; ext ω; exact ((hlim ω).liminf_eq).symm
    _ ≤ Filter.liminf (fun N : ℕ => ∫⁻ ω, ENNReal.ofReal (truncFn φ φ' N (T ω)) ∂μ)
          Filter.atTop :=
        lintegral_liminf_le fun N =>
          ENNReal.measurable_ofReal.comp ((continuous_truncFn hφcont _).measurable.comp hTm)
    _ ≤ _ := by
        refine Filter.liminf_le_of_le (by isBoundedDefault) fun b hb => ?_
        obtain ⟨N, hN⟩ := hb.exists
        exact hN.trans (key N)

end GMCExplicitDelta.Source
