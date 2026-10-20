module

public import GMCExplicitDelta.Assembly.ModelInduction
public import GMCExplicitDelta.Coarse.Affine
public import GMCExplicitDelta.Coarse.PhiLpIntegral
public import SubdiffusiveProcess.CoarseGrainingVocab.MeasurabilityProviders

/-! # Deterministic shifts of the scalar normalization -/

@[expose] public section

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta.Assembly

open Contract Coarse

variable {d : ℕ}

/-- The normalized response written as two scalar quadratic forms. -/
theorem normalized_response_formula {U : Ch02.Domain d} {a : Ch02.CoeffOn U}
    (ha : Ch02.CoeffOn.IsSymmetric a) {e : Homogenization.Vec d} (he : vecNormSq e = 1)
    {s : ℝ} (hs : 0 < s) :
    J U a ((Real.sqrt s)⁻¹ • e) (Real.sqrt s • e) =
      (qf (XU U a) e / s + s * qf (YU U a) e) / 2 - 1 := by
  change Ch02.responseJ U a _ _ = _
  rw [responseJ_eq_XY ha, posDef_qf_smul, posDef_qf_smul,
    smul_dotProduct, dotProduct_smul]
  change _ - (Real.sqrt s)⁻¹ * (Real.sqrt s * vecNormSq e) = _
  rw [he, mul_one, inv_mul_cancel₀ (Real.sqrt_pos.mpr hs).ne']
  simp only [inv_pow, Real.sq_sqrt hs.le]
  ring

/-- C7 applies with an arbitrary positive base normalization. -/
theorem normalized_response_shift_le {U : Ch02.Domain d} {a : Ch02.CoeffOn U}
    (ha : Ch02.CoeffOn.IsSymmetric a) {e : Homogenization.Vec d} (he : vecNormSq e = 1)
    {s : ℝ} (hs : 0 < s) (c : ℝ) :
    J U a ((Real.sqrt (s * Real.exp c))⁻¹ • e) (Real.sqrt (s * Real.exp c) • e) ≤
      phi |c| (J U a ((Real.sqrt s)⁻¹ • e) (Real.sqrt s • e)) := by
  have he0 : e ≠ 0 := by rintro rfl; simp [vecNormSq, vecDot] at he
  have hα := posDef_qf_pos (XU_posDef ha) he0
  have h1 := posDef_sq_dot_le (XU_posDef ha) e
  have h2 := (matLoewnerLE_iff_qf.mp (XU_inv_le_YU ha)) e
  have hαβ : 1 ≤ (s * qf (YU U a) e) * (qf (XU U a) e / s) := by
    have he' : e ⬝ᵥ e = 1 := he
    rw [he'] at h1
    have hx : 1 ≤ qf (XU U a) e * qf (YU U a) e := by nlinarith
    convert hx using 1
    field_simp [hs.ne']
  rw [normalized_response_formula ha he (mul_pos hs (Real.exp_pos c)),
    normalized_response_formula ha he hs]
  have h := half_exp_le_phi hαβ c
  have heq : qf (XU U a) e / (s * Real.exp c) =
      Real.exp (-c) * (qf (XU U a) e / s) := by
    simp only [Real.exp_neg, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [heq]
  convert h using 1 <;> congr 1 <;> ring

/-- The normalized affine and constant-flux trials on any deterministic domain. -/
theorem normalized_response_le_trial (M : SubdiffusiveProcess.Model.GMCModel d) (m : ℕ)
    (U : Ch02.Domain d) {s : ℝ} (hs : 0 < s)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) (e : Homogenization.Vec d) (he : vecNormSq e = 1) :
    J U (aCutoffCoeffOnData M m ω U).toCoeffOn
      ((Real.sqrt s)⁻¹ • e) (Real.sqrt s • e) ≤
      (Ch02.average U (SubdiffusiveProcess.Model.aCutoff M m ω) / s +
        s * Ch02.average U (fun x => (SubdiffusiveProcess.Model.aCutoff M m ω x)⁻¹)) / 2 - 1 := by
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension
  have hX := qf_XU_le_average (aCutoffCoeffOnData M m ω U) e
  have hY := qf_YU_le_average (aCutoffCoeffOnData M m ω U) ⟨0, hd⟩ e
  change e ⬝ᵥ e = 1 at he
  rw [he, mul_one] at hX hY
  rw [normalized_response_formula (aCutoffCoeffOnData M m ω U).isSymmetric he hs]
  linarith only [div_le_div_of_nonneg_right hX hs.le,
    mul_le_mul_of_nonneg_left hY hs.le]

/-- The affine trial is a finite upper bound for the literal sphere maximum. -/
theorem scaledDefect_ne_top (M : SubdiffusiveProcess.Model.GMCModel d) (m : ℕ)
    (U : Ch02.Domain d) {s : ℝ} (hs : 0 < s)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) : scaledDefect M m U s ω ≠ ∞ := by
  apply ne_of_lt
  refine lt_of_le_of_lt (b := ENNReal.ofReal
    ((Ch02.average U (SubdiffusiveProcess.Model.aCutoff M m ω) / s +
      s * Ch02.average U (fun x => (SubdiffusiveProcess.Model.aCutoff M m ω x)⁻¹)) / 2 - 1))
    ?_ ENNReal.ofReal_lt_top
  apply iSup_le
  intro e
  exact ENNReal.ofReal_le_ofReal (normalized_response_le_trial M m U hs ω e e.property)

/-- Continuity in the unit direction reduces the measurable supremum to a countable dense set. -/
theorem measurable_scaledDefect (M : SubdiffusiveProcess.Model.GMCModel d) (m : ℕ)
    (U : Ch02.Domain d) (s : ℝ) : Measurable (scaledDefect M m U s) := by
  let : NeZero d := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension)⟩
  have hm := fun e : {e : Homogenization.Vec d // vecNormSq e = 1} =>
    ENNReal.measurable_ofReal.comp (measurable_cutoff_responseJ M m U
      ((Real.sqrt s)⁻¹ • (e : Homogenization.Vec d)) (Real.sqrt s • (e : Homogenization.Vec d)))
  have hc : ∀ ω : SubdiffusiveProcess.Model.PotentialSample d,
      LowerSemicontinuous (fun e : {e : Homogenization.Vec d // vecNormSq e = 1} =>
        ENNReal.ofReal (J U (aCutoffCoeffOnData M m ω U).toCoeffOn
          ((Real.sqrt s)⁻¹ • (e : Homogenization.Vec d)) (Real.sqrt s • (e : Homogenization.Vec d)))) := by
    intro ω
    apply Continuous.lowerSemicontinuous
    apply ENNReal.continuous_ofReal.comp
    change Continuous (fun e : {e : Homogenization.Vec d // vecNormSq e = 1} =>
      Ch02.responseJ U (aCutoffCoeffOnData M m ω U).toCoeffOn
        ((Real.sqrt s)⁻¹ • (e : Homogenization.Vec d)) (Real.sqrt s • (e : Homogenization.Vec d)))
    simp_rw [responseJ_eq_XY (aCutoffCoeffOnData M m ω U).isSymmetric]
    unfold qf Matrix.mulVec dotProduct
    fun_prop
  convert measurable_iSup_of_lowerSemicontinuous hm hc using 1
  funext ω
  simp only [scaledDefect, paperScalarProbeMaxOn, iSup_apply, Function.comp_def]

/-- The paper's raw norm agrees with the usual norm for a measurable nonnegative real variable. -/
theorem paper_norm_ofReal_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {f : Ω → ℝ} (hf : AEMeasurable f μ) (hf0 : ∀ ω, 0 ≤ f ω) :
    paperENNRealLpNorm μ 32 (fun ω => ENNReal.ofReal (f ω)) =
      eLpNorm f (ENNReal.ofReal 32) μ := by
  rw [eLpNorm_eq_eLpNorm' (by norm_num) ENNReal.ofReal_ne_top hf.aestronglyMeasurable]
  simp only [eLpNorm', paperENNRealLpNorm, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 32),
    Real.enorm_eq_ofReal (hf0 _), one_div]

theorem scaledDefect_shift_le_proof (M : SubdiffusiveProcess.Model.GMCModel d) (m : ℕ)
    (U : Ch02.Domain d) {s c γ y : ℝ} (hs : 0 < s) (hc : |c| ≤ γ) (hy : 0 ≤ y)
    (h : paperENNRealLpNorm M.P.toMeasure 32 (scaledDefect M m U s) ≤ ENNReal.ofReal y) :
    paperENNRealLpNorm M.P.toMeasure 32 (scaledDefect M m U (s * Real.exp c)) ≤
      ENNReal.ofReal (PhiMap γ y) := by
  let f := fun ω => (scaledDefect M m U s ω).toReal
  have hf : Measurable f :=
    (measurable_scaledDefect M m U s).ennreal_toReal
  have hf0 : ∀ ω, 0 ≤ f ω := fun ω => ENNReal.toReal_nonneg
  have heq : ∀ ω, ENNReal.ofReal (f ω) = scaledDefect M m U s ω := fun ω =>
    ENNReal.ofReal_toReal (scaledDefect_ne_top M m U hs ω)
  have hγ : 0 ≤ γ := (abs_nonneg c).trans hc
  have hpoint : ∀ ω, scaledDefect M m U (s * Real.exp c) ω ≤ ENNReal.ofReal (phi γ (f ω)) := by
    intro ω
    apply iSup_le
    intro e
    apply ENNReal.ofReal_le_ofReal
    have hb : J U (aCutoffCoeffOnData M m ω U).toCoeffOn
        ((Real.sqrt s)⁻¹ • (e : Homogenization.Vec d)) (Real.sqrt s • (e : Homogenization.Vec d)) ≤ f ω := by
      apply (ENNReal.ofReal_le_iff_le_toReal (scaledDefect_ne_top M m U hs ω)).mp
      exact le_iSup (fun e : {e : Homogenization.Vec d // vecNormSq e = 1} =>
        ENNReal.ofReal (J U (aCutoffCoeffOnData M m ω U).toCoeffOn
          ((Real.sqrt s)⁻¹ • (e : Homogenization.Vec d)) (Real.sqrt s • (e : Homogenization.Vec d)))) e
    have hj0 := Ch02.responseJ_nonneg U (aCutoffCoeffOnData M m ω U).toCoeffOn
      ((Real.sqrt s)⁻¹ • (e : Homogenization.Vec d)) (Real.sqrt s • (e : Homogenization.Vec d))
    exact (normalized_response_shift_le (aCutoffCoeffOnData M m ω U).isSymmetric e.property hs c).trans
      ((phi_mono_j (abs_nonneg c) hj0 (hf0 ω) hb).trans
        (phi_mono_t (hf0 ω) (abs_nonneg c) hγ hc))
  have hbase : eLpNorm f (ENNReal.ofReal 32) M.P.toMeasure ≤ ENNReal.ofReal y := by
    rw [← paper_norm_ofReal_eq M.P.toMeasure hf.aemeasurable hf0]
    simpa only [heq] using h
  have hp := eLpNorm_phi_comp_le (by norm_num : (2 : ℝ) ≤ 32) hf.aemeasurable hf0 hγ hy hbase
  have hpmeas := (continuous_phi γ).measurable.comp hf
  have hp0 := fun ω => phi_nonneg (hf0 ω) hγ
  calc
    _ ≤ paperENNRealLpNorm M.P.toMeasure 32 (fun ω => ENNReal.ofReal (phi γ (f ω))) := by
      apply ENNReal.rpow_le_rpow _ (by norm_num)
      exact lintegral_mono fun ω => ENNReal.rpow_le_rpow (hpoint ω) (by norm_num)
    _ = eLpNorm (fun ω => phi γ (f ω)) (ENNReal.ofReal 32) M.P.toMeasure :=
      paper_norm_ofReal_eq M.P.toMeasure hpmeas.aemeasurable hp0
    _ ≤ _ := hp

end GMCExplicitDelta.Assembly
