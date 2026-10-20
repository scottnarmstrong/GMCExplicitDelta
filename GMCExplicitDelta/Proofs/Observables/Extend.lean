module

public import GMCExplicitDelta.Proofs.Observables.Translation

/-! R1: extension from the cutoff scale to all larger translated cubes. -/
@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open scoped ENNReal

namespace GMCExplicitDelta.Assembly

variable {d : ℕ}

theorem cutoff_cap_origin_extend (M : SubdiffusiveProcess.Model.GMCModel d) (m n : ℕ)
    (hmn : m ≤ n) {D : ℝ}
    (hD : paperENNRealLpNorm M.P.toMeasure 32
      (normalizedDefect M m (Ch02.cubeDomain (originCube d (m : ℤ)))) ≤ ENNReal.ofReal D) :
    paperENNRealLpNorm M.P.toMeasure 32
      (normalizedDefect M m (Ch02.cubeDomain (originCube d (n : ℤ)))) ≤ ENNReal.ofReal D := by
  classical
  let Q := originCube d (n : ℤ)
  let j := n - m
  let C := descendantsAtDepth Q j
  let c : ℝ≥0∞ := (C.card : ℝ≥0∞)⁻¹
  let X := fun R ω => normalizedDefect M m (Ch02.cubeDomain R) ω
  have hC : C.Nonempty := descendantsAtDepth_nonempty Q j
  have hscale : ∀ R ∈ C, R.scale = (m : ℤ) := by
    intro R hR
    have h := scale_eq_sub_of_mem_descendantsAtDepth hR
    change R.scale = (n : ℤ) - (n - m : ℕ) at h
    omega
  have hXm : ∀ R ∈ C, Measurable (X R) := fun R _ =>
    (measurable_cascadeObservables_proof M m _).1 (ahom M m)
  have hXb : ∀ R ∈ C, paperENNRealLpNorm M.P.toMeasure 32 (X R) ≤ ENNReal.ofReal D := by
    intro R hR
    change paperENNRealLpNorm _ _ (normalizedDefect M m (Ch02.cubeDomain R)) ≤ _
    rw [paperENNRealLpNorm_normalizedDefect_cube_eq_origin, hscale R hR]
    exact hD
  have hpoint (ω : SubdiffusiveProcess.Model.PotentialSample d) :
      normalizedDefect M m (Ch02.cubeDomain Q) ω ≤ c * ∑ R ∈ C, X R ω :=
    normalizedDefect_le_descendantsENNAverage M m Q j ω
  calc
    _ ≤ paperENNRealLpNorm M.P.toMeasure 32 (fun ω => c * ∑ R ∈ C, X R ω) :=
      paperENNRealLpNorm_mono_ae _ (by norm_num) (Filter.Eventually.of_forall hpoint)
    _ = c * paperENNRealLpNorm M.P.toMeasure 32 (fun ω => ∑ R ∈ C, X R ω) := by
      rw [paperENNRealLpNorm_const_mul_eq _ (by norm_num) c]
      exact Finset.measurable_sum _ hXm
    _ ≤ c * ∑ R ∈ C, paperENNRealLpNorm M.P.toMeasure 32 (X R) :=
      mul_le_mul le_rfl (paperENNRealLpNorm_finset_sum_le _ (by norm_num) C X hXm) zero_le zero_le
    _ ≤ c * ∑ _R ∈ C, ENNReal.ofReal D :=
      mul_le_mul le_rfl (Finset.sum_le_sum hXb) zero_le zero_le
    _ = ENNReal.ofReal D := by
      simp only [Finset.sum_const, nsmul_eq_mul, c]
      rw [← mul_assoc, ENNReal.inv_mul_cancel]
      · exact one_mul _
      · exact_mod_cast Finset.card_ne_zero.mpr hC
      · exact ENNReal.coe_ne_top

theorem inductionBounds_extend_proof (M : SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) {D F : ℝ}
    (hD : ∀ z : Homogenization.Vec d,
      paperENNRealLpNorm M.P.toMeasure 32 (normalizedDefect M m (cubeAt z m)) ≤ ENNReal.ofReal D)
    (hF : ∀ z e : Homogenization.Vec d, vecNormSq e = 1 →
      ∫⁻ ω, ENNReal.ofReal (frozenJ M m (cubeAt z m) e e ω) ∂M.P.toMeasure ≤ ENNReal.ofReal F) :
    ∀ n, m ≤ n → ∀ z : Homogenization.Vec d,
      paperENNRealLpNorm M.P.toMeasure 32 (normalizedDefect M m (cubeAt z n)) ≤
          ENNReal.ofReal D ∧
        ∀ e : Homogenization.Vec d, vecNormSq e = 1 →
          ∫⁻ ω, ENNReal.ofReal (frozenJ M m (cubeAt z n) e e ω) ∂M.P.toMeasure ≤
            ENNReal.ofReal F := by
  intro n hmn z
  constructor
  · rw [normalizedDefect_cubeAt_moment_eq_origin]
    apply cutoff_cap_origin_extend M m n hmn
    simpa only [cubeAt_zero] using hD 0
  · intro e he
    rw [frozenJ_lintegral_eq_fMean M m n z e he]
    have h := hF 0 e he
    rw [frozenJ_lintegral_eq_fMean M m m 0 e he] at h
    exact (ENNReal.ofReal_le_ofReal ((fMean_nonneg_antitone_proof M m).2 m n hmn)).trans h

end GMCExplicitDelta.Assembly
