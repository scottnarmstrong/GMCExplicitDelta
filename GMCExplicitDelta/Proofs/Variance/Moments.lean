module

public import GMCExplicitDelta.Assembly.ModelFrozen
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.SecondMomentBudgets

/-! # Second moment of the frozen defect from the supplied finite cap -/

@[expose] public section

open MeasureTheory Homogenization Homogenization.Book SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion

open scoped ENNReal

namespace GMCExplicitDelta.Assembly

variable {d : ℕ}

theorem frozenVar_defect_second_moment (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (U : Ch02.Domain d) {D : ℝ} (hD : 0 ≤ D)
    (hJ : paperENNRealLpNorm M.P.toMeasure 32 (normalizedDefect M L U) ≤ ENNReal.ofReal D) :
    MemLp (fun ω => (normalizedDefect M L U ω).toReal) 2 M.P.toMeasure ∧
      ∫ ω, (normalizedDefect M L U ω).toReal ^ 2 ∂M.P.toMeasure ≤ D ^ 2 := by
  let : NeZero d := ⟨by have := M.shellPrefix.dimension; omega⟩
  have hm : Measurable (normalizedDefect M L U) :=
    (measurable_normalizedDefect_potentialShellIndexSigma_Iic M L U).mono
      (potentialShellIndexSigma_le_borel (d := d) (Set.Iic L)) le_rfl
  have h32 : eLpNorm (fun ω => (normalizedDefect M L U ω).toReal) 32 M.P.toMeasure ≤
      ENNReal.ofReal D := by
    have heq := paperENNRealLpNorm_eq_guarded_eLpNorm_toReal M.P.toMeasure
      (by norm_num : (0 : ℝ) < 32)
      (aux_dedup_d203_normalizedDefect_ne_top M L U) hm.ennreal_toReal.aestronglyMeasurable
    norm_num only [ENNReal.ofReal_ofNat] at heq
    rw [← heq]
    exact hJ
  have h2 : eLpNorm (fun ω => (normalizedDefect M L U ω).toReal) 2 M.P.toMeasure ≤
      ENNReal.ofReal D :=
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (2 : ℝ≥0∞) ≤ 32)).trans h32
  have hmem : MemLp (fun ω => (normalizedDefect M L U ω).toReal) 2 M.P.toMeasure :=
    h2.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hmem, ?_⟩
  rw [← Homogenization.toReal_eLpNorm_two_sq_eq_integral_sq hmem]
  apply (sq_le_sq₀ ENNReal.toReal_nonneg hD).2
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
  simpa only [ENNReal.toReal_ofReal hD] using h

end GMCExplicitDelta.Assembly
