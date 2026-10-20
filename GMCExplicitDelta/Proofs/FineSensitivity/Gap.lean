module

public import GMCExplicitDelta.Proofs.FineSensitivity.SpliceCoefficient
public import GMCExplicitDelta.Proofs.FineSensitivity.RemainderComparison
public import GMCExplicitDelta.Proofs.FineSensitivity.JointRatio
public import GMCExplicitDelta.Proofs.NativeCaps.MatrixLocal

/-! # The measurable scalar gap controlled by the fixed-old remainder -/

@[expose] public section

open Homogenization Homogenization.Book.Ch02 MeasureTheory Matrix
open SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab (normalizedDefect)
open GMCExplicitDelta.Insertion
open scoped ENNReal

namespace GMCExplicitDelta.Assembly

variable {d : ℕ}

noncomputable def fineTop (M : GMCModel d) (m : ℕ) (U : Domain d)
    (ω : PotentialSample d) : ℝ := sphereTop (frozenDefect M m U ω)

theorem fineTop_nonneg [NeZero d] (M : GMCModel d) (m : ℕ) (U : Domain d) (ω : PotentialSample d) :
    0 ≤ fineTop M m U ω := sphereTop_nonneg (frozenDefect_posSemidef M m U ω)

theorem fineTop_eq_opNorm [NeZero d] (M : GMCModel d) (m : ℕ) (U : Domain d)
    (ω : PotentialSample d) :
    fineTop M m U ω = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (frozenDefect M m U ω)‖ :=
  sphereTop_eq_opNorm_of_posSemidef (frozenDefect_posSemidef M m U ω)

theorem measurable_fineTop [NeZero d] (M : GMCModel d) (m : ℕ) (U : Domain d) :
    Measurable (fineTop M m U) :=
  (continuous_sphereTop d).measurable.comp (measurable_frozenDefect M m U)

theorem normalizedDefect_eq_ofReal_fineTop [NeZero d] (M : GMCModel d)
    (m : ℕ) (U : Domain d) (ω : PotentialSample d) :
    normalizedDefect M m U ω = ENNReal.ofReal (fineTop M m U ω) := by
  rw [fineTop_eq_opNorm, normalizedDefect_eq_ofReal_opNorm]

theorem fineTop_splice_prefix (M : GMCModel d) (k : ℕ) (U : Domain d)
    (old fresh : PotentialSample d) :
    fineTop M k U (fineSpliceSample k (old, fresh)) = fineTop M k U old := by
  unfold fineTop
  congr 1
  ext i j
  simp only [frozenDefect_entry, frozenJ_splice_prefix]

theorem frozenJ_le_fineTop [NeZero d] (M : GMCModel d) (m : ℕ) (U : Domain d)
    (ω : PotentialSample d) {e : Vec d} (he : e ⬝ᵥ e = 1) :
    frozenJ M m U e e ω ≤ fineTop M m U ω := by
  have hn : ‖WithLp.toLp 2 e‖ = 1 := by
    have hh := vecNorm_sq_eq_vecNormSq e
    change ‖WithLp.toLp 2 e‖^2 = e ⬝ᵥ e at hh
    rw [he] at hh
    nlinarith only [hh, norm_nonneg (WithLp.toLp 2 e)]
  have hb := le_csSup (sphereTop_bddAbove (frozenDefect M m U ω))
    (show sphereQuadratic (frozenDefect M m U ω) (WithLp.toLp 2 e) ∈
      sphereQuadratic (frozenDefect M m U ω) '' Metric.sphere 0 1 from
      ⟨_, mem_sphere_zero_iff_norm.mpr hn, rfl⟩)
  change sphereQuadratic (frozenDefect M m U ω) (WithLp.toLp 2 e) ≤ fineTop M m U ω at hb
  rw [sphereQuadratic_frozenDefect] at hb
  exact hb

noncomputable def fineGap (M : GMCModel d) (k L : ℕ) (U : Domain d) (η : ℝ)
    (ω : PotentialSample d) : ℝ := max (fineTop M L U ω - (1+η)*fineTop M k U ω) 0

theorem measurable_fineGap [NeZero d] (M : GMCModel d) (k L : ℕ) (U : Domain d) (η : ℝ) :
    Measurable (fineGap M k L U η) :=
  ((measurable_fineTop M L U).sub ((measurable_fineTop M k U).const_mul _)).max measurable_const

theorem fineGap_nonneg (M : GMCModel d) (k L : ℕ) (U : Domain d) (η : ℝ)
    (ω : PotentialSample d) : 0 ≤ fineGap M k L U η ω := le_max_right _ _

theorem fineTop_le_scaled_add_gap (M : GMCModel d) (k L : ℕ) (U : Domain d) (η : ℝ)
    (ω : PotentialSample d) :
    fineTop M L U ω ≤ (1+η)*fineTop M k U ω + fineGap M k L U η ω := by
  have h := le_max_left (fineTop M L U ω - (1+η)*fineTop M k U ω) 0
  dsimp [fineGap]
  linarith

/-- The measurable scalar gap is controlled pointwise by the fixed-old matrix. -/
theorem fineGap_splice_le [NeZero d] (M : GMCModel d) {k L : ℕ} (hkL : k ≤ L)
    (U : Domain d) {η : ℝ} (hη : 0 < η) (old fresh : PotentialSample d) :
    fineGap M k L U η (fineSpliceSample k (old, fresh)) ≤
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
        (fineRemainderMatrix (fineNormalizedCoeffData M k old U)
          (cutoffRatio M k L fresh) η)‖ := by
  let h := fineNormalizedCoeffData M k old U
  let h' := fineNormalizedCoeffData M L (fineSpliceSample k (old, fresh)) U
  have hb := Averaging.psd_opNorm_le_constant_add
    (H := fineRemainderMatrix h (cutoffRatio M k L fresh) η)
    (frozenDefect_posSemidef M L U (fineSpliceSample k (old, fresh)))
    (show 0 ≤ (1+η)*fineTop M k U old from mul_nonneg (by positivity) (fineTop_nonneg _ _ _ _))
    (by
      intro e he
      have he' : e.ofLp ⬝ᵥ e.ofLp = 1 := by
        have hh := vecNorm_sq_eq_vecNormSq e.ofLp
        change ‖e‖^2 = e.ofLp ⬝ᵥ e.ofLp at hh
        rw [he, one_pow] at hh
        exact hh.symm
      have hc := responseJ_le_fineRemainderMatrix h h' hη he'
        (cutoffRatio_pos M k L fresh) (continuous_cutoffRatio M hkL fresh)
        (Filter.Eventually.of_forall fun x => fine_normalized_splice_coefficient M hkL old fresh x)
      rw [← frozenJ_eq_response_normalized M k old U,
        ← frozenJ_eq_response_normalized M L (fineSpliceSample k (old, fresh)) U] at hc
      have ht := mul_le_mul_of_nonneg_left (frozenJ_le_fineTop M k U old he')
        (show 0 ≤ 1+η by positivity)
      rw [sphereQuadratic_frozenDefect]
      simpa only [sphereQuadratic,
        Matrix.inner_toEuclideanCLM, Coarse.qf] using hc.trans (add_le_add ht le_rfl))
  rw [← fineTop_eq_opNorm] at hb
  unfold fineGap
  rw [fineTop_splice_prefix]
  exact max_le (by linarith only [hb]) (norm_nonneg _)

end GMCExplicitDelta.Assembly
