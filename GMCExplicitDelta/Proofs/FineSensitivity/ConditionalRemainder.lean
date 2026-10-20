module

public import GMCExplicitDelta.Proofs.FineSensitivity.ProbeNorm
public import GMCExplicitDelta.Proofs.FineSensitivity.SphereNorm

/-! # Fixed-old-sample C13 estimate for the G3 remainder -/

@[expose] public section

open Homogenization Homogenization.Book.Ch02 MeasureTheory Matrix
open GMCExplicitDelta.Insertion
open SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab (ScalarCoeffOnData paperENNRealLpNorm)
open scoped ENNReal

namespace GMCExplicitDelta.Assembly

variable {d : ℕ} {U : Domain d}

theorem measurable_fine_qf {Ω : Type*} [MeasurableSpace Ω]
    {N : Ω → Mat d} (hN : Measurable N) (e : Vec d) :
    Measurable (fun ω => Coarse.qf (N ω) e) := by
  change Measurable (fun ω => ∑ i, e i * ∑ j, N ω i j * e j)
  exact Finset.measurable_sum _ (fun i _ => measurable_const.mul
    (Finset.measurable_sum _ (fun j _ =>
      (((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hN)).mul_const (e j)))))

theorem fine_remainder_probe_memLp {a : Vec d → ℝ}
    (h : ScalarCoeffOnData U a) (ha : Measurable a) (ha0 : ∀ x, 0 ≤ a x)
    (M : GMCModel d) {k L : ℕ} (hkL : k ≤ L) (i : Fin d)
    {η F G : ℝ} (hη : 0 < η)
    (hF : ∀ x, paperENNRealLpNorm M.P.toMeasure 32
      (fun ω => ENNReal.ofReal ((cutoffRatio M k L ω x - 1)^2)) ≤ ENNReal.ofReal F)
    (hG : ∀ x, paperENNRealLpNorm M.P.toMeasure 32
      (fun ω => ENNReal.ofReal (cutoffRatio M k L ω x + (cutoffRatio M k L ω x)⁻¹-2)) ≤
        ENNReal.ofReal G) (e : Vec d) :
    MemLp (fun ω => Coarse.qf (fineRemainderMatrix h (cutoffRatio M k L ω) η) e) 32 M.P.toMeasure := by
  have hN := measurable_fineRemainderMatrix h ha M hkL η
  have hp (ω) := fineRemainderMatrix_posSemidef h i hη ha0
    (cutoffRatio_pos M k L ω) (continuous_cutoffRatio M hkL ω)
  have hnn (ω) : 0 ≤ Coarse.qf (fineRemainderMatrix h (cutoffRatio M k L ω) η) e :=
    (hp ω).dotProduct_mulVec_nonneg e
  have hb := fine_remainder_probe_norm_le h ha ha0 M hkL i hη hF hG e
  change eLpNorm _ 32 _ < ∞
  rw [← Averaging.paperNorm_ofReal_eq_eLpNorm
    (measurable_fine_qf hN e).aestronglyMeasurable hnn]
  exact hb.trans_lt (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩)

/-- C13 is applied only after fixing the entire old coefficient. -/
theorem fine_remainder_conditional_moment {a : Vec d → ℝ} [NeZero d]
    (h : ScalarCoeffOnData U a) (ha : Measurable a) (ha0 : ∀ x, 0 ≤ a x)
    (M : GMCModel d) {k L : ℕ} (hkL : k ≤ L)
    {η F G J : ℝ} (hη : 0 < η) (hF0 : 0 ≤ F) (hG0 : 0 ≤ G) (hJ : 0 ≤ J)
    (hbound : ∀ e : Vec d, e ⬝ᵥ e = 1 → responseJ U h.toCoeffOn e e ≤ J)
    (hF : ∀ x, paperENNRealLpNorm M.P.toMeasure 32
      (fun ω => ENNReal.ofReal ((cutoffRatio M k L ω x - 1)^2)) ≤ ENNReal.ofReal F)
    (hG : ∀ x, paperENNRealLpNorm M.P.toMeasure 32
      (fun ω => ENNReal.ofReal (cutoffRatio M k L ω x + (cutoffRatio M k L ω x)⁻¹-2)) ≤
        ENNReal.ofReal G) :
    (∫⁻ ω, ENNReal.ofReal (‖Matrix.toEuclideanCLM (𝕜 := ℝ)
      (fineRemainderMatrix h (cutoffRatio M k L ω) η)‖) ^ (32 : ℝ) ∂M.P.toMeasure) ≤
      ENNReal.ofReal (sphereMomentRatio d 32 * ((J+1)*(F/(2*η)+G))^32) := by
  let i : Fin d := ⟨0, NeZero.pos d⟩
  have hp (ω) := fineRemainderMatrix_posSemidef h i hη ha0
    (cutoffRatio_pos M k L ω) (continuous_cutoffRatio M hkL ω)
  have hN := measurable_fineRemainderMatrix h ha M hkL η
  apply fine_psd_sphere_lintegral_le hN hp
  · intro e
    have hm := fine_remainder_probe_memLp h ha ha0 M hkL i hη hF hG e.ofLp
    simpa only [sphereQuadratic, Matrix.inner_toEuclideanCLM, Coarse.qf] using hm
  · positivity
  · intro e he
    have he' : e.ofLp ⬝ᵥ e.ofLp = 1 := by
      have hh := vecNorm_sq_eq_vecNormSq e.ofLp
      change ‖e‖^2 = vecNormSq e.ofLp at hh
      rw [he, one_pow] at hh
      exact hh.symm
    have hb := fine_remainder_unit_probe_norm_le h ha ha0 M hkL hη hF0 hG0 hF hG he'
    have hscalar : (responseJ U h.toCoeffOn e.ofLp e.ofLp + 1)*(F/(2*η)+G) ≤
        (J+1)*(F/(2*η)+G) :=
      mul_le_mul_of_nonneg_right (add_le_add (hbound e.ofLp he') le_rfl) (by positivity)
    refine le_trans ?_ (ENNReal.ofReal_le_ofReal hscalar)
    simpa only [sphereQuadratic, Matrix.inner_toEuclideanCLM, Coarse.qf] using hb

end GMCExplicitDelta.Assembly
