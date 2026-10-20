module

public import GMCExplicitDelta.Coarse.Affine
public import SubdiffusiveProcess.CoarseGrainingVocab.Defect

/-! # The affine upper bound at an arbitrary normalization (K1) -/

@[expose] public section

open Homogenization Homogenization.Book.Ch02 Matrix
open MeasureTheory hiding average
open SubdiffusiveProcess.CoarseGrainingVocab (ScalarCoeffOnData paperScalarProbeMaxOn)

namespace GMCExplicitDelta.Insertion

/-- The affine trial controls every direction simultaneously, without a sphere factor. -/
theorem paperScalarProbeMaxOn_le_affine {d : ℕ} {U : Domain d} {a : Vec d → ℝ}
    (h : ScalarCoeffOnData U a) {s : ℝ} (hs : 0 < s) :
    paperScalarProbeMaxOn U h.toCoeffOn s ≤
      ENNReal.ofReal ((average U a / s + s * average U (fun x => (a x)⁻¹)) / 2 - 1) := by
  unfold paperScalarProbeMaxOn
  refine iSup_le fun e => ENNReal.ofReal_le_ofReal ?_
  let t := Real.sqrt s
  have ht : 0 < t := Real.sqrt_pos.mpr hs
  have ht2 : t ^ 2 = s := Real.sq_sqrt hs.le
  have he : (e : Vec d) ⬝ᵥ (e : Vec d) = 1 := e.property
  have hp : (t⁻¹ • (e : Vec d)) ⬝ᵥ (t⁻¹ • (e : Vec d)) = s⁻¹ := by
    simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul, he, mul_one]
    rw [← pow_two, inv_pow, ht2]
  have hq : (t • (e : Vec d)) ⬝ᵥ (t • (e : Vec d)) = s := by
    simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul, he, mul_one]
    simpa only [pow_two] using ht2
  have hpq : (t⁻¹ • (e : Vec d)) ⬝ᵥ (t • (e : Vec d)) = 1 := by
    simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul, he, mul_one]
    exact mul_inv_cancel₀ ht.ne'
  have hX := Coarse.qf_XU_le_average h (t⁻¹ • (e : Vec d))
  have hi : Fin d := ⟨0, by
    by_contra hn
    have hd : d = 0 := by omega
    subst d
    simp only [dotProduct, Finset.univ_eq_empty, Finset.sum_empty] at he
    norm_num at he⟩
  have hY := Coarse.qf_YU_le_average h hi (t • (e : Vec d))
  rw [hp] at hX
  rw [hq] at hY
  change responseJ U h.toCoeffOn (t⁻¹ • (e : Vec d)) (t • (e : Vec d)) ≤ _
  rw [Coarse.responseJ_eq_XY (Coarse.scalarCoeffOn_isSymmetric h), hpq]
  calc
    _ ≤ (1 / 2) * (average U a * s⁻¹) +
        (1 / 2) * (average U (fun x => (a x)⁻¹) * s) - 1 := by linarith only [hX, hY]
    _ = _ := by ring

/-- Hyperbolic form of the normalized affine trial (K1). -/
theorem paperScalarProbeMaxOn_le_average_cosh_log_sub {d : ℕ} [NeZero d]
    {U : Domain d} {a : Vec d → ℝ} (h : ScalarCoeffOnData U a)
    {s : ℝ} (hs : 0 < s) :
    paperScalarProbeMaxOn U h.toCoeffOn s ≤
      ENNReal.ofReal (average U (fun x => Real.cosh (Real.log (a x) - Real.log s) - 1)) := by
  have i : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
  have hcosh : (fun x => Real.cosh (Real.log (a x) - Real.log s) - 1) =ᵐ[
      volumeMeasureOn (U : Set (Vec d))]
      (fun x => (s⁻¹ * a x + s * (a x)⁻¹) / 2 - 1) := by
    filter_upwards [Coarse.a_pos_ae h] with x hx
    rw [← Real.log_div hx.ne' hs.ne', Real.cosh_log (div_pos hx hs)]
    field_simp
  have havg : average U (fun x => Real.cosh (Real.log (a x) - Real.log s) - 1) =
      (average U a / s + s * average U (fun x => (a x)⁻¹)) / 2 - 1 := by
    rw [Coarse.average_congr_ae hcosh,
      Coarse.average_add_sub ((Coarse.integrable_scalar h i).const_mul s⁻¹)
        ((Coarse.integrable_scalar_inv h i).const_mul s),
      Coarse.average_const_mul', Coarse.average_const_mul']
    ring
  rw [havg]
  exact paperScalarProbeMaxOn_le_affine h hs

end GMCExplicitDelta.Insertion
