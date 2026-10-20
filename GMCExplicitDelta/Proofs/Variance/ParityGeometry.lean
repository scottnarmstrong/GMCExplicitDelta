module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ResponseRosenthal

/-! # Parity separation above the cutoff, with room for local representatives -/

@[expose] public section

open MeasureTheory Matrix Homogenization Homogenization.Book SubdiffusiveProcess.CoarseGrainingVocab

namespace GMCExplicitDelta.Assembly

variable {d : ℕ}

def frozenVar_parityColor (R : Homogenization.TriadicCube d) : Fin d → Fin 2 := fun i =>
  ⟨Int.toNat (R.index i % 2), by
    have hn := Int.emod_nonneg (R.index i) (by norm_num : (2 : ℤ) ≠ 0)
    have hl := Int.emod_lt_of_pos (R.index i) (by norm_num : (0 : ℤ) < 2)
    omega⟩

theorem frozenVar_parity_mod {R S : Homogenization.TriadicCube d}
    (h : frozenVar_parityColor R = frozenVar_parityColor S) (i : Fin d) :
    R.index i % 2 = S.index i % 2 := by
  have hv := congrArg Fin.val (congrFun h i)
  change Int.toNat (R.index i % 2) = Int.toNat (S.index i % 2) at hv
  have hR := Int.emod_nonneg (R.index i) (by norm_num : (2 : ℤ) ≠ 0)
  have hS := Int.emod_nonneg (S.index i) (by norm_num : (2 : ℤ) ≠ 0)
  omega

theorem frozenVar_parity_base_separation {R S : Homogenization.TriadicCube d}
    (hscale : R.scale = S.scale) (hcolor : frozenVar_parityColor R = frozenVar_parityColor S)
    (hne : R ≠ S) {x y : Homogenization.Vec d} (hx : x ∈ cubeSet R) (hy : y ∈ cubeSet S) :
    cubeScaleFactor R ≤ Homogenization.euclideanNorm (x - y) := by
  have hindex : ∃ i, R.index i ≠ S.index i := by
    by_contra h
    push Not at h
    apply hne
    cases R with
    | mk r u =>
      cases S with
      | mk s v =>
        simp only [TriadicCube.mk.injEq]
        exact ⟨hscale, funext h⟩
  obtain ⟨i, hi⟩ := hindex
  have hmod := frozenVar_parity_mod hcolor i
  have hfactor : cubeScaleFactor S = cubeScaleFactor R := by
    simp only [cubeScaleFactor, hscale]
  have hpos : 0 ≤ cubeScaleFactor R := by unfold cubeScaleFactor; positivity
  have hxR := hx i
  have hyS := hy i
  rw [hfactor] at hyS
  have hcoord : cubeScaleFactor R ≤ |(x - y) i| := by
    rcases lt_or_gt_of_ne hi with hlt | hgt
    · have hgap : R.index i + 2 ≤ S.index i := by omega
      have hgap' : (R.index i : ℝ) + 2 ≤ (S.index i : ℝ) := by exact_mod_cast hgap
      rw [Pi.sub_apply, abs_sub_comm, abs_of_nonneg]
      · nlinarith only [hxR.2.le, hyS.1, mul_le_mul_of_nonneg_right hgap' hpos]
      · nlinarith only [hxR.2.le, hyS.1, mul_le_mul_of_nonneg_right hgap' hpos, hpos]
    · have hgap : S.index i + 2 ≤ R.index i := by omega
      have hgap' : (S.index i : ℝ) + 2 ≤ (R.index i : ℝ) := by exact_mod_cast hgap
      rw [Pi.sub_apply, abs_of_nonneg]
      · nlinarith only [hxR.1, hyS.2.le, mul_le_mul_of_nonneg_right hgap' hpos]
      · nlinarith only [hxR.1, hyS.2.le, mul_le_mul_of_nonneg_right hgap' hpos, hpos]
  have hnorm : |(x - y) i| ≤ ‖x - y‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm (x - y) i
  exact hcoord.trans (hnorm.trans (Homogenization.norm_le_euclideanNorm (x - y)))

/-- Above the cutoff the parity gap survives the positive locality thickening. -/
theorem frozenVar_parity_thickened_separation (hd : d ∈ ({2, 3, 4} : Finset ℕ))
    {L k : ℕ} (hk : L + 1 ≤ k) {R S : Homogenization.TriadicCube d}
    (hR : R.scale = (k : ℤ)) (hS : S.scale = (k : ℤ))
    (hcolor : frozenVar_parityColor R = frozenVar_parityColor S) (hne : R ≠ S)
    {x y : Homogenization.Vec d}
    (hx : x ∈ Metric.thickening (responseRestrictionBridgeRadius d) (cubeSet R))
    (hy : y ∈ Metric.thickening (responseRestrictionBridgeRadius d) (cubeSet S)) :
    Real.sqrt (d : ℝ) * (3 : ℝ) ^ L ≤ Ch02.vecNorm (x - y) := by
  have hd2 : 2 ≤ d := by simp only [Finset.mem_insert, Finset.mem_singleton] at hd; omega
  have hd4 : d ≤ 4 := by simp only [Finset.mem_insert, Finset.mem_singleton] at hd; omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  obtain ⟨x0, hx0, hxx0⟩ := Metric.mem_thickening_iff.mp hx
  obtain ⟨y0, hy0, hyy0⟩ := Metric.mem_thickening_iff.mp hy
  have hbase := frozenVar_parity_base_separation (hR.trans hS.symm) hcolor hne hx0 hy0
  have hnormEq (z : Homogenization.Vec d) : Homogenization.euclideanNorm z = Ch02.vecNorm z := by
    rw [← sq_eq_sq₀ (Homogenization.euclideanNorm_nonneg z) (Ch02.vecNorm_nonneg z),
      Homogenization.euclideanNorm_sq, Ch02.vecNorm_sq_eq_vecNormSq]
  rw [hnormEq, cubeScaleFactor, hR, zpow_natCast] at hbase
  have hpertx : Ch02.vecNorm (x0 - x) < (d : ℝ) * responseRestrictionBridgeRadius d := by
    rw [← hnormEq]
    exact lt_of_le_of_lt (euclideanNorm_le_dimension_mul_norm (x0 - x)) (by
      rw [← dist_eq_norm]
      simpa only [dist_comm] using mul_lt_mul_of_pos_left hxx0 hdpos)
  have hperty : Ch02.vecNorm (y - y0) < (d : ℝ) * responseRestrictionBridgeRadius d := by
    rw [← hnormEq]
    exact lt_of_le_of_lt (euclideanNorm_le_dimension_mul_norm (y - y0)) (by
      rw [← dist_eq_norm]
      exact mul_lt_mul_of_pos_left hyy0 hdpos)
  have htri : Ch02.vecNorm (x0 - y0) ≤
      Ch02.vecNorm (x0 - x) + Ch02.vecNorm (x - y) + Ch02.vecNorm (y - y0) := by
    simp only [← hnormEq, Homogenization.euclideanNorm_eq_norm_ofVec]
    have hid : x0 - y0 = (x0 - x) + (x - y) + (y - y0) := by abel
    rw [hid]
    simpa only [map_add] using! norm_add₃_le (a := HilbertVec.ofVec (x0 - x))
      (b := HilbertVec.ofVec (x - y)) (c := HilbertVec.ofVec (y - y0))
  have heps : (d : ℝ) * responseRestrictionBridgeRadius d < 1 / 4 := by
    rw [responseRestrictionBridgeRadius, inv_eq_one_div, mul_one_div,
      div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * ((d : ℝ) + 1))]
    linarith
  have hsqrt : Real.sqrt (d : ℝ) ≤ 2 := by
    apply (Real.sqrt_le_iff).2
    constructor
    · norm_num
    · exact_mod_cast hd4
  have hp : (3 : ℝ) ^ (L + 1) ≤ (3 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hk
  rw [pow_succ] at hp
  have hunit : (1 : ℝ) ≤ 3 ^ L := one_le_pow₀ (by norm_num)
  have htarget := mul_le_mul_of_nonneg_right hsqrt (by positivity : (0 : ℝ) ≤ 3 ^ L)
  linarith only [hbase, hpertx, hperty, htri, heps, hp, hunit, htarget]

end GMCExplicitDelta.Assembly
