module

public import GMCExplicitDelta.Proofs.HaarMode.Bounds
public import GMCExplicitDelta.Proofs.HaarBlocks.CellPoincare

/-! # H10 from the exact sharp cell Poincaré statement -/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace GMCExplicitDelta.Localization

open Assembly Contract
variable {d : ℕ}

/-- The contract width lies in the range used by the cutoff moment identities. -/
theorem haarMode_omega_bounds (row : Row d) (hO : row.Obligations) :
    0 < row.omegaEff ∧ row.omegaEff ≤ 1 / 2 := by
  unfold Row.omegaEff
  split_ifs with hd
  · norm_num
  · have h := (hO.par2.2.2.2.2.2 hd).2
    constructor
    · exact_mod_cast h.1
    · have h' : (row.width : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr h.2
      simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h'

/-- The positive Haar weight is below the cell-decay factor nine. -/
theorem haarMode_qs_bounds (row : Row d) (hO : row.Obligations) : 1 < row.qs ∧ row.qs < 9 := by
  have hs0 : 0 < (row.s : ℝ) := by exact_mod_cast hO.par1.2.2.2.2.2.1
  have hs1 : (row.s : ℝ) < 1 / 2 := by
    have hs1' : (row.s : ℝ) < ((1 / 2 : ℚ) : ℝ) := Rat.cast_lt.mpr hO.par1.2.2.2.2.2.2.1
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hs1'
  unfold Row.qs
  constructor
  · exact Real.one_lt_rpow (by norm_num) (by linarith)
  · have hlt : (3 : ℝ) ^ (2 * (row.s : ℝ)) < (3 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
    norm_num only [Real.rpow_one] at hlt
    linarith

/-- The minimum series is homogeneous under nonnegative scalar multiplication. -/
theorem haarMode_minSeries_mul (q R H C : ℝ) (hC : 0 ≤ C) :
    minSeries q (R * C) (H * C) = minSeries q R H * C := by
  unfold minSeries
  rw [← tsum_mul_right]
  apply tsum_congr
  intro j
  rw [show H * C / 9 ^ j = (H / 9 ^ j) * C by ring, ← min_mul_of_nonneg _ _ hC]
  ring

/-- Squaring the real square root always dominates its argument. -/
theorem haarMode_le_sqrt_sq (x : ℝ) : x ≤ Real.sqrt x ^ 2 := by
  by_cases hx : 0 ≤ x
  · rw [Real.sq_sqrt hx]
  · exact (le_of_not_ge hx).trans (sq_nonneg _)

/-- H10, with exactly H8's conclusion as the sole internal analytic hypothesis. -/
theorem haar_constant_mode_of_cellPoincare
    (hP : ∀ (Q : Homogenization.TriadicCube d) (j : ℕ) (h : H1Function (openCubeSet Q)),
      Haar.energy Q (fun x => h.toFun x - cubeProjection Q j h.toFun x) ≤
        cubeScaleFactor Q ^ 2 / (9 ^ j * Real.pi ^ 2) * vecEnergy Q h.grad)
    (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ))
    (hO : row.Obligations) (n : ℕ) (a : Homogenization.Vec d) :
    haarPrimal (originCube d (n : ℤ)) row.qs (fun x =>
        (vecDot a x - cubeAverage (originCube d (n : ℤ)) (fun y => vecDot a y)) •
          cubeCutoffGrad row n x) ≤
      ENNReal.ofReal (row.haarB 0 ^ 2 * vecNormSq a) := by
  classical
  obtain ⟨h0, h1⟩ := haarMode_omega_bounds row hO
  obtain ⟨hq1, hq9⟩ := haarMode_qs_bounds row hO
  have hC := vecNormSq_nonneg a
  have hR := haarMode_residual_R row hd h0 h1 n a
  have hH := haarMode_residual_H hP row hd h0 h1 n a
  have hr0 : 0 ≤ LocWeights.residualEnergy (originCube d (n : ℤ)) 0 (haarMode_field row n a) :=
    Finset.sum_nonneg fun _ _ => Haar.energy_nonneg _ _
  have hA : 0 ≤ row.Rcirc * vecNormSq a := hr0.trans (hR 0)
  have hB : 0 ≤ row.Hcirc * vecNormSq a := by simpa using hr0.trans (hH 0)
  have hm (i : Fin d) : MemLp (fun x => haarMode_field row n a x i) 2
      (normalizedCubeMeasure (originCube d (n : ℤ))) := by
    obtain ⟨u, hf, _⟩ := haarMode_affine_cutoff_h1 h1 n a i
    simpa only [hf, haarMode_field] using u.memL2_normalizedCubeMeasure
  have hr (j : ℕ) : LocWeights.residualEnergy (originCube d (n : ℤ)) j (haarMode_field row n a) ≤
      min (row.Rcirc * vecNormSq a) ((row.Hcirc * vecNormSq a) / 9 ^ j) := by
    exact le_min (hR j) ((hH j).trans_eq (by ring))
  have hb := haarMode_haarPrimal_le_minSeries (originCube d (n : ℤ)) hq1 hq9 hA hB
    (haarMode_field row n a) hm (haarMode_total_energy row hd h0 h1 n a).le hr
  have heq : (fun x =>
      (vecDot a x - cubeAverage (originCube d (n : ℤ)) (fun y => vecDot a y)) •
        cubeCutoffGrad row n x) = haarMode_field row n a := by
    rw [haarMode_affine_mean]
    funext x i
    have hdot : vecDot a (fun k => x k / (3 : ℝ) ^ n) = vecDot a x / (3 : ℝ) ^ n := by
      unfold vecDot
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      ring
    simp only [sub_zero, Pi.smul_apply, smul_eq_mul, cubeCutoffGrad, haarMode_field, haarMode_rawG_eq]
    rw [hdot]
    ring
  rw [heq]
  refine hb.trans ?_
  rw [haarMode_minSeries_mul _ _ _ _ hC]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ = (row.Lcirc + (row.qs - 1) * minSeries row.qs row.Rcirc row.Hcirc) * vecNormSq a := by ring
    _ ≤ row.haarB 0 ^ 2 * vecNormSq a := by
      apply mul_le_mul_of_nonneg_right _ hC
      simpa only [Row.haarB, ite_true] using
        haarMode_le_sqrt_sq (row.Lcirc + (row.qs - 1) * minSeries row.qs row.Rcirc row.Hcirc)

/-- H10 with the exact intermediate statement statement, using the proved sharp cell inequality. -/
theorem haar_constant_mode_proof (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ))
    (hO : row.Obligations) (n : ℕ) (a : Homogenization.Vec d) :
    haarPrimal (originCube d (n : ℤ)) row.qs (fun x =>
        (vecDot a x - cubeAverage (originCube d (n : ℤ)) (fun y => vecDot a y)) •
          cubeCutoffGrad row n x) ≤
      ENNReal.ofReal (row.haarB 0 ^ 2 * vecNormSq a) := by
  exact haar_constant_mode_of_cellPoincare cell_poincare_proof row hd hO n a

end GMCExplicitDelta.Localization
