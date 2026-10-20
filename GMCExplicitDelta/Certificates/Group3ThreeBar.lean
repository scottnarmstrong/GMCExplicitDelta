module

public import GMCExplicitDelta.Certificates.Group3Barrier
public import GMCExplicitDelta.Certificates.Group3ThreeGeo

/-!
# Numeric obligations, group 3, row `rowThree`: the barrier

O.bar.1 (and, for `d = 2`, O.bar.2) for `rowThree` from the certified majorants of the Geo file.
-/

@[expose] public section

open Real

namespace GMCExplicitDelta.Certificates.G3.Three

open GMCExplicitDelta.Contract GMCExplicitDelta.Haar GMCExplicitDelta.Certificates.G3

theorem hZ0 : (0 : ℝ) < (rowThree.Z : ℝ) := by norm_num [rowThree]
theorem hZM : (rowThree.Z : ℝ) < (rowThree.Mwin : ℝ) := by norm_num [Row.Mwin, rowThree]
theorem ht1 : rowThree.tStar ≤ 1 := by
  unfold Row.tStar
  rw [div_le_one (by norm_num [Row.Mwin, rowThree])]
  exact hZM.le

theorem hq0 : 0 ≤ rowThree.qStar ((rowThree.F : ℚ) : ℝ) := by
  norm_num [Row.qStar]

theorem sigmas : True := trivial

/-- The coefficient bounds of the barrier. -/
theorem coef_bounds :
    (0 ≤ rowThree.coefA ((rowThree.F : ℚ) : ℝ) ∧ rowThree.coefA ((rowThree.F : ℚ) : ℝ) ≤ ((5770155511063 : ℝ) / 1000000000000)) ∧
    (0 ≤ rowThree.coefAv ∧ rowThree.coefAv ≤ ((3651684934083 : ℝ) / 1000000000000)) ∧
    (0 ≤ rowThree.coefB ((rowThree.F : ℚ) : ℝ) ∧ rowThree.coefB ((rowThree.F : ℚ) : ℝ) ≤ ((6115575197809 : ℝ) / 200000000000)) := by
  obtain ⟨hcl, hcu⟩ := cNu_bounds
  have hclp : (0 : ℝ) < ((4158388118537 : ℝ) / 10000000000000) := by norm_num
  have hε0 : (0 : ℝ) ≤ (rowThree.epsilon : ℝ) := by norm_num [rowThree]
  have hε1 : (0 : ℝ) < (rowThree.epsilon : ℝ) := by norm_num [rowThree]
  have hR0 : (0 : ℝ) ≤ (rowThree.R : ℝ) := by norm_num [rowThree]
  have eA : sigmaA 3 ((rowThree.F : ℚ) : ℝ) = √(1 + 2 * ((rowThree.F : ℚ) : ℝ)) := sigmaA_of_ne (by norm_num)
  have eV : sigmaV 3 = √2 := sigmaV_of_ne (by norm_num)
  have eB : sigmaB 3 ((rowThree.F : ℚ) : ℝ) = 1 + 2 * ((rowThree.F : ℚ) : ℝ) := sigmaB_of_ne (by norm_num)
  have hσA0 : 0 ≤ sigmaA 3 ((rowThree.F : ℚ) : ℝ) := by rw [eA]; exact Real.sqrt_nonneg _
  have hσA : sigmaA 3 ((rowThree.F : ℚ) : ℝ) ≤ ((4659593493 : ℝ) / 4000000000) := by
    rw [eA]; exact Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num [rowThree]⟩
  have hσV0 : 0 ≤ sigmaV 3 := by rw [eV]; exact Real.sqrt_nonneg _
  have hσV : sigmaV 3 ≤ ((707106781187 : ℝ) / 500000000000) := by
    rw [eV]; exact Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  have hσB0 : 0 ≤ sigmaB 3 ((rowThree.F : ℚ) : ℝ) := by rw [eB]; norm_num [rowThree]
  have hσB : sigmaB 3 ((rowThree.F : ℚ) : ℝ) ≤ 1 + 2 * ((rowThree.F : ℚ) : ℝ) := by rw [eB]
  have hs2R : √(2 * (rowThree.R : ℝ)) ≤ ((479580135379 : ℝ) / 250000000000) :=
    Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num [rowThree]⟩
  refine ⟨coefA_enc rowThree (F := ((rowThree.F : ℚ) : ℝ)) (cl := ((4158388118537 : ℝ) / 10000000000000)) (σu := ((4659593493 : ℝ) / 4000000000)) hclp hcl hσA0 hσA hε0 hR0
      (by norm_num [rowThree]),
    coefAv_enc rowThree (cl := ((4158388118537 : ℝ) / 10000000000000)) (σu := ((707106781187 : ℝ) / 500000000000)) hclp hcl hs2R hσV0 hσV hε0
      (by norm_num [rowThree]),
    coefB_enc rowThree (F := ((rowThree.F : ℚ) : ℝ)) (cl := ((4158388118537 : ℝ) / 10000000000000)) (σu := (1 + 2 * ((rowThree.F : ℚ) : ℝ))) hclp hcl hσB0 hσB hε1
      (by norm_num [rowThree])⟩

theorem Btail_bound : 0 ≤ rowThree.Btail ∧ rowThree.Btail ≤ ((589683 : ℝ) / 100000000000000000000) := by
  have h := Btail_le rowThree (uu := uU) (Ksu := Ksu) Ks_le us_bounds.2 huU3
  exact ⟨h.1, h.2.trans (by norm_num [Row.Kprime, rowThree, Ksu, uU])⟩

theorem bar1_pos : 0 < rowThree.barrier rowThree.D rowThree.F := by
  obtain ⟨hA, hAv, hB⟩ := coef_bounds
  have hBt := Btail_bound
  have h1 : √(1 - rowThree.tStar) ≤ ((436811075481 : ℝ) / 1000000000000) :=
    Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num [Row.tStar, Row.Mwin, rowThree]⟩
  have h2 : √(rowThree.qStar ((rowThree.F : ℚ) : ℝ)) ≤ (1 : ℝ) :=
    Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num [Row.qStar, qMatch, cMatch, rMatch, Row.uStar, Row.tStar, Row.Mwin, rowThree]⟩
  have hri : (√(rowThree.rStar ((rowThree.F : ℚ) : ℝ)))⁻¹ ≤ (1 : ℝ) :=
    inv_sqrt_le (rl := (1 : ℝ)) (by norm_num) (by norm_num [Row.rStar, rMatch, Row.uStar, Row.tStar, Row.Mwin, rowThree]) (by norm_num)
  have hx : √(rowThree.Qt0 ((rowThree.D : ℚ) : ℝ) ((rowThree.F : ℚ) : ℝ) + rowThree.Qfor ((rowThree.F : ℚ) : ℝ) * (1 - rowThree.tStar ^ 2)) ≤ ((448039401551 : ℝ) / 1000000000000) :=
    Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num [Row.Qt0, Row.Qf0, Row.Qfor, vi, ellV, Row.rhoV, Row.jV, Row.cV, Row.tStar, Row.Mwin, rowThree]⟩
  have hy : √(rowThree.Qf0 ((rowThree.D : ℚ) : ℝ) ((rowThree.F : ℚ) : ℝ) + rowThree.Qfor ((rowThree.F : ℚ) : ℝ) * (1 - rowThree.tStar ^ 2)) ≤ ((5376038329 : ℝ) / 312500000) :=
    Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num [Row.Qt0, Row.Qf0, Row.Qfor, vi, ellV, Row.rhoV, Row.jV, Row.cV, Row.tStar, Row.Mwin, rowThree]⟩
  have hC := Cbar_le rowThree ((rowThree.D : ℚ) : ℝ) ((rowThree.F : ℚ) : ℝ) hA.1 hA.2 Sd_le h1 h2 hAv.1 hAv.2 hri Sb_le hx hBt.1 hBt.2 hy
  have hz : √(rowThree.Z : ℝ) ≤ ((8195320311007 : ℝ) / 500000000000) :=
    Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num [rowThree]⟩
  have hb := barrier_ge rowThree ((rowThree.D : ℚ) : ℝ) ((rowThree.F : ℚ) : ℝ) hZ0.le tau_bound.2 hC.1 hC.2 hz hB.2 ht1 hq0
  refine lt_of_lt_of_le ?_ hb
  norm_num [Row.qStar, qMatch, cMatch, rMatch, Row.uStar, Row.tStar, Row.Mwin, rowThree, Row.Qt0, Row.Qfor, Row.rStar, Row.rhoV, Row.jV, Row.cV, Ksu, SbU, SdU, Row.Qf0, vi, ellV, Row.rhoV]

theorem bar1 : 0 < (rowThree.Z : ℝ) ∧ (rowThree.Z : ℝ) < (rowThree.Mwin : ℝ) ∧
    0 < rowThree.barrier rowThree.D rowThree.F := ⟨hZ0, hZM, bar1_pos⟩

end GMCExplicitDelta.Certificates.G3.Three
