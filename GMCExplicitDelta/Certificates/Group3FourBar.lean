module

public import GMCExplicitDelta.Certificates.Group3Barrier
public import GMCExplicitDelta.Certificates.Group3FourGeo

/-!
# Numeric obligations, group 3, row `rowFour`: the barrier

O.bar.1 (and, for `d = 2`, O.bar.2) for `rowFour` from the certified majorants of the Geo file.
-/

@[expose] public section

open Real

namespace GMCExplicitDelta.Certificates.G3.Four

open GMCExplicitDelta.Contract GMCExplicitDelta.Haar GMCExplicitDelta.Certificates.G3

theorem hZ0 : (0 : ℝ) < (rowFour.Z : ℝ) := by norm_num [rowFour]
theorem hZM : (rowFour.Z : ℝ) < (rowFour.Mwin : ℝ) := by norm_num [Row.Mwin, rowFour]
theorem ht1 : rowFour.tStar ≤ 1 := by
  unfold Row.tStar
  rw [div_le_one (by norm_num [Row.Mwin, rowFour])]
  exact hZM.le

theorem hq0 : 0 ≤ rowFour.qStar ((rowFour.F : ℚ) : ℝ) := by
  norm_num [Row.qStar]

theorem sigmas : True := trivial

/-- The coefficient bounds of the barrier. -/
theorem coef_bounds :
    (0 ≤ rowFour.coefA ((rowFour.F : ℚ) : ℝ) ∧ rowFour.coefA ((rowFour.F : ℚ) : ℝ) ≤ ((5576500868191 : ℝ) / 1000000000000)) ∧
    (0 ≤ rowFour.coefAv ∧ rowFour.coefAv ≤ ((3585246231323 : ℝ) / 1000000000000)) ∧
    (0 ≤ rowFour.coefB ((rowFour.F : ℚ) : ℝ) ∧ rowFour.coefB ((rowFour.F : ℚ) : ℝ) ≤ ((7256730596581 : ℝ) / 200000000000)) := by
  obtain ⟨hcl, hcu⟩ := cNu_bounds
  have hclp : (0 : ℝ) < ((10295826280197 : ℝ) / 25000000000000) := by norm_num
  have hε0 : (0 : ℝ) ≤ (rowFour.epsilon : ℝ) := by norm_num [rowFour]
  have hε1 : (0 : ℝ) < (rowFour.epsilon : ℝ) := by norm_num [rowFour]
  have hR0 : (0 : ℝ) ≤ (rowFour.R : ℝ) := by norm_num [rowFour]
  have eA : sigmaA 4 ((rowFour.F : ℚ) : ℝ) = √(1 + 2 * ((rowFour.F : ℚ) : ℝ)) := sigmaA_of_ne (by norm_num)
  have eV : sigmaV 4 = √2 := sigmaV_of_ne (by norm_num)
  have eB : sigmaB 4 ((rowFour.F : ℚ) : ℝ) = 1 + 2 * ((rowFour.F : ℚ) : ℝ) := sigmaB_of_ne (by norm_num)
  have hσA0 : 0 ≤ sigmaA 4 ((rowFour.F : ℚ) : ℝ) := by rw [eA]; exact Real.sqrt_nonneg _
  have hσA : sigmaA 4 ((rowFour.F : ℚ) : ℝ) ≤ ((1157098716619 : ℝ) / 1000000000000) := by
    rw [eA]; exact Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num [rowFour]⟩
  have hσV0 : 0 ≤ sigmaV 4 := by rw [eV]; exact Real.sqrt_nonneg _
  have hσV : sigmaV 4 ≤ ((707106781187 : ℝ) / 500000000000) := by
    rw [eV]; exact Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  have hσB0 : 0 ≤ sigmaB 4 ((rowFour.F : ℚ) : ℝ) := by rw [eB]; norm_num [rowFour]
  have hσB : sigmaB 4 ((rowFour.F : ℚ) : ℝ) ≤ 1 + 2 * ((rowFour.F : ℚ) : ℝ) := by rw [eB]
  have hs2R : √(2 * (rowFour.R : ℝ)) ≤ ((237627875443 : ℝ) / 125000000000) :=
    Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num [rowFour]⟩
  refine ⟨coefA_enc rowFour (F := ((rowFour.F : ℚ) : ℝ)) (cl := ((10295826280197 : ℝ) / 25000000000000)) (σu := ((1157098716619 : ℝ) / 1000000000000)) hclp hcl hσA0 hσA hε0 hR0
      (by norm_num [rowFour]),
    coefAv_enc rowFour (cl := ((10295826280197 : ℝ) / 25000000000000)) (σu := ((707106781187 : ℝ) / 500000000000)) hclp hcl hs2R hσV0 hσV hε0
      (by norm_num [rowFour]),
    coefB_enc rowFour (F := ((rowFour.F : ℚ) : ℝ)) (cl := ((10295826280197 : ℝ) / 25000000000000)) (σu := (1 + 2 * ((rowFour.F : ℚ) : ℝ))) hclp hcl hσB0 hσB hε1
      (by norm_num [rowFour])⟩

theorem Btail_bound : 0 ≤ rowFour.Btail ∧ rowFour.Btail ≤ ((36847 : ℝ) / 25000000000000000000000) := by
  have h := Btail_le rowFour (uu := uU) (Ksu := Ksu) Ks_le us_bounds.2 huU3
  exact ⟨h.1, h.2.trans (by norm_num [Row.Kprime, rowFour, Ksu, uU])⟩

theorem bar1_pos : 0 < rowFour.barrier rowFour.D rowFour.F := by
  obtain ⟨hA, hAv, hB⟩ := coef_bounds
  have hBt := Btail_bound
  have h1 : √(1 - rowFour.tStar) ≤ ((26915166013 : ℝ) / 62500000000) :=
    Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num [Row.tStar, Row.Mwin, rowFour]⟩
  have h2 : √(rowFour.qStar ((rowFour.F : ℚ) : ℝ)) ≤ (1 : ℝ) :=
    Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num [Row.qStar, qMatch, cMatch, rMatch, Row.uStar, Row.tStar, Row.Mwin, rowFour]⟩
  have hri : (√(rowFour.rStar ((rowFour.F : ℚ) : ℝ)))⁻¹ ≤ (1 : ℝ) :=
    inv_sqrt_le (rl := (1 : ℝ)) (by norm_num) (by norm_num [Row.rStar, rMatch, Row.uStar, Row.tStar, Row.Mwin, rowFour]) (by norm_num)
  have hx : √(rowFour.Qt0 ((rowFour.D : ℚ) : ℝ) ((rowFour.F : ℚ) : ℝ) + rowFour.Qfor ((rowFour.F : ℚ) : ℝ) * (1 - rowFour.tStar ^ 2)) ≤ ((375277483609 : ℝ) / 1000000000000) :=
    Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num [Row.Qt0, Row.Qf0, Row.Qfor, vi, ellV, Row.rhoV, Row.jV, Row.cV, Row.tStar, Row.Mwin, rowFour]⟩
  have hy : √(rowFour.Qf0 ((rowFour.D : ℚ) : ℝ) ((rowFour.F : ℚ) : ℝ) + rowFour.Qfor ((rowFour.F : ℚ) : ℝ) * (1 - rowFour.tStar ^ 2)) ≤ ((74099376991 : ℝ) / 5000000000) :=
    Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num [Row.Qt0, Row.Qf0, Row.Qfor, vi, ellV, Row.rhoV, Row.jV, Row.cV, Row.tStar, Row.Mwin, rowFour]⟩
  have hC := Cbar_le rowFour ((rowFour.D : ℚ) : ℝ) ((rowFour.F : ℚ) : ℝ) hA.1 hA.2 Sd_le h1 h2 hAv.1 hAv.2 hri Sb_le hx hBt.1 hBt.2 hy
  have hz : √(rowFour.Z : ℝ) ≤ ((959394600777 : ℝ) / 50000000000) :=
    Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num [rowFour]⟩
  have hb := barrier_ge rowFour ((rowFour.D : ℚ) : ℝ) ((rowFour.F : ℚ) : ℝ) hZ0.le tau_bound.2 hC.1 hC.2 hz hB.2 ht1 hq0
  refine lt_of_lt_of_le ?_ hb
  norm_num [Row.qStar, qMatch, cMatch, rMatch, Row.uStar, Row.tStar, Row.Mwin, rowFour, Row.Qt0, Row.Qfor, Row.rStar, Row.rhoV, Row.jV, Row.cV, Ksu, SbU, SdU, Row.Qf0, vi, ellV, Row.rhoV]

theorem bar1 : 0 < (rowFour.Z : ℝ) ∧ (rowFour.Z : ℝ) < (rowFour.Mwin : ℝ) ∧
    0 < rowFour.barrier rowFour.D rowFour.F := ⟨hZ0, hZM, bar1_pos⟩

end GMCExplicitDelta.Certificates.G3.Four
