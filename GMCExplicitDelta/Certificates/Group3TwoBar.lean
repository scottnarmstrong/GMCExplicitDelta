module

public import GMCExplicitDelta.Certificates.Group3Barrier
public import GMCExplicitDelta.Certificates.Group3TwoGeo

/-!
# Numeric obligations, group 3, row `rowTwo`: the barrier

O.bar.1 (and, for `d = 2`, O.bar.2) for `rowTwo` from the certified majorants of the Geo file.
-/

@[expose] public section

open Real

namespace GMCExplicitDelta.Certificates.G3.Two

open GMCExplicitDelta.Contract GMCExplicitDelta.Haar GMCExplicitDelta.Certificates.G3

theorem hZ0 : (0 : ℝ) < (rowTwo.Z : ℝ) := by norm_num [rowTwo]
theorem hZM : (rowTwo.Z : ℝ) < (rowTwo.Mwin : ℝ) := by norm_num [Row.Mwin, rowTwo]
theorem ht1 : rowTwo.tStar ≤ 1 := by
  unfold Row.tStar
  rw [div_le_one (by norm_num [Row.Mwin, rowTwo])]
  exact hZM.le

theorem hq0 : 0 ≤ rowTwo.qStar ((rowTwo.F : ℚ) : ℝ) := by
  unfold Row.qStar; simp only [↓reduceIte]
  exact (qMatch_pos (by norm_num [Row.uStar, Row.tStar, Row.Mwin, rowTwo])).le

theorem sigmas : True := trivial

/-- The coefficient bounds of the barrier. -/
theorem coef_bounds :
    (0 ≤ rowTwo.coefA ((rowTwo.F : ℚ) : ℝ) ∧ rowTwo.coefA ((rowTwo.F : ℚ) : ℝ) ≤ ((7900571147487 : ℝ) / 1000000000000)) ∧
    (0 ≤ rowTwo.coefAv ∧ rowTwo.coefAv ≤ ((1659026274469 : ℝ) / 500000000000)) ∧
    (0 ≤ rowTwo.coefB ((rowTwo.F : ℚ) : ℝ) ∧ rowTwo.coefB ((rowTwo.F : ℚ) : ℝ) ≤ ((12124946728957 : ℝ) / 500000000000)) := by
  obtain ⟨hcl, hcu⟩ := cNu_bounds
  have hclp : (0 : ℝ) < ((20002258765469 : ℝ) / 50000000000000) := by norm_num
  have hε0 : (0 : ℝ) ≤ (rowTwo.epsilon : ℝ) := by norm_num [rowTwo]
  have hε1 : (0 : ℝ) < (rowTwo.epsilon : ℝ) := by norm_num [rowTwo]
  have hR0 : (0 : ℝ) ≤ (rowTwo.R : ℝ) := by norm_num [rowTwo]
  have eA : sigmaA 2 ((rowTwo.F : ℚ) : ℝ) = 1 := sigmaA_of_eq rfl
  have eV : sigmaV 2 = 1 := sigmaV_of_eq rfl
  have eB : sigmaB 2 ((rowTwo.F : ℚ) : ℝ) = 1 := sigmaB_of_eq rfl
  have hσA0 : 0 ≤ sigmaA 2 ((rowTwo.F : ℚ) : ℝ) := by rw [eA]; norm_num
  have hσA : sigmaA 2 ((rowTwo.F : ℚ) : ℝ) ≤ 1 := by rw [eA]
  have hσV0 : 0 ≤ sigmaV 2 := by rw [eV]; norm_num
  have hσV : sigmaV 2 ≤ 1 := by rw [eV]
  have hσB0 : 0 ≤ sigmaB 2 ((rowTwo.F : ℚ) : ℝ) := by rw [eB]; norm_num
  have hσB : sigmaB 2 ((rowTwo.F : ℚ) : ℝ) ≤ 1 := by rw [eB]
  have hs2R : √(2 * (rowTwo.R : ℝ)) ≤ ((1190543403241 : ℝ) / 500000000000) :=
    Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num [rowTwo]⟩
  refine ⟨coefA_enc rowTwo (F := ((rowTwo.F : ℚ) : ℝ)) (cl := ((20002258765469 : ℝ) / 50000000000000)) (σu := 1) hclp hcl hσA0 hσA hε0 hR0
      (by norm_num [rowTwo]),
    coefAv_enc rowTwo (cl := ((20002258765469 : ℝ) / 50000000000000)) (σu := 1) hclp hcl hs2R hσV0 hσV hε0
      (by norm_num [rowTwo]),
    coefB_enc rowTwo (F := ((rowTwo.F : ℚ) : ℝ)) (cl := ((20002258765469 : ℝ) / 50000000000000)) (σu := 1) hclp hcl hσB0 hσB hε1
      (by norm_num [rowTwo])⟩

theorem Btail_bound : 0 ≤ rowTwo.Btail ∧ rowTwo.Btail ≤ ((54403 : ℝ) / 5000000000000000) := by
  have h := Btail_le rowTwo (uu := uU) (Ksu := Ksu) Ks_le us_bounds.2 huU3
  exact ⟨h.1, h.2.trans (by norm_num [Row.Kprime, rowTwo, Ksu, uU])⟩

theorem bar1_pos : 0 < rowTwo.barrier rowTwo.D rowTwo.F := by
  obtain ⟨hA, hAv, hB⟩ := coef_bounds
  have hBt := Btail_bound
  have h1 : √(1 - rowTwo.tStar) ≤ ((82181018531 : ℝ) / 200000000000) :=
    Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num [Row.tStar, Row.Mwin, rowTwo]⟩
  have h2 : √(rowTwo.qStar ((rowTwo.F : ℚ) : ℝ)) ≤ ((932382284681 : ℝ) / 1000000000000) :=
    Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num [Row.qStar, qMatch, cMatch, rMatch, Row.uStar, Row.tStar, Row.Mwin, rowTwo]⟩
  have hri : (√(rowTwo.rStar ((rowTwo.F : ℚ) : ℝ)))⁻¹ ≤ ((29540582011 : ℝ) / 40000000000) :=
    inv_sqrt_le (rl := ((169258682789 : ℝ) / 125000000000)) (by norm_num) (by norm_num [Row.rStar, rMatch, Row.uStar, Row.tStar, Row.Mwin, rowTwo]) (by norm_num)
  have hx : √(rowTwo.Qt0 ((rowTwo.D : ℚ) : ℝ) ((rowTwo.F : ℚ) : ℝ) + rowTwo.Qfor ((rowTwo.F : ℚ) : ℝ) * (1 - rowTwo.tStar ^ 2)) ≤ ((862873190361 : ℝ) / 1000000000000) :=
    Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num [Row.Qt0, Row.Qf0, Row.Qfor, vi, ellV, Row.rhoV, Row.jV, Row.cV, Row.tStar, Row.Mwin, rowTwo]⟩
  have hy : √(rowTwo.Qf0 ((rowTwo.D : ℚ) : ℝ) ((rowTwo.F : ℚ) : ℝ) + rowTwo.Qfor ((rowTwo.F : ℚ) : ℝ) * (1 - rowTwo.tStar ^ 2)) ≤ ((2872662477 : ℝ) / 12500000) :=
    Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num [Row.Qt0, Row.Qf0, Row.Qfor, vi, ellV, Row.rhoV, Row.jV, Row.cV, Row.tStar, Row.Mwin, rowTwo]⟩
  have hC := Cbar_le rowTwo ((rowTwo.D : ℚ) : ℝ) ((rowTwo.F : ℚ) : ℝ) hA.1 hA.2 Sd_le h1 h2 hAv.1 hAv.2 hri Sb_le hx hBt.1 hBt.2 hy
  have hz : √(rowTwo.Z : ℝ) ≤ ((6558382041327 : ℝ) / 500000000000) :=
    Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num [rowTwo]⟩
  have hb := barrier_ge rowTwo ((rowTwo.D : ℚ) : ℝ) ((rowTwo.F : ℚ) : ℝ) hZ0.le tau_bound.2 hC.1 hC.2 hz hB.2 ht1 hq0
  refine lt_of_lt_of_le ?_ hb
  norm_num [Row.qStar, qMatch, cMatch, rMatch, Row.uStar, Row.tStar, Row.Mwin, rowTwo, Row.Qt0, Row.Qfor, Row.rStar, Row.rhoV, Row.jV, Row.cV, Ksu, SbU, SdU, Row.Qf0, vi, ellV, Row.rhoV]

theorem bar1 : 0 < (rowTwo.Z : ℝ) ∧ (rowTwo.Z : ℝ) < (rowTwo.Mwin : ℝ) ∧
    0 < rowTwo.barrier rowTwo.D rowTwo.F := ⟨hZ0, hZM, bar1_pos⟩

/-! ### O.bar.2 (planar derivative test) -/

theorem hX : 0 ≤ rowTwo.Qt0 ((rowTwo.D : ℚ) : ℝ) ((rowTwo.F : ℚ) : ℝ) + rowTwo.Qfor ((rowTwo.F : ℚ) : ℝ) * (1 - rowTwo.tStar ^ 2) := by
  norm_num [Row.Qt0, Row.Qf0, Row.Qfor, vi, ellV, Row.rhoV, Row.jV, Row.cV, Row.tStar, Row.Mwin, rowTwo]

theorem hY : 0 ≤ rowTwo.Qf0 ((rowTwo.D : ℚ) : ℝ) ((rowTwo.F : ℚ) : ℝ) + rowTwo.Qfor ((rowTwo.F : ℚ) : ℝ) * (1 - rowTwo.tStar ^ 2) := by
  norm_num [Row.Qt0, Row.Qf0, Row.Qfor, vi, ellV, Row.rhoV, Row.jV, Row.cV, Row.tStar, Row.Mwin, rowTwo]

theorem bar2_nt : 0 ≤ nMatch rowTwo.vT0 (rowTwo.vT1 ((rowTwo.D : ℚ) : ℝ) ((rowTwo.F : ℚ) : ℝ)) (rowTwo.uStar ((rowTwo.F : ℚ) : ℝ)) := by
  norm_num [nMatch, Row.vT0, Row.vT1, Row.vF0, Row.vF1, Row.Qt0, Row.Qf0, Row.Qfor, vi, ellV, Row.rhoV, Row.jV, Row.cV, Row.uStar, Row.tStar, Row.Mwin, rowTwo]

theorem bar2_nf : 0 ≤ nMatch rowTwo.vF0 (rowTwo.vF1 ((rowTwo.D : ℚ) : ℝ) ((rowTwo.F : ℚ) : ℝ)) (rowTwo.uStar ((rowTwo.F : ℚ) : ℝ)) := by
  norm_num [nMatch, Row.vT0, Row.vT1, Row.vF0, Row.vF1, Row.Qt0, Row.Qf0, Row.Qfor, vi, ellV, Row.rhoV, Row.jV, Row.cV, Row.uStar, Row.tStar, Row.Mwin, rowTwo]

theorem Sb_ge : ((1311695207723 : ℝ) / 1000000000000) ≤ rowTwo.Sb := by
  have hsum := haar_hyps_summable rowTwo hq1 hq9 hu3 haar_hyps.1 haar_hyps.2
  have h := Sb_ge_two rowTwo hsum
  have b0 : ((16031872877 : ℝ) / 25000000000) ≤ rowTwo.haarB 0 :=
    le_trans (Real.le_sqrt_of_sq_le (le_trans (by norm_num) Lc_bounds.1))
      (haarB0_ge_sqrt rowTwo hq1 hR0 hH0)
  have b1 : ((670420292643 : ℝ) / 1000000000000) ≤ rowTwo.haarB 1 :=
    le_trans (Real.le_sqrt_of_sq_le (le_trans (by norm_num [PH]) (haarL_one_ge rowTwo pi_le_PH)))
      (haarB_ge_sqrt rowTwo (le_refl 1) hq1)
  linarith

theorem bar2_loss : rowTwo.t4Loss ((rowTwo.F : ℚ) : ℝ) ≤
    rowTwo.t4b * mMatch rowTwo.vT0 (rowTwo.vT1 ((rowTwo.D : ℚ) : ℝ) ((rowTwo.F : ℚ) : ℝ)) (rowTwo.uStar ((rowTwo.F : ℚ) : ℝ)) +
      rowTwo.t4c * mMatch rowTwo.vF0 (rowTwo.vF1 ((rowTwo.D : ℚ) : ℝ) ((rowTwo.F : ℚ) : ℝ)) (rowTwo.uStar ((rowTwo.F : ℚ) : ℝ)) := by
  obtain ⟨hA, hAv, hB⟩ := coef_bounds
  have hBt := Btail_bound
  obtain ⟨hcl, hcu⟩ := cNu_bounds
  have hε0 : (0 : ℝ) ≤ (rowTwo.epsilon : ℝ) := by norm_num [rowTwo]
  have hc0 : 0 < rowTwo.cNu := lt_of_lt_of_le (by norm_num) hcl
  have hu0 : 0 ≤ rowTwo.uStar ((rowTwo.F : ℚ) : ℝ) := by norm_num [Row.uStar, Row.tStar, Row.Mwin, rowTwo]
  have hu1 : (rowTwo.uStar ((rowTwo.F : ℚ) : ℝ)) ^ 2 / 2 ≤ 1 := by norm_num [Row.uStar, Row.tStar, Row.Mwin, rowTwo]
  have h1 : √(1 - rowTwo.tStar) ≤ ((82181018531 : ℝ) / 200000000000) :=
    Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num [Row.tStar, Row.Mwin, rowTwo]⟩
  have ha := t4a_le rowTwo ((rowTwo.F : ℚ) : ℝ) hA.1 hA.2 Sd_le h1
  have ha0 : 0 ≤ rowTwo.t4a ((rowTwo.F : ℚ) : ℝ) := by
    unfold Row.t4a
    exact mul_nonneg (mul_nonneg hA.1 (Sd_nonneg _)) (Real.sqrt_nonneg _)
  have hzl : ((13116764082653 : ℝ) / 1000000000000) ≤ √(rowTwo.Z : ℝ) :=
    Real.le_sqrt_of_sq_le (by norm_num [rowTwo])
  have hL := t4L_le rowTwo ((rowTwo.F : ℚ) : ℝ) hB.1 hB.2 ht1 (by norm_num) hzl
  have hql : ((23309557117 : ℝ) / 25000000000) ≤ √(qMatch (rowTwo.uStar ((rowTwo.F : ℚ) : ℝ))) :=
    Real.le_sqrt_of_sq_le (by norm_num [qMatch, cMatch, rMatch, Row.uStar, Row.tStar, Row.Mwin, rowTwo])
  have hloss := t4Loss_le rowTwo ((rowTwo.F : ℚ) : ℝ) hu0 hu1 ha0 ha hL.2 (by norm_num) hql
  have hsx : √(rowTwo.vT0 + rowTwo.vT1 ((rowTwo.D : ℚ) : ℝ) ((rowTwo.F : ℚ) : ℝ)) ≤ ((862873190361 : ℝ) / 1000000000000) :=
    Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num [nMatch, Row.vT0, Row.vT1, Row.vF0, Row.vF1, Row.Qt0, Row.Qf0, Row.Qfor, vi, ellV, Row.rhoV, Row.jV, Row.cV, Row.uStar, Row.tStar, Row.Mwin, rowTwo]⟩
  have hsr : √(rMatch (rowTwo.uStar ((rowTwo.F : ℚ) : ℝ))) ≤ ((1354069462313 : ℝ) / 1000000000000) :=
    Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num [rMatch, Row.uStar, Row.tStar, Row.Mwin, rowTwo]⟩
  have hv : 0 < rowTwo.vT0 + rowTwo.vT1 ((rowTwo.D : ℚ) : ℝ) ((rowTwo.F : ℚ) : ℝ) := by norm_num [nMatch, Row.vT0, Row.vT1, Row.vF0, Row.vF1, Row.Qt0, Row.Qf0, Row.Qfor, vi, ellV, Row.rhoV, Row.jV, Row.cV, Row.uStar, Row.tStar, Row.Mwin, rowTwo]
  have hmt := mMatch_ge bar2_nt hv hu0 hsx hsr
  have hmt' : ((76914894317 : ℝ) / 500000000000) ≤ nMatch rowTwo.vT0 (rowTwo.vT1 ((rowTwo.D : ℚ) : ℝ) ((rowTwo.F : ℚ) : ℝ)) (rowTwo.uStar ((rowTwo.F : ℚ) : ℝ)) /
      (2 * ((862873190361 : ℝ) / 1000000000000) * (rMatch (rowTwo.uStar ((rowTwo.F : ℚ) : ℝ)) * ((1354069462313 : ℝ) / 1000000000000))) := by
    norm_num [nMatch, Row.vT0, Row.vT1, Row.vF0, Row.vF1, Row.Qt0, Row.Qf0, Row.Qfor, vi, ellV, Row.rhoV, Row.jV, Row.cV, Row.uStar, Row.tStar, Row.Mwin, rowTwo, rMatch]
  have hmf := mMatch_nonneg bar2_nf hu0
  have hAvl : ((414756568617 : ℝ) / 125000000000) ≤ rowTwo.coefAv :=
    coefAv_lower rowTwo (cu := ((2000225876547 : ℝ) / 5000000000000)) (s2Rl := ((2381086806481 : ℝ) / 1000000000000)) (σl := 1) hcu hc0
      (Real.le_sqrt_of_sq_le (by norm_num [rowTwo])) (by norm_num) (by rw [sigmaV_of_eq rfl])
      hε0 (by norm_num [rowTwo])
  have hb : ((414756568617 : ℝ) / 125000000000) * ((1311695207723 : ℝ) / 1000000000000) ≤ rowTwo.t4b := by
    unfold Row.t4b
    exact mul_le_mul hAvl Sb_ge (by norm_num) (hAv.1)
  have hc : 0 ≤ rowTwo.t4c := by
    unfold Row.t4c
    exact mul_nonneg hAv.1 hBt.1
  have hmt0 : 0 ≤ ((76914894317 : ℝ) / 500000000000) := by norm_num
  have e1 : ((414756568617 : ℝ) / 125000000000) * ((1311695207723 : ℝ) / 1000000000000) * ((76914894317 : ℝ) / 500000000000) ≤
      rowTwo.t4b * mMatch rowTwo.vT0 (rowTwo.vT1 ((rowTwo.D : ℚ) : ℝ) ((rowTwo.F : ℚ) : ℝ)) (rowTwo.uStar ((rowTwo.F : ℚ) : ℝ)) :=
    mul_le_mul hb (hmt'.trans hmt) hmt0 (le_trans (by norm_num) hb)
  have e2 : 0 ≤ rowTwo.t4c * mMatch rowTwo.vF0 (rowTwo.vF1 ((rowTwo.D : ℚ) : ℝ) ((rowTwo.F : ℚ) : ℝ)) (rowTwo.uStar ((rowTwo.F : ℚ) : ℝ)) := mul_nonneg hc hmf
  refine hloss.trans (le_trans ?_ (e1.trans (le_add_of_nonneg_right e2)))
  norm_num [Row.qStar, qMatch, cMatch, rMatch, Row.uStar, Row.tStar, Row.Mwin, rowTwo, Row.Qt0, Row.Qfor, Row.rhoV, Row.jV, Row.cV, SdU]

theorem bar2_margin' : 0 < (1 - rowTwo.tauAbs) * √(rowTwo.Z : ℝ) - rowTwo.t4R ((rowTwo.D : ℚ) : ℝ) ((rowTwo.F : ℚ) : ℝ) 1 -
    (rowTwo.Mwin : ℝ) * (rowTwo.badBudget : ℝ) / √(rowTwo.Z : ℝ) :=
  bar2_margin rowTwo ((rowTwo.D : ℚ) : ℝ) ((rowTwo.F : ℚ) : ℝ) hZ0 hX hY bar1_pos

theorem bar2 : 2 = 2 →
    0 ≤ nMatch rowTwo.vT0 (rowTwo.vT1 ((rowTwo.D : ℚ) : ℝ) ((rowTwo.F : ℚ) : ℝ)) (rowTwo.uStar ((rowTwo.F : ℚ) : ℝ)) ∧
    0 ≤ nMatch rowTwo.vF0 (rowTwo.vF1 ((rowTwo.D : ℚ) : ℝ) ((rowTwo.F : ℚ) : ℝ)) (rowTwo.uStar ((rowTwo.F : ℚ) : ℝ)) ∧
    rowTwo.t4Loss ((rowTwo.F : ℚ) : ℝ) ≤
      rowTwo.t4b * mMatch rowTwo.vT0 (rowTwo.vT1 ((rowTwo.D : ℚ) : ℝ) ((rowTwo.F : ℚ) : ℝ)) (rowTwo.uStar ((rowTwo.F : ℚ) : ℝ)) +
        rowTwo.t4c * mMatch rowTwo.vF0 (rowTwo.vF1 ((rowTwo.D : ℚ) : ℝ) ((rowTwo.F : ℚ) : ℝ)) (rowTwo.uStar ((rowTwo.F : ℚ) : ℝ)) ∧
    0 < (1 - rowTwo.tauAbs) * √(rowTwo.Z : ℝ) - rowTwo.t4R ((rowTwo.D : ℚ) : ℝ) ((rowTwo.F : ℚ) : ℝ) 1 -
      (rowTwo.Mwin : ℝ) * (rowTwo.badBudget : ℝ) / √(rowTwo.Z : ℝ) :=
  fun _ => ⟨bar2_nt, bar2_nf, bar2_loss, bar2_margin'⟩

end GMCExplicitDelta.Certificates.G3.Two
