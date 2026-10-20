module

public import GMCExplicitDelta.HistoryLane.Levels
public import GMCExplicitDelta.HistoryLane.Sums2

/-!
# History lane: assembly of G7 (`excess_bound`)

From G2 (`haarStat_sub_le`), the level norms of `Levels.lean` (A6, G3, G4, G6) and the sums of
`Sums.lean`, `Sums2.lean`, `Grid.lean`: `‖(T_{2s}(z+Q_{L+t}) - F)_+‖_{32} ≤ e_⋆` for `t ≥ g`.
-/

@[expose] public section

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta.Assembly

open Contract HistoryLane GMCExplicitDelta.Certificates

variable {d : ℕ}

theorem fineCap_nonneg (row : Row d) (hO : row.Obligations) {δ D r : ℝ} (hδ : 0 < δ) (hD : 0 ≤ D)
    (hr : 0 ≤ r) : 0 ≤ fineCap row δ D r := by
  have hη : 0 < (row.eta : ℝ) := by exact_mod_cast hO.par3.1
  have hβ := sphereFactor_nonneg d
  have hF : 0 ≤ fineF d δ r := by
    unfold fineF
    have := AF_nonneg (d := d) hδ.le
    have := Ch_nonneg
    positivity
  have hG : 0 ≤ fineG d δ r := by
    unfold fineG
    have := AG_nonneg (d := d) hδ.le
    have := Ch_nonneg
    positivity
  unfold fineCap
  positivity

/-- The history constant without the grid part. -/
noncomputable def Hfine (row : Row d) (δ D : ℝ) : ℝ :=
  (1 + (row.eta : ℝ)) * row.C1 * D +
    sphereFactor d * (1 + D) * (row.Fbar δ / (2 * (row.eta : ℝ)) + row.Gbar δ)

theorem Hhist_eq (row : Row d) (δ D : ℝ) : row.Hhist δ D = Hfine row δ D + row.Ugrid δ := by
  unfold Row.Hhist Hfine; ring

theorem Hfine_nonneg (row : Row d) (hO : row.Obligations) {δ D : ℝ} (hδ : 0 < δ) (hD : 0 ≤ D)
    (hz : row.zF δ < 1) : 0 ≤ Hfine row δ D := by
  have hx := xHist_pos' row
  have hx1 : row.xHist < 1 := lt_of_le_of_lt (xHist_le_zF row δ) hz
  have hw1 := wHaar_lt_one row hO
  have hw0 : 0 ≤ row.wHaar := by unfold Row.wHaar; positivity
  have hη : 0 < (row.eta : ℝ) := by exact_mod_cast hO.par3.1
  have hβ := sphereFactor_nonneg d
  have hzF0 : 0 ≤ row.zF δ := le_trans hx.le (xHist_le_zF row δ)
  have hzG0 : 0 ≤ row.zG δ := by unfold Row.zG; positivity
  have hzG1 : row.zG δ < 1 := lt_of_le_of_lt (zG_le_zF row δ) hz
  have h1z : 0 < 1 - row.zF δ := by linarith
  have h1g : 0 < 1 - row.zG δ := by linarith
  have h1x : 0 < 1 - row.xHist := by linarith
  have h1w : 0 ≤ 1 - row.wHaar := by linarith
  have hCh := Ch_nonneg
  have hAF := AF_nonneg (d := d) hδ.le
  have hAG := AG_nonneg (d := d) hδ.le
  have hC1 : 0 ≤ row.C1 := by unfold Row.C1 Row.C0; positivity
  have hF : 0 ≤ row.Fbar δ := by unfold Row.Fbar; positivity
  have hG : 0 ≤ row.Gbar δ := by unfold Row.Gbar; positivity
  unfold Hfine; positivity

theorem bg_pos (row : Row d) {δ : ℝ} (hz : row.zF δ < 1) : 0 < row.bg δ := by
  have hx := xHist_pos' row
  have hκ := kappaH_nonneg' d
  have ha : (0 : ℝ) < proxyA := by norm_num [proxyA]
  have h := Real.log_lt_log (by unfold Row.zF; positivity) hz
  rw [Real.log_one] at h
  unfold Row.zF at h
  rw [Real.log_mul hx.ne' (Real.exp_pos _).ne', Real.log_exp] at h
  unfold Row.bg
  nlinarith [sq_nonneg δ, mul_nonneg (add_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 64) ha.le) hκ)
    (sq_nonneg δ)]

theorem gridBound_nonneg (row : Row d) {δ : ℝ} (hδ : 0 < δ) (L : ℕ) : 0 ≤ gridBound row δ L := by
  have hκ := kappaH_nonneg' d
  have := cg_nonneg row
  have := Ag_nonneg row
  have hP : 0 ≤ P32 := by unfold P32; positivity
  have hs : 0 ≤ δ * √P32 * (row.cg * √((L : ℝ) + 1) + row.Ag) +
      kappaH d * ((L : ℝ) + 1) * δ ^ 2 := by positivity
  unfold gridBound; unfold varsigma Row.hbar; positivity

theorem excess_bound_proof (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (M : SubdiffusiveProcess.Model.GMCModel d) {D F : ℝ} (hD : 0 < D) (hF : 0 < F) (hFD : F ≤ D)
    (L : ℕ) (hP : ∀ k ≤ L, InductionP M k D F) (hzF : row.zF M.delta < 1)
    (_hu : frakU d row.historyCutoff D F < 1) :
    ∀ t, row.g ≤ t → ∀ z : Homogenization.Vec d,
      paperENNRealLpNorm M.P.toMeasure 32
          (fun ω => haarStat row M L z (L + t) ω - ENNReal.ofReal F) ≤
        ENNReal.ofReal (row.eStar M.delta D F) := by
  intro t ht z
  have hδ : 0 < M.delta := M.shellPrefix.delta_pos
  have hx := xHist_pos' row
  have hx1 : row.xHist < 1 := lt_of_le_of_lt (xHist_le_zF row _) hzF
  have hw1 := wHaar_lt_one row hO
  have hw0 : 0 ≤ row.wHaar := by unfold Row.wHaar; positivity
  have h1w : 0 ≤ 1 - row.wHaar := by linarith
  have hbg := bg_pos row hzF
  have hε : 0 < (row.epsSub : ℝ) := by exact_mod_cast hO.par4
  have h4 := hO.avg4
  have hSinf := Sinf_nonneg row hD hF.le hx
  have hUg := Ugrid_nonneg' row (δ := M.delta) hε
  have hHf := Hfine_nonneg row hO hδ hD.le hzF
  have hGB := gridBound_nonneg row hδ L
  set A : SubdiffusiveProcess.Model.PotentialSample d → ℝ≥0∞ := fun ω =>
    ∑ j ∈ Finset.range (t + 1), ENNReal.ofReal ((1 - row.wHaar) * row.wHaar ^ j) *
      (depthMax M L z (L + t) j ω - ENNReal.ofReal F) with hA
  set B : SubdiffusiveProcess.Model.PotentialSample d → ℝ≥0∞ := fun ω =>
    ∑ j ∈ Finset.Ico (t + 1) (t + L + 1), ENNReal.ofReal ((1 - row.wHaar) * row.wHaar ^ j) *
      depthMax M L z (L + t) j ω with hB
  set C : SubdiffusiveProcess.Model.PotentialSample d → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (row.wHaar ^ (t + L + 1)) * unitCellsMax M L z (L + t) ω with hC
  have hAm : AEMeasurable A M.P.toMeasure :=
    Finset.aemeasurable_fun_sum _ fun j _ =>
      (measurable_const.mul ((measurable_depthMax M L z _ j).sub_const _)).aemeasurable
  have hBm : AEMeasurable B M.P.toMeasure :=
    Finset.aemeasurable_fun_sum _ fun j _ =>
      (measurable_const.mul (measurable_depthMax M L z _ j)).aemeasurable
  have hCm : AEMeasurable C M.P.toMeasure :=
    (measurable_const.mul (measurable_unitCellsMax M L z _)).aemeasurable
  have hmain : paperENNRealLpNorm M.P.toMeasure 32
      (fun ω => haarStat row M L z (L + t) ω - ENNReal.ofReal F) ≤
      paperENNRealLpNorm M.P.toMeasure 32 A + paperENNRealLpNorm M.P.toMeasure 32 B +
        paperENNRealLpNorm M.P.toMeasure 32 C := by
    refine (lnorm_mono (by norm_num) fun ω => haarStat_sub_le row hw0 hw1 M L t z F ω).trans ?_
    refine (lnorm_add_le (by norm_num) (hAm.add hBm) hCm).trans ?_
    exact add_le_add (lnorm_add_le (by norm_num) hAm hBm) le_rfl
  have hNA : paperENNRealLpNorm M.P.toMeasure 32 A ≤
      ENNReal.ofReal ((1 - row.wHaar) * D * (row.xHist ^ t * row.Sinf D F)) := by
    refine (lnorm_finset_sum_le (by norm_num) _ _ fun j _ =>
      (measurable_const.mul ((measurable_depthMax M L z _ j).sub_const _)).aemeasurable).trans ?_
    have hterm : ∀ j ∈ Finset.range (t + 1),
        paperENNRealLpNorm M.P.toMeasure 32 (fun ω => ENNReal.ofReal ((1 - row.wHaar) * row.wHaar ^ j) *
          (depthMax M L z (L + t) j ω - ENNReal.ofReal F)) ≤
        ENNReal.ofReal ((1 - row.wHaar) * row.wHaar ^ j * (rootCard d j * (D * frakU d (t - j) D F))) := by
      intro j hj
      have hj' : j ≤ t := by simpa [Nat.lt_succ_iff] using hj
      rw [lnorm_const_mul (by norm_num) ENNReal.ofReal_ne_top,
        ENNReal.ofReal_mul (show (0 : ℝ) ≤ (1 - row.wHaar) * row.wHaar ^ j by positivity)]
      exact mul_le_mul' le_rfl (coarse_level row hd hO M hD hF hFD L (hP L le_rfl) z t j hj')
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => by
      have := rootCard_nonneg d j
      have := frakU_nonneg d (t - j) hD hF.le
      positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc ∑ j ∈ Finset.range (t + 1), (1 - row.wHaar) * row.wHaar ^ j *
          (rootCard d j * (D * frakU d (t - j) D F)) =
        (1 - row.wHaar) * D * ∑ j ∈ Finset.range (t + 1), row.xHist ^ j * frakU d (t - j) D F := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← w_mul_rootCard row j]; ring
      _ ≤ _ := by
          gcongr
          exact coarse_sum_le row hD hF.le hx h4 t
  have hNB : paperENNRealLpNorm M.P.toMeasure 32 B ≤
      ENNReal.ofReal (row.xHist ^ t * Hfine row M.delta D) := by
    refine (lnorm_finset_sum_le (by norm_num) _ _ fun j _ =>
      (measurable_const.mul (measurable_depthMax M L z _ j)).aemeasurable).trans ?_
    have hterm : ∀ j ∈ Finset.Ico (t + 1) (t + L + 1),
        paperENNRealLpNorm M.P.toMeasure 32 (fun ω => ENNReal.ofReal ((1 - row.wHaar) * row.wHaar ^ j) *
          depthMax M L z (L + t) j ω) ≤
        ENNReal.ofReal ((1 - row.wHaar) * row.xHist ^ j * fineCap row M.delta D ((j - t : ℕ) : ℝ)) := by
      intro j hj
      obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
      have hcap := fineCap_nonneg row hO hδ hD.le (Nat.cast_nonneg (j - t))
      rw [lnorm_const_mul (by norm_num) ENNReal.ofReal_ne_top,
        show (1 - row.wHaar) * row.xHist ^ j * fineCap row M.delta D ((j - t : ℕ) : ℝ) =
          (1 - row.wHaar) * row.wHaar ^ j * (rootCard d j * fineCap row M.delta D ((j - t : ℕ) : ℝ)) by
            rw [← w_mul_rootCard row j]; ring,
        ENNReal.ofReal_mul (show (0 : ℝ) ≤ (1 - row.wHaar) * row.wHaar ^ j by positivity)]
      exact mul_le_mul' le_rfl (fine_level row hd hO M hD L hP z t j hj1 (by omega))
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j hj => by
      have := fineCap_nonneg row hO hδ hD.le (Nat.cast_nonneg (j - t))
      positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Finset.sum_Ico_eq_sum_range]
    have hlen : t + L + 1 - (t + 1) = L := by omega
    rw [hlen]
    calc ∑ k ∈ Finset.range L, (1 - row.wHaar) * row.xHist ^ (t + 1 + k) *
          fineCap row M.delta D ((t + 1 + k - t : ℕ) : ℝ) =
        row.xHist ^ t * ∑ k ∈ Finset.range L, (1 - row.wHaar) * row.xHist ^ (k + 1) *
          fineCap row M.delta D ((k + 1 : ℕ) : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          have e1 : t + 1 + k - t = k + 1 := by omega
          rw [e1, show t + 1 + k = t + (k + 1) by ring, pow_add]; ring
      _ ≤ _ := by
          gcongr
          exact fine_sum_le row hO hδ hD.le hzF L
  have hNC : paperENNRealLpNorm M.P.toMeasure 32 C ≤
      ENNReal.ofReal (row.xHist ^ t * row.Ugrid M.delta) := by
    rw [hC, lnorm_const_mul (by norm_num) ENNReal.ofReal_ne_top]
    refine (mul_le_mul' le_rfl (grid_level row hd hO M L z (L + t))).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hg := grid_term_le row hε hδ hbg L
    have hrc := w_mul_rootCard row (L + t)
    calc row.wHaar ^ (t + L + 1) * (rootCard d (L + t) * gridBound row M.delta L) =
        row.xHist ^ t * (row.wHaar * row.xHist ^ L * gridBound row M.delta L) := by
          have : row.wHaar ^ (t + L + 1) * rootCard d (L + t) = row.wHaar * row.xHist ^ (L + t) := by
            rw [show t + L + 1 = (L + t) + 1 by ring, pow_succ, mul_comm (row.wHaar ^ (L + t)) row.wHaar,
              mul_assoc, hrc]
          rw [← mul_assoc, this, pow_add]; ring
      _ ≤ _ := by gcongr
  refine hmain.trans ?_
  refine (add_le_add (add_le_add hNA hNB) hNC).trans ?_
  have hA0 : 0 ≤ (1 - row.wHaar) * D * (row.xHist ^ t * row.Sinf D F) :=
    mul_nonneg (mul_nonneg h1w hD.le) (mul_nonneg (pow_nonneg hx.le _) hSinf)
  have hB0 : 0 ≤ row.xHist ^ t * Hfine row M.delta D := mul_nonneg (pow_nonneg hx.le _) hHf
  have hC0 : 0 ≤ row.xHist ^ t * row.Ugrid M.delta := mul_nonneg (pow_nonneg hx.le _) hUg
  rw [← ENNReal.ofReal_add hA0 hB0, ← ENNReal.ofReal_add (add_nonneg hA0 hB0) hC0]
  refine ENNReal.ofReal_le_ofReal ?_
  have hpow : row.xHist ^ t ≤ row.xHist ^ row.g := pow_le_pow_of_le_one hx.le hx1.le ht
  unfold Row.eStar
  rw [Hhist_eq]
  have hbr : 0 ≤ (1 - row.wHaar) * D * row.Sinf D F + (Hfine row M.delta D + row.Ugrid M.delta) := by
    exact add_nonneg (mul_nonneg (mul_nonneg h1w hD.le) hSinf) (add_nonneg hHf hUg)
  calc (1 - row.wHaar) * D * (row.xHist ^ t * row.Sinf D F) +
        row.xHist ^ t * Hfine row M.delta D + row.xHist ^ t * row.Ugrid M.delta =
      row.xHist ^ t * ((1 - row.wHaar) * D * row.Sinf D F + (Hfine row M.delta D + row.Ugrid M.delta)) := by ring
    _ ≤ row.xHist ^ row.g * ((1 - row.wHaar) * D * row.Sinf D F + (Hfine row M.delta D + row.Ugrid M.delta)) :=
        mul_le_mul_of_nonneg_right hpow hbr
    _ = _ := by ring

end GMCExplicitDelta.Assembly
