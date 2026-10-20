module

public import GMCExplicitDelta.HistoryLane.Level
public import GMCExplicitDelta.HistoryLane.Cells
public import GMCExplicitDelta.HistoryLane.Defs
public import GMCExplicitDelta.HistoryLane.Grid
public import GMCExplicitDelta.Steps.HistoryFine
public import GMCExplicitDelta.Steps.AssemblyFrozen

/-!
# History lane: norms of the depth levels (G7)

* `coarse_level`: `‖(e_j - F)_+‖_{32} ≤ 3^{dj/32} D 𝔲_{t-j}` for `j ≤ t` (A6).
* `fine_level`: `‖e_j‖_{32} ≤ 3^{dj/32} fineCap(j-t)` for `t < j ≤ t+L` (G3, G4).
* `grid_level`: `‖max_{U'} sup_V J^max(V)‖_{32} ≤ 3^{dn/32} B_L` (G6).
-/

@[expose] public section

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta.Assembly

open Contract HistoryLane GMCExplicitDelta.Certificates

variable {d : ℕ}

theorem measurable_finset_sup' {ι Ω : Type*} [MeasurableSpace Ω] (s : Finset ι)
    {f : ι → Ω → ℝ≥0∞} (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable fun ω => s.sup fun i => f i ω := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.sup_insert]
    exact Measurable.fun_sup (hf a (Finset.mem_insert_self _ _))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem measurable_normalizedDefect_cell (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (z : Homogenization.Vec d) (R : Homogenization.TriadicCube d) :
    Measurable (normalizedDefect M L (cellAt z R)) := by
  rw [normalizedDefect_eq_scaledDefect]
  exact (measurable_cascadeObservables M L (cellAt z R)).1 _

theorem measurable_depthMax (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (z : Homogenization.Vec d) (n j : ℕ) : Measurable (depthMax M L z n j) :=
  measurable_finset_sup' _ fun R _ => measurable_normalizedDefect_cell M L z R

theorem measurable_subcellMax (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (z : Homogenization.Vec d) (R : Homogenization.TriadicCube d) :
    Measurable (subcellMax M L z R) := by
  unfold subcellMax
  refine Measurable.iSup fun k => ?_
  exact measurable_finset_sup' _ fun S _ => measurable_normalizedDefect_cell M L z S

theorem measurable_unitCellsMax (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (z : Homogenization.Vec d) (n : ℕ) : Measurable (unitCellsMax M L z n) :=
  measurable_finset_sup' _ fun R _ => measurable_subcellMax M L z R

theorem cell_eq_cube (z : Homogenization.Vec d) {n j : ℕ} (hj : j ≤ n)
    {R : Homogenization.TriadicCube d} (hR : R ∈ descendantsAtDepth (originCube d (n : ℤ)) j) :
    ∃ z' : Homogenization.Vec d, cellAt z R = cubeAt z' (n - j) := by
  have hs := scale_eq_sub_of_mem_descendantsAtDepth hR
  refine ⟨_, cellAt_eq_cubeAt z R (n - j) ?_⟩
  rw [hs]; simp only [originCube]; push_cast [Nat.cast_sub hj]; ring

theorem coarse_level (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (M : SubdiffusiveProcess.Model.GMCModel d) {D F : ℝ} (hD : 0 < D) (hF : 0 < F) (hFD : F ≤ D)
    (L : ℕ) (hPL : InductionP M L D F) (z : Homogenization.Vec d) (t j : ℕ) (hj : j ≤ t) :
    paperENNRealLpNorm M.P.toMeasure 32
        (fun ω => depthMax M L z (L + t) j ω - ENNReal.ofReal F) ≤
      ENNReal.ofReal (rootCard d j * (D * frakU d (t - j) D F)) := by
  have hu0 : 0 ≤ D * frakU d (t - j) D F := mul_nonneg hD.le (frakU_nonneg d _ hD hF.le)
  have hpt : ∀ ω, depthMax M L z (L + t) j ω - ENNReal.ofReal F ≤
      (descendantsAtDepth (originCube d ((L + t : ℕ) : ℤ)) j).sup
        fun R => normalizedDefect M L (cellAt z R) ω - ENNReal.ofReal F := by
    intro ω
    unfold depthMax
    rw [tsub_le_iff_right]
    refine Finset.sup_le fun R hR => ?_
    calc normalizedDefect M L (cellAt z R) ω ≤
          (normalizedDefect M L (cellAt z R) ω - ENNReal.ofReal F) + ENNReal.ofReal F :=
          le_tsub_add
      _ ≤ _ := add_le_add (Finset.le_sup (f := fun R => normalizedDefect M L (cellAt z R) ω -
            ENNReal.ofReal F) hR) le_rfl
  refine (lnorm_mono (by norm_num) hpt).trans ?_
  refine level_norm_le _ j (fun R ω => normalizedDefect M L (cellAt z R) ω - ENNReal.ofReal F)
    (fun R _ => ((measurable_normalizedDefect_cell M L z R).sub_const _).aemeasurable) hu0 ?_
  intro R hR
  obtain ⟨z', hz'⟩ := cell_eq_cube z (by omega : j ≤ L + t) hR
  have hk : L + t - j = L + (t - j) := by omega
  rw [hk] at hz'
  show paperENNRealLpNorm M.P.toMeasure 32
      (fun ω => normalizedDefect M L (cellAt z R) ω - ENNReal.ofReal F) ≤ _
  rw [hz']
  rcases Nat.eq_zero_or_pos (t - j) with h0 | hk1
  · rw [h0]
    have hfu : frakU d 0 D F = 1 := by simp [frakU]
    rw [hfu, mul_one]
    have := (hPL L le_rfl z' ).2.1
    refine le_trans (lnorm_mono (by norm_num) fun ω => tsub_le_self) ?_
    simpa [h0] using this
  · exact (nativeCap_bound hd hO M hD hF hFD L hPL (t - j) hk1 z').2

theorem fine_level (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (M : SubdiffusiveProcess.Model.GMCModel d) {D F : ℝ} (hD : 0 < D)
    (L : ℕ) (hP : ∀ k ≤ L, InductionP M k D F) (z : Homogenization.Vec d) (t j : ℕ)
    (hj1 : t + 1 ≤ j) (hj2 : j ≤ t + L) :
    paperENNRealLpNorm M.P.toMeasure 32 (depthMax M L z (L + t) j) ≤
      ENNReal.ofReal (rootCard d j * fineCap row M.delta D ((j - t : ℕ) : ℝ)) := by
  have hδ : 0 < M.delta := M.shellPrefix.delta_pos
  have hη : 0 < (row.eta : ℝ) := by exact_mod_cast hO.par3.1
  have hη1 : (row.eta : ℝ) ≤ 1 := by exact_mod_cast hO.par3.2
  have hβ := sphereFactor_nonneg d
  set r := j - t with hr
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have hFnn : 0 ≤ fineF d M.delta (r : ℝ) := by
    unfold fineF
    have := AF_nonneg (d := d) hδ.le
    have := Ch_nonneg
    positivity
  have hGnn : 0 ≤ fineG d M.delta (r : ℝ) := by
    unfold fineG
    have := AG_nonneg (d := d) hδ.le
    have := Ch_nonneg
    positivity
  have hcap : 0 ≤ fineCap row M.delta D (r : ℝ) := by
    unfold fineCap
    have : 0 ≤ (row.eta : ℝ) := hη.le
    positivity
  refine level_norm_le _ j (fun R ω => normalizedDefect M L (cellAt z R) ω)
    (fun R _ => (measurable_normalizedDefect_cell M L z R).aemeasurable) hcap ?_
  intro R hR
  obtain ⟨z', hz'⟩ := cell_eq_cube z (by omega : j ≤ L + t) hR
  have hk : L + t - j = L - r := by omega
  rw [hk] at hz'
  show paperENNRealLpNorm M.P.toMeasure 32 (normalizedDefect M L (cellAt z R)) ≤ _
  rw [hz']
  have hkL : L - r < L := by omega
  have hL : L - (L - r) = r := by omega
  have hNk := (hP (L - r) (by omega) (L - r) le_rfl z').2.1
  obtain ⟨hF', hG'⟩ : (∀ x, _) ∧ (∀ x, _) :=
    ⟨fun x => (fineRatioNorms row hd hO M hkL x).1, fun x => (fineRatioNorms row hd hO M hkL x).2⟩
  rw [hL] at hF' hG'
  have hsens := fineSensitivity hd M hkL z' hη hη1 hFnn hGnn hF' hG'
  refine hsens.trans ?_
  unfold fineCap
  have h1 : (1 + ENNReal.ofReal (row.eta : ℝ)) *
      paperENNRealLpNorm M.P.toMeasure 32 (normalizedDefect M (L - r) (cubeAt z' (L - r))) ≤
      ENNReal.ofReal ((1 + (row.eta : ℝ)) * D) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (by norm_num) hη.le,
      ENNReal.ofReal_one]
    exact mul_le_mul' le_rfl hNk
  have h2 : ENNReal.ofReal (sphereFactor d) *
      (1 + paperENNRealLpNorm M.P.toMeasure 32
        (normalizedDefect M (L - r) (cubeAt z' (L - r)))) *
      ENNReal.ofReal (fineF d M.delta r / (2 * (row.eta : ℝ)) + fineG d M.delta r) ≤
      ENNReal.ofReal (sphereFactor d * (1 + D) *
        (fineF d M.delta r / (2 * (row.eta : ℝ)) + fineG d M.delta r)) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hβ, ENNReal.ofReal_add (by norm_num) hD.le,
      ENNReal.ofReal_one]
    gcongr
  refine (add_le_add h1 h2).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]

theorem grid_level (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (z : Homogenization.Vec d) (n : ℕ) :
    paperENNRealLpNorm M.P.toMeasure 32 (unitCellsMax M L z n) ≤
      ENNReal.ofReal (rootCard d n * gridBound row M.delta L) := by
  have hB : 0 ≤ gridBound row M.delta L := by
    have hκ := kappaH_nonneg' d
    have := cg_nonneg row
    have := Ag_nonneg row
    have hP : 0 ≤ P32 := by unfold P32; positivity
    have hs : 0 ≤ M.delta * √P32 * (row.cg * √((L : ℝ) + 1) + row.Ag) +
        kappaH d * ((L : ℝ) + 1) * M.delta ^ 2 := by
      have hδ : 0 < M.delta := M.shellPrefix.delta_pos
      positivity
    unfold gridBound; unfold varsigma Row.hbar; positivity
  refine level_norm_le _ n (fun R ω => subcellMax M L z R ω)
    (fun R _ => (measurable_subcellMax M L z R).aemeasurable) hB ?_
  intro R hR
  refine gridMax_norm_le row hd hO M L z R ?_
  have := scale_eq_sub_of_mem_descendantsAtDepth hR
  simpa [originCube] using this

end GMCExplicitDelta.Assembly
