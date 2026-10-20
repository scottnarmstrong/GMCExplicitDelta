module

public import GMCExplicitDelta.HistoryLane.Cells

/-!
# History lane: G2, splitting the all-descendant statistic

`haarStat_sub_le`: for `n = L + t`, pointwise (in `ℝ≥0∞`, where truncated subtraction is `(·)_+`)
`(T_{2s}(Q) - F)_+ ≤ (1-w)∑_{j≤t} w^j (e_j - F)_+ + (1-w)∑_{j=t+1}^{t+L} w^j e_j
  + w^{t+L+1} max_{U'} sup_{V ⊆ U'} J^max(V)`.
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta.Assembly

open Contract

variable {d : ℕ}

/-- `sup_{V ⊆ U} J^max(V; b_L)` over the triadic subcells `V` (of every depth) of the cube `R`
(translated by `z`). -/
noncomputable def subcellMax (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (z : Homogenization.Vec d) (R : Homogenization.TriadicCube d)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) : ℝ≥0∞ :=
  ⨆ k : ℕ, (descendantsAtDepth R k).sup fun S => normalizedDefect M L (cellAt z S) ω

/-- `max_{U'} sup_{V ⊆ U'} J^max(V; b_L)` over the unit cells `U'` (depth `n`) of `z + Q_n`. -/
noncomputable def unitCellsMax (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (z : Homogenization.Vec d) (n : ℕ) (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    ℝ≥0∞ :=
  (descendantsAtDepth (originCube d (n : ℤ)) n).sup fun R => subcellMax M L z R ω

end GMCExplicitDelta.Assembly

namespace GMCExplicitDelta.HistoryLane

open scoped ENNReal

/-- Abstract form of G2. -/
theorem split_abstract {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1) (e : ℕ → ℝ≥0∞) (F S : ℝ≥0∞)
    (t L : ℕ) (hS : ∀ j, t + L < j → e j ≤ S) :
    (∑' j : ℕ, ENNReal.ofReal ((1 - w) * w ^ j) * e j) - F ≤
      ∑ j ∈ Finset.range (t + 1), ENNReal.ofReal ((1 - w) * w ^ j) * (e j - F) +
      ∑ j ∈ Finset.Ico (t + 1) (t + L + 1), ENNReal.ofReal ((1 - w) * w ^ j) * e j +
      ENNReal.ofReal (w ^ (t + L + 1)) * S := by
  set c : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal ((1 - w) * w ^ j) with hc
  have hsplit : ∑' j, c j * e j =
      ∑ j ∈ Finset.range (t + L + 1), c j * e j + ∑' j, c (j + (t + L + 1)) * e (j + (t + L + 1)) :=
    (ENNReal.summable.sum_add_tsum_nat_add' (f := fun j => c j * e j)).symm
  have htail : ∑' j, c (j + (t + L + 1)) * e (j + (t + L + 1)) ≤
      ENNReal.ofReal (w ^ (t + L + 1)) * S := by
    calc ∑' j, c (j + (t + L + 1)) * e (j + (t + L + 1)) ≤ ∑' j, c (j + (t + L + 1)) * S :=
          ENNReal.tsum_le_tsum fun j => mul_le_mul' le_rfl (hS _ (by omega))
      _ = (∑' j, c (j + (t + L + 1))) * S := ENNReal.tsum_mul_right
      _ = _ := by
        congr 1
        have hg : HasSum (fun j : ℕ => (1 - w) * w ^ (j + (t + L + 1))) (w ^ (t + L + 1)) := by
          have h0 := (hasSum_geometric_of_lt_one hw0 hw1).mul_left ((1 - w) * w ^ (t + L + 1))
          have h1 : (1 - w) * w ^ (t + L + 1) * (1 - w)⁻¹ = w ^ (t + L + 1) := by
            field_simp [(sub_pos.mpr hw1).ne']
          rw [h1] at h0
          convert h0 using 1
          funext j; rw [pow_add]; ring
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
          hg.summable, hg.tsum_eq]
  have hmass : ∑ j ∈ Finset.range (t + 1), c j ≤ 1 := by
    rw [hc, ← ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
    have : ∑ j ∈ Finset.range (t + 1), (1 - w) * w ^ j = 1 - w ^ (t + 1) := by
      clear hsplit htail
      induction t + 1 with
      | zero => simp
      | succ n ih => rw [Finset.sum_range_succ, ih]; ring
    rw [this]
    exact ENNReal.ofReal_le_one.mpr (by have := pow_nonneg hw0 (t + 1); linarith)
  have hcoarse : ∑ j ∈ Finset.range (t + 1), c j * e j ≤
      ∑ j ∈ Finset.range (t + 1), c j * (e j - F) + F := by
    calc ∑ j ∈ Finset.range (t + 1), c j * e j ≤
          ∑ j ∈ Finset.range (t + 1), (c j * (e j - F) + c j * F) :=
          Finset.sum_le_sum fun j _ => by
            rw [← mul_add]; exact mul_le_mul' le_rfl le_tsub_add
      _ = ∑ j ∈ Finset.range (t + 1), c j * (e j - F) + (∑ j ∈ Finset.range (t + 1), c j) * F := by
          rw [Finset.sum_add_distrib, Finset.sum_mul]
      _ ≤ _ := by
          gcongr
          calc (∑ j ∈ Finset.range (t + 1), c j) * F ≤ 1 * F := by gcongr
            _ = F := one_mul F
  have hfin : ∑ j ∈ Finset.range (t + L + 1), c j * e j =
      ∑ j ∈ Finset.range (t + 1), c j * e j + ∑ j ∈ Finset.Ico (t + 1) (t + L + 1), c j * e j :=
    (Finset.sum_range_add_sum_Ico _ (by omega)).symm
  rw [tsub_le_iff_right, hsplit, hfin]
  calc ∑ j ∈ Finset.range (t + 1), c j * e j + ∑ j ∈ Finset.Ico (t + 1) (t + L + 1), c j * e j +
        ∑' j, c (j + (t + L + 1)) * e (j + (t + L + 1)) ≤
      (∑ j ∈ Finset.range (t + 1), c j * (e j - F) + F) +
        ∑ j ∈ Finset.Ico (t + 1) (t + L + 1), c j * e j + ENNReal.ofReal (w ^ (t + L + 1)) * S :=
        add_le_add (add_le_add hcoarse le_rfl) htail
    _ = _ := by ring

end GMCExplicitDelta.HistoryLane

namespace GMCExplicitDelta.Assembly

open Contract

variable {d : ℕ}

theorem depthMax_le_unitCellsMax (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (z : Homogenization.Vec d) (n j : ℕ) (hj : n ≤ j)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    depthMax M L z n j ω ≤ unitCellsMax M L z n ω := by
  unfold depthMax unitCellsMax
  refine Finset.sup_le fun R hR => ?_
  have hj' : j = n + (j - n) := by omega
  rw [hj'] at hR
  obtain ⟨S, hS, hRS⟩ := exists_descendant_of_depth_add hR
  refine le_trans ?_ (Finset.le_sup (f := fun R => subcellMax M L z R ω) hS)
  unfold subcellMax
  exact le_trans (Finset.le_sup (f := fun S => normalizedDefect M L (cellAt z S) ω) hRS)
    (le_iSup (fun k : ℕ => (descendantsAtDepth S k).sup fun S => normalizedDefect M L (cellAt z S) ω)
      (j - n))

/-- **G2 (splitting the statistic).** -/
theorem haarStat_sub_le (row : Row d) (hw0 : 0 ≤ row.wHaar) (hw1 : row.wHaar < 1)
    (M : SubdiffusiveProcess.Model.GMCModel d) (L t : ℕ) (z : Homogenization.Vec d) (F : ℝ)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    haarStat row M L z (L + t) ω - ENNReal.ofReal F ≤
      ∑ j ∈ Finset.range (t + 1), ENNReal.ofReal ((1 - row.wHaar) * row.wHaar ^ j) *
          (depthMax M L z (L + t) j ω - ENNReal.ofReal F) +
        ∑ j ∈ Finset.Ico (t + 1) (t + L + 1),
          ENNReal.ofReal ((1 - row.wHaar) * row.wHaar ^ j) * depthMax M L z (L + t) j ω +
        ENNReal.ofReal (row.wHaar ^ (t + L + 1)) * unitCellsMax M L z (L + t) ω := by
  unfold haarStat
  exact HistoryLane.split_abstract hw0 hw1 (fun j => depthMax M L z (L + t) j ω) _ _ t L
    fun j hj => depthMax_le_unitCellsMax M L z (L + t) j (by omega) ω

end GMCExplicitDelta.Assembly
