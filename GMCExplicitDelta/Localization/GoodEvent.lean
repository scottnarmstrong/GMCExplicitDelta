module

public import GMCExplicitDelta.Localization.Subadd

/-!
# G1(a): descendant bound on the good event

`goodEvent_cell_bound_proof`: on `𝒢(Q_n) = {T_{2s}(Q_n) ≤ θ_R}`, every depth-`k` cell `R` of `Q_n` has
`J^max(R; b_L) ≤ θ_R q_s^k`. Proof: `J^max` of a cell is at most the maximum over its children (C2,
`frozenJ_le_descAvg`), so `e_j = max_{depth j} J^max` is nondecreasing in `j` (C11(b)); then
`T_{2s} ≥ (1-w)∑_{j≥k} w^j e_k = w^k e_k` and `w^{-k} = q_s^k`.
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta.Localization

open Assembly Contract

variable {d : ℕ}

theorem normalizedDefect_eq_iSup (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (U : Ch02.Domain d) (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    normalizedDefect M L U ω =
      ⨆ e : {e : Homogenization.Vec d // vecNormSq e = 1},
        ENNReal.ofReal (frozenJ M L U e.1 e.1 ω) := rfl

/-- `J^max` of a cell is at most the maximum of `J^max` over its depth-`1` children. -/
theorem normalizedDefect_le_children (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (R : Homogenization.TriadicCube d) (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    normalizedDefect M L (cellAt 0 R) ω ≤
      (descendantsAtDepth R 1).sup fun R' => normalizedDefect M L (cellAt 0 R') ω := by
  rw [normalizedDefect_eq_iSup]
  refine iSup_le fun e => ?_
  have hsub := frozenJ_le_descAvg M L R 1 e.1 e.1 ω
  obtain ⟨R', hR', hmax⟩ := (descendantsAtDepth R 1).exists_max_image
    (fun R' => frozenJ M L (cellAt 0 R') e.1 e.1 ω) (descendantsAtDepth_nonempty R 1)
  have havg : descendantsAverage R 1 (fun R' => frozenJ M L (cellAt 0 R') e.1 e.1 ω) ≤
      frozenJ M L (cellAt 0 R') e.1 e.1 ω := by
    have h := descendantsAverage_le_descendantsAverage R 1 (G := fun _ =>
      frozenJ M L (cellAt 0 R') e.1 e.1 ω) hmax
    have hc : descendantsAverage R 1 (fun _ => frozenJ M L (cellAt 0 R') e.1 e.1 ω) =
        frozenJ M L (cellAt 0 R') e.1 e.1 ω := by
      have hpos : (0 : ℝ) < ((descendantsAtDepth R 1).card : ℝ) := by
        exact_mod_cast (descendantsAtDepth_nonempty R 1).card_pos
      unfold descendantsAverage
      simp only [Finset.sum_const, nsmul_eq_mul]
      field_simp
    linarith
  calc ENNReal.ofReal (frozenJ M L (cellAt 0 R) e.1 e.1 ω) ≤
      ENNReal.ofReal (frozenJ M L (cellAt 0 R') e.1 e.1 ω) :=
        ENNReal.ofReal_le_ofReal (hsub.trans havg)
    _ ≤ normalizedDefect M L (cellAt 0 R') ω := by
        rw [normalizedDefect_eq_iSup]
        exact le_iSup (fun e : {e : Homogenization.Vec d // vecNormSq e = 1} =>
          ENNReal.ofReal (frozenJ M L (cellAt 0 R') e.1 e.1 ω)) e
    _ ≤ _ := Finset.le_sup (f := fun R' => normalizedDefect M L (cellAt 0 R') ω) hR'

/-- **C11(b)**: the depth maxima `e_j` are nondecreasing in `j`. -/
theorem depthMax_mono (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    Monotone fun j => depthMax M L 0 n j ω := by
  refine monotone_nat_of_le_succ fun j => ?_
  refine Finset.sup_le fun R hR => ?_
  refine (normalizedDefect_le_children M L R ω).trans (Finset.sup_le fun R' hR' => ?_)
  exact Finset.le_sup (f := fun R => normalizedDefect M L (cellAt 0 R) ω)
    (mem_descendantsAtDepth_add hR hR')

theorem wHaar_pos (row : Row d) : 0 < row.wHaar := Real.rpow_pos_of_pos (by norm_num) _

theorem wHaar_lt_one (row : Row d) (hO : row.Obligations) : row.wHaar < 1 := by
  have hs : (0 : ℝ) < (row.s : ℝ) := by exact_mod_cast hO.par1.2.2.2.2.2.1
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

theorem qs_mul_wHaar (row : Row d) : row.qs * row.wHaar = 1 := by
  unfold Row.qs Row.wHaar
  rw [← Real.rpow_add (by norm_num), add_neg_cancel, Real.rpow_zero]

/-- **G1(a)**: on the good event, `J^max(R; b_L) ≤ θ_R q_s^k` for every depth-`k` cell `R` of `Q_n`. -/
theorem goodEvent_cell_bound_proof (row : Row d) (hO : row.Obligations)
    (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) (hω : ω ∈ goodEvent row M L 0 n) (k : ℕ)
    (R : Homogenization.TriadicCube d) (hR : R ∈ descendantsAtDepth (originCube d (n : ℤ)) k) :
    normalizedDefect M L (cellAt 0 R) ω ≤ ENNReal.ofReal (row.thetaR * row.qs ^ k) := by
  have hw0 := wHaar_pos row
  have hw1 := wHaar_lt_one row hO
  set w := row.wHaar with hw
  set e : ℕ → ℝ≥0∞ := fun j => depthMax M L 0 n j ω with he
  have hmono : Monotone e := depthMax_mono M L n ω
  -- `T_{2s} ≥ w^k e_k`
  have hgeom : ∑' i : ℕ, ENNReal.ofReal ((1 - w) * w ^ (k + i)) = ENNReal.ofReal (w ^ k) := by
    have hsum : HasSum (fun i : ℕ => (1 - w) * w ^ (k + i)) (w ^ k) := by
      have h := (hasSum_geometric_of_lt_one hw0.le hw1).mul_left ((1 - w) * w ^ k)
      have hne : (1 - w) ≠ 0 := by linarith
      convert h using 1
      · funext i; ring
      · field_simp
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => mul_nonneg (by linarith) (pow_nonneg hw0.le _))
      hsum.summable, hsum.tsum_eq]
  have hT : ENNReal.ofReal (w ^ k) * e k ≤ haarStat row M L 0 n ω := by
    calc ENNReal.ofReal (w ^ k) * e k = ∑' i : ℕ, ENNReal.ofReal ((1 - w) * w ^ (k + i)) * e k := by
          rw [ENNReal.tsum_mul_right, hgeom]
      _ ≤ ∑' i : ℕ, ENNReal.ofReal ((1 - w) * w ^ (k + i)) * e (k + i) :=
          ENNReal.tsum_le_tsum fun i => by gcongr; exact hmono (Nat.le_add_right k i)
      _ ≤ ∑' j : ℕ, ENNReal.ofReal ((1 - w) * w ^ j) * e j :=
          ENNReal.tsum_comp_le_tsum_of_injective (f := fun i : ℕ => k + i)
            (fun i j hij => by simpa using hij)
            (fun j => ENNReal.ofReal ((1 - w) * w ^ j) * e j)
      _ = haarStat row M L 0 n ω := rfl
  have hek : e k ≤ ENNReal.ofReal (row.thetaR * row.qs ^ k) := by
    have hT' := hT.trans hω
    have hwk : 0 < w ^ k := pow_pos hw0 k
    have hq : row.qs ^ k * w ^ k = 1 := by rw [← mul_pow, qs_mul_wHaar, one_pow]
    have hqpos : 0 < row.qs := Real.rpow_pos_of_pos (by norm_num) _
    calc e k = ENNReal.ofReal (row.qs ^ k) * (ENNReal.ofReal (w ^ k) * e k) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg hqpos.le _), hq, ENNReal.ofReal_one,
            one_mul]
      _ ≤ ENNReal.ofReal (row.qs ^ k) * ENNReal.ofReal row.thetaR := by gcongr
      _ = ENNReal.ofReal (row.thetaR * row.qs ^ k) := by
          rw [← ENNReal.ofReal_mul (pow_nonneg hqpos.le _), mul_comm]
  exact (Finset.le_sup (f := fun R => normalizedDefect M L (cellAt 0 R) ω) hR).trans hek

end GMCExplicitDelta.Localization
