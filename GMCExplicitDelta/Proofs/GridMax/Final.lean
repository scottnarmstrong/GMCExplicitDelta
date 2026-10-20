module

public import GMCExplicitDelta.Proofs.GridMax.Constants
public import GMCExplicitDelta.Proofs.GridMax.Holder
public import GMCExplicitDelta.Proofs.GridMax.Trial

/-! # G6a: the whole-sum grid bound for all subunit cells -/

@[expose] public section

open Homogenization Homogenization.Book MeasureTheory
open SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

namespace GMCExplicitDelta.Assembly

open Contract
variable {d : ℕ}

/-- G6a with exactly the statement. -/
theorem gridMax_norm_le_proof (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (z : Homogenization.Vec d)
    (R : Homogenization.TriadicCube d) (hR : R.scale = 0) :
    paperENNRealLpNorm M.P.toMeasure 32 (subcellMax M L z R) ≤
      ENNReal.ofReal (gridBound row M.delta L) := by
  classical
  have hN : 0 < row.gridN := lt_of_lt_of_le Nat.zero_lt_one hO.par2.2.2.2.1
  let : NeZero row.gridN := ⟨hN.ne'⟩
  let : NeZero d := ⟨by have := M.shellPrefix.dimension; omega⟩
  have hδ := M.shellPrefix.delta_pos
  have hκ : 0 ≤ kappaH d := by unfold kappaH; split_ifs <;> norm_num [kappaQ1]
  have hcg : 0 ≤ row.cg := by unfold Row.cg Row.hbar; positivity
  have hAg : 0 ≤ row.Ag := by unfold Row.Ag; positivity
  have hD : 0 ≤ kappaH d * ((L : ℝ) + 1) * M.delta ^ 2 := by positivity
  let c : Homogenization.Vec d := z + fun i => (R.index i : ℝ)
  have hdom : cellAt z R = cubeAt c 0 := by
    simpa only [pow_zero, mul_one] using cellAt_eq_cubeAt z R 0 hR
  have hpoint (ω : PotentialSample d) : subcellMax M L z R ω ≤
      ENNReal.ofReal ((GridMax.maximum row.gridN L c ω + GridMax.remainder row.gridN L c ω +
        kappaH d * ((L : ℝ) + 1) * M.delta ^ 2) ^ 2 *
          Real.exp (GridMax.maximum row.gridN L c ω + GridMax.remainder row.gridN L c ω +
            kappaH d * ((L : ℝ) + 1) * M.delta ^ 2) / 2) := by
    apply GridMax.subcellMax_le_trial M L z R ω ((normShift_drift_proof row hd hO M).1 L)
      (add_nonneg (add_nonneg (GridMax.maximum_nonneg _ _ _ _) (GridMax.remainder_nonneg _ _ _ _)) hD)
    intro x hx
    have hx' : x - c ∈ openCubeSet (originCube d 0) := by
      rw [hdom] at hx
      exact mem_translateSet_iff_sub_mem.1 hx
    have hp := GridMax.prefix_le_maximum_remainder row.gridN L c ω hx'
    simp only [sub_add_cancel] at hp
    have hab : |GridMax.layerPrefix L ω x - normShift M L| ≤
        |GridMax.layerPrefix L ω x| + |normShift M L| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le (GridMax.layerPrefix L ω x) (normShift M L)
    exact hab.trans (add_le_add hp ((normShift_drift_proof row hd hO M).2.2 L))
  refine (HistoryLane.lnorm_mono (μ := M.P.toMeasure) (ξ := 32) (by norm_num) hpoint).trans ?_
  have hb := GridMax.trial_norm_bound (μ := M.P.toMeasure)
    (GridMax.maximum_measurable row.gridN L c) (GridMax.remainder_measurable row.gridN L c)
    (GridMax.maximum_nonneg row.gridN L c) (GridMax.remainder_nonneg row.gridN L c)
    hD
    (by positivity : 0 ≤ M.delta * Real.sqrt P32 * (row.cg * Real.sqrt ((L : ℝ) + 1)))
    (by positivity : 0 ≤ row.Ag * M.delta * Real.sqrt P32)
    (by positivity : 0 ≤ (2 * ((row.gridN ^ d : ℕ) : ℝ)) ^ (1 / 128 : ℝ) *
      Real.exp (64 * (GridMax.prefixProxy M L : ℝ)))
    (by positivity : 0 ≤ (2 : ℝ) ^ (1 / 128 : ℝ) * Real.exp (32 * row.Ag ^ 2 * M.delta ^ 2))
    (GridMax.maximum_lnorm_row row M L c)
    (by simpa only [Row.Ag] using GridMax.remainder_lnorm128 M hN L c)
    (GridMax.maximum_exp128_norm M row.gridN L c)
    (by simpa only [Row.Ag] using GridMax.remainder_exp128_norm M hN L c)
  refine hb.trans_eq ?_
  congr 1
  rw [GridMax.exponential_factor]
  unfold gridBound
  ring

end GMCExplicitDelta.Assembly
