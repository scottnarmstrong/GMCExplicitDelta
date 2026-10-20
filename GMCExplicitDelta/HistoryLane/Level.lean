module

public import GMCExplicitDelta.HistoryLane.Norm
public import GMCExplicitDelta.Contract.DerivedGeometry
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import GMCExplicitDelta.Assembly.ModelEvents

/-!
# History lane: union bound over the cells of one depth

`level_norm_le`: if every cell of depth `j` has `‖X_R‖_{32} ≤ B`, the maximum over the `3^{dj}` cells has
norm `≤ 3^{dj/32} B`; and `w^j 3^{dj/32} = x^j` (`w_mul_rootCard`).
-/

@[expose] public section

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab Homogenization
open scoped ENNReal

namespace GMCExplicitDelta.HistoryLane

/-- `3^{dj/32} = (3^{dj})^{1/32}`. -/
noncomputable def rootCard (d j : ℕ) : ℝ := (((3 : ℝ) ^ d) ^ j) ^ ((1 : ℝ) / 32)

theorem rootCard_nonneg (d j : ℕ) : 0 ≤ rootCard d j := by unfold rootCard; positivity

theorem w_mul_rootCard {d : ℕ} (row : GMCExplicitDelta.Contract.Row d) (j : ℕ) :
    row.wHaar ^ j * rootCard d j = row.xHist ^ j := by
  set u : ℝ := (3 : ℝ) ^ ((d : ℝ) / 32) with hu0
  have hu : u ^ 32 = (3 : ℝ) ^ d := by
    rw [hu0, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    rw [show ((d : ℝ) / 32 * ((32 : ℕ) : ℝ)) = ((d : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hupos : 0 ≤ u := by positivity
  have hrc : rootCard d j = u ^ j := by
    unfold rootCard
    rw [← hu, ← pow_mul, mul_comm 32 j, pow_mul, one_div]
    exact_mod_cast Real.pow_rpow_inv_natCast (pow_nonneg hupos j) (by norm_num : (32 : ℕ) ≠ 0)
  have hx : row.xHist = row.wHaar * u := by
    unfold GMCExplicitDelta.Contract.Row.xHist GMCExplicitDelta.Contract.Row.wHaar
    rw [Real.rpow_add (by norm_num)]
  rw [hrc, hx, mul_pow]

theorem card_rpow_eq (d j : ℕ) :
    ((((3 ^ d) ^ j : ℕ) : ℝ≥0∞)) ^ ((1 : ℝ) / 32) = ENNReal.ofReal (rootCard d j) := by
  rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
  unfold rootCard; push_cast; rfl

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {d : ℕ}

theorem level_norm_le (Q : Homogenization.TriadicCube d) (j : ℕ)
    (X : Homogenization.TriadicCube d → Ω → ℝ≥0∞)
    (hX : ∀ R ∈ descendantsAtDepth Q j, AEMeasurable (X R) μ) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ R ∈ descendantsAtDepth Q j, paperENNRealLpNorm μ 32 (X R) ≤ ENNReal.ofReal B) :
    paperENNRealLpNorm μ 32 (fun ω => (descendantsAtDepth Q j).sup fun R => X R ω) ≤
      ENNReal.ofReal (rootCard d j * B) := by
  refine (lnorm_finset_sup_le (by norm_num) _ X hX h).trans ?_
  rw [descendantsAtDepth_card, card_rpow_eq, ← ENNReal.ofReal_mul (rootCard_nonneg d j)]

end GMCExplicitDelta.HistoryLane
