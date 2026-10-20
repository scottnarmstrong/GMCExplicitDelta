module

public import GMCExplicitDelta.Proofs.Contraction.Haar
public import GMCExplicitDelta.Proofs.Contraction.Matching

/-! Signs and matching comparisons for the terminal summation. -/
@[expose] public section

namespace GMCExplicitDelta.Assembly

open Contract Haar Real

variable {d : ℕ}

theorem terminal_constants (row : Row d) (hO : row.Obligations) {F : ℝ} (hF : 0 < F) :
    0 < row.tStar ∧ row.tStar < 1 ∧ 0 < row.cNu ∧
      0 ≤ row.coefA F ∧ 0 ≤ row.coefAv ∧ 0 ≤ row.coefB F ∧
      0 < row.rStar F ∧ 0 < row.qStar F := by
  have hM : 0 < (row.Mwin : ℝ) := by unfold Row.Mwin; positivity
  have ht0 : 0 < row.tStar := div_pos (by exact_mod_cast hO.bar1.1) hM
  have ht1 : row.tStar < 1 := (div_lt_one hM).2 hO.bar1.2.1
  have hc : 0 < row.cNu := pow_pos hO.geo1.1 _
  have he : 0 < (row.epsilon : ℝ) := by exact_mod_cast hO.par2.2.1
  have hR : 0 < (row.R : ℝ) := by have := hO.par2.1; exact_mod_cast (lt_trans (by norm_num : (0 : ℚ) < 1) this)
  have hu : 0 ≤ row.uStar F := mul_nonneg ht0.le hF.le
  refine ⟨ht0, ht1, hc, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Row.coefA sigmaA
    split <;> positivity
  · unfold Row.coefAv sigmaV
    split <;> positivity
  · unfold Row.coefB sigmaB
    split <;> positivity
  · unfold Row.rStar
    split
    · exact rMatch_pos hu
    · norm_num
  · unfold Row.qStar
    split
    · exact qMatch_pos hu
    · norm_num

theorem matching_comparison (row : Row d) {F x : ℝ} (hF1 : F ≤ 1)
    (ht0 : 0 ≤ row.tStar) (hF0 : 0 ≤ F) (hx : row.tStar * F ≤ x) (hxF : x ≤ F) :
    0 ≤ qPair d x ∧ qPair d x ≤ row.qStar F ∧
      0 < rPair d x ∧ row.rStar F ≤ rPair d x := by
  have hu : 0 ≤ row.uStar F := mul_nonneg ht0 hF0
  have hx0 : 0 ≤ x := hu.trans hx
  unfold qPair rPair Row.qStar Row.rStar
  split_ifs with hd
  · exact ⟨(qMatch_pos hx0).le, qMatch_antitone hu hx (hxF.trans hF1), rMatch_pos hx0, rMatch_mono hu hx⟩
  · exact ⟨by norm_num, le_rfl, by norm_num, le_rfl⟩

end GMCExplicitDelta.Assembly
