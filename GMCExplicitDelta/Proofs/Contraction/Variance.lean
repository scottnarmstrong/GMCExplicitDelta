module

public import GMCExplicitDelta.Proofs.Contraction.Constants
public import GMCExplicitDelta.Contraction.SequencesExchange

/-! V4 and V5 at the row's exact split and variance constants. -/
@[expose] public section

namespace GMCExplicitDelta.Assembly

open Contract Real Finset GMCContraction

variable {d : ℕ}

theorem row_variance_window (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ))
    (hO : row.Obligations) {D F : ℝ} (hF : 0 < F) {f V : ℕ → ℝ} {L : ℕ}
    (hV : VarBudget f V L (ellV d) row.rhoV row.cV F (vi D F))
    (ht0 : 0 ≤ row.tStar) (ht : row.tStar * F ≤ f (L + row.h)) :
    ∑ m ∈ Icc (L + row.g) (L + row.h), √(f m) *
      ∑ k ∈ range (m - L + 1), row.haarB k * √(V (m - k)) ≤
      √(∑ m ∈ Icc (L + row.g) (L + row.h), f m) * √F *
        (row.Sb * √(row.Qt0 D F + row.Qfor F * (1 - row.tStar ^ 2)) +
          row.Btail * √(row.Qf0 D F + row.Qfor F * (1 - row.tStar ^ 2))) := by
  obtain ⟨hb, hsb, hbt, _, _⟩ := haarB_sums_proof row hd hO
  have hg2 : 2 ≤ row.g := le_trans (le_max_right _ _) hO.par1.2.2.2.1
  have hj : 1 ≤ row.jV := by unfold Row.jV; split_ifs <;> omega
  have hsplit : L + row.g = L + row.Kprime + row.jV := by
    unfold Row.Kprime Row.jV
    split_ifs <;> omega
  have hdef := sq_defect_le ht0 hF.le ht
  have hden : 0 < 1 - row.rhoV := sub_pos.mpr hV.rho_lt
  have hfor : (ellV d : ℝ) * row.cV * (F ^ 2 - f (L + row.h) ^ 2) / (1 - row.rhoV) ≤
      F * (row.Qfor F * (1 - row.tStar ^ 2)) := by
    have hm := mul_le_mul_of_nonneg_left hdef
      (div_nonneg (mul_nonneg (Nat.cast_nonneg (ellV d)) hV.c_nonneg) hden.le)
    convert hm using 1
    · ring
    · unfold Row.Qfor
      ring
  have htbound : ∑ n ∈ Icc (L + row.jV) (L + row.h), V n ≤
      F * (row.Qt0 D F + row.Qfor F * (1 - row.tStar ^ 2)) := by
    have h := hV.sum_tail_le (T' := L + row.h) (by omega) hj
    change _ ≤ F * row.Qt0 D F + _ at h
    exact (h.trans (add_le_add le_rfl hfor)).trans_eq (by ring)
  have hfbound : ∑ n ∈ Icc L (L + row.h), V n ≤
      F * (row.Qf0 D F + row.Qfor F * (1 - row.tStar ^ 2)) := by
    have h := hV.sum_full_le (T' := L + row.h) (by omega)
    change _ ≤ F * row.Qf0 D F + _ at h
    exact (h.trans (add_le_add le_rfl hfor)).trans_eq (by ring)
  have hs : ∑ k ∈ (range (L + row.h - L + 1)).filter (fun k => k ≤ row.Kprime), row.haarB k ≤ row.Sb := by
    exact (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun k _ _ => hb k)).trans (hsb _)
  have hb' : ∑ k ∈ (range (L + row.h - L + 1)).filter (fun k => ¬ k ≤ row.Kprime), row.haarB k ≤ row.Btail := by
    have heq : (range (L + row.h - L + 1)).filter (fun k => ¬ k ≤ row.Kprime) =
        Ioc row.Kprime (L + row.h - L) := by
      ext k
      simp only [mem_filter, mem_range, mem_Ioc]
      omega
    rw [heq]
    exact hbt _
  have h := V5_split hsplit hj hV.f_nonneg hV.V_nonneg hb htbound hfbound hs hb'
  refine h.trans_eq ?_
  rw [sqrt_mul hF.le, sqrt_mul hF.le]
  ring

end GMCExplicitDelta.Assembly
