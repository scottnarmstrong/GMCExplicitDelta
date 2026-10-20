module

public import GMCExplicitDelta.HistoryLane.Sums
public import GMCExplicitDelta.Contract.Obligations

/-!
# History lane: the fine source sum (G5)

`fine_sum_le`: `∑_{r=1}^L (1-w) x^r fineCap(r) ≤ (1+η)C₁D + β_d(1+D)(F̄/(2η) + Ḡ)`.
-/

@[expose] public section

open Real

namespace GMCExplicitDelta.Assembly

open GMCExplicitDelta.Contract GMCExplicitDelta.Certificates

variable {d : ℕ}

theorem xHist_pos' (row : Row d) : 0 < row.xHist := by unfold Row.xHist; positivity

theorem wHaar_lt_one (row : Row d) (hO : row.Obligations) : row.wHaar < 1 := by
  unfold Row.wHaar
  have hs : (0 : ℝ) < (row.s : ℝ) := by exact_mod_cast hO.par1.2.2.2.2.2.1
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

theorem xHist_le_zF (row : Row d) (δ : ℝ) : row.xHist ≤ row.zF δ := by
  unfold Row.zF
  have hx := xHist_pos' row
  have hc : 0 ≤ (128 * (proxyA : ℝ) + 2 * kappaH d) * δ ^ 2 := by
    have : (0 : ℝ) < proxyA := by norm_num [proxyA]
    have : 0 ≤ kappaH d := by unfold kappaH; split_ifs <;> norm_num [kappaQ1]
    positivity
  have := Real.one_le_exp hc
  nlinarith

theorem zG_le_zF (row : Row d) (δ : ℝ) : row.zG δ ≤ row.zF δ := by
  unfold Row.zG Row.zF
  have hx := xHist_pos' row
  have : 0 ≤ kappaH d := by unfold kappaH; split_ifs <;> norm_num [kappaQ1]
  have : (0 : ℝ) < proxyA := by norm_num [proxyA]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hx.le
  nlinarith [sq_nonneg δ]

theorem kappaH_nonneg' (d : ℕ) : 0 ≤ kappaH d := by
  unfold kappaH; split_ifs <;> norm_num [kappaQ1]

theorem fineF_term (row : Row d) (δ : ℝ) (r : ℕ) :
    row.xHist ^ (r + 1) * fineF d δ ((r + 1 : ℕ) : ℝ) =
      row.zF δ ^ (r + 1) * ((Ch * δ ^ 2) * ((r + 1 : ℕ) : ℝ) + AF d δ * ((r + 1 : ℕ) : ℝ) ^ 2) := by
  unfold fineF Row.zF
  rw [mul_pow, ← Real.exp_nat_mul]
  have : Real.exp ((128 * (proxyA : ℝ) + 2 * kappaH d) * ((r + 1 : ℕ) : ℝ) * δ ^ 2) =
      Real.exp (((r + 1 : ℕ) : ℝ) * ((128 * (proxyA : ℝ) + 2 * kappaH d) * δ ^ 2)) := by
    congr 1; ring
  rw [this]; ring

theorem fineG_term (row : Row d) (δ : ℝ) (r : ℕ) :
    row.xHist ^ (r + 1) * fineG d δ ((r + 1 : ℕ) : ℝ) =
      row.zG δ ^ (r + 1) * ((Ch * δ ^ 2) * ((r + 1 : ℕ) : ℝ) + AG d δ * ((r + 1 : ℕ) : ℝ) ^ 2) := by
  unfold fineG Row.zG
  rw [mul_pow, ← Real.exp_nat_mul]
  have : Real.exp ((32 * (proxyA : ℝ) + kappaH d) * ((r + 1 : ℕ) : ℝ) * δ ^ 2) =
      Real.exp (((r + 1 : ℕ) : ℝ) * ((32 * (proxyA : ℝ) + kappaH d) * δ ^ 2)) := by
    congr 1; ring
  rw [this]; ring

theorem fine_sum_le (row : Row d) (hO : row.Obligations) {δ D : ℝ} (hδ : 0 < δ) (hD : 0 ≤ D)
    (hz : row.zF δ < 1) (L : ℕ) :
    ∑ r ∈ Finset.range L, (1 - row.wHaar) * row.xHist ^ (r + 1) *
        fineCap row δ D ((r + 1 : ℕ) : ℝ) ≤
      (1 + (row.eta : ℝ)) * row.C1 * D +
        sphereFactor d * (1 + D) * (row.Fbar δ / (2 * (row.eta : ℝ)) + row.Gbar δ) := by
  have hx := xHist_pos' row
  have hx1 : row.xHist < 1 := lt_of_le_of_lt (xHist_le_zF row δ) hz
  have hw1 := wHaar_lt_one row hO
  have hw0 : 0 ≤ row.wHaar := by unfold Row.wHaar; positivity
  have hη : 0 < (row.eta : ℝ) := by exact_mod_cast hO.par3.1
  have hβ := sphereFactor_nonneg d
  have hCh : 0 ≤ Ch := Ch_nonneg
  have hAF := AF_nonneg (d := d) hδ.le
  have hAG := AG_nonneg (d := d) hδ.le
  have hzF0 : 0 ≤ row.zF δ := le_trans hx.le (xHist_le_zF row δ)
  have hzG0 : 0 ≤ row.zG δ := by unfold Row.zG; positivity
  have hzG1 : row.zG δ < 1 := lt_of_le_of_lt (zG_le_zF row δ) hz
  have hterm : ∀ r : ℕ, (1 - row.wHaar) * row.xHist ^ (r + 1) * fineCap row δ D ((r + 1 : ℕ) : ℝ) =
      ((1 - row.wHaar) * (1 + (row.eta : ℝ)) * D) * row.xHist ^ (r + 1) +
      ((1 - row.wHaar) * sphereFactor d * (1 + D) / (2 * (row.eta : ℝ))) * (row.xHist ^ (r + 1) * fineF d δ ((r + 1 : ℕ) : ℝ)) +
      ((1 - row.wHaar) * sphereFactor d * (1 + D)) * (row.xHist ^ (r + 1) * fineG d δ ((r + 1 : ℕ) : ℝ)) := by
    intro r; unfold fineCap; field_simp; ring
  simp only [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [fineF_term, fineG_term]
  have hS1 : ∑ r ∈ Finset.range L, row.xHist ^ (r + 1) ≤ row.xHist / (1 - row.xHist) := by
    have := geom_partial_le hx.le hx1 L
    calc ∑ r ∈ Finset.range L, row.xHist ^ (r + 1) = row.xHist * ∑ r ∈ Finset.range L, row.xHist ^ r := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun r _ => by ring
      _ ≤ row.xHist * (1 / (1 - row.xHist)) := by gcongr
      _ = _ := by ring
  have hSF := HistoryLane.fine_series_le (C := Ch * δ ^ 2) (A := AF d δ) hzF0 hz
    (by positivity) hAF L
  have hSG := HistoryLane.fine_series_le (C := Ch * δ ^ 2) (A := AG d δ) hzG0 hzG1
    (by positivity) hAG L
  have h1w : 0 ≤ 1 - row.wHaar := by linarith
  have c1 : 0 ≤ (1 - row.wHaar) * (1 + (row.eta : ℝ)) * D := by positivity
  have c2 : 0 ≤ (1 - row.wHaar) * sphereFactor d * (1 + D) / (2 * (row.eta : ℝ)) := by positivity
  have c3 : 0 ≤ (1 - row.wHaar) * sphereFactor d * (1 + D) := by positivity
  have e1 : row.C1 = (1 - row.wHaar) / (1 - row.xHist) * row.xHist := rfl
  have key : (1 - row.wHaar) * (1 + (row.eta : ℝ)) * D * (row.xHist / (1 - row.xHist)) = (1 + (row.eta : ℝ)) * row.C1 * D := by
    rw [e1]; ring
  have kF : (1 - row.wHaar) * sphereFactor d * (1 + D) / (2 * (row.eta : ℝ)) *
      (Ch * δ ^ 2 * (row.zF δ / (1 - row.zF δ) ^ 2) +
        AF d δ * (row.zF δ * (1 + row.zF δ) / (1 - row.zF δ) ^ 3)) =
      sphereFactor d * (1 + D) * (row.Fbar δ / (2 * (row.eta : ℝ))) := by
    unfold Row.Fbar; field_simp
  have kG : (1 - row.wHaar) * sphereFactor d * (1 + D) *
      (Ch * δ ^ 2 * (row.zG δ / (1 - row.zG δ) ^ 2) +
        AG d δ * (row.zG δ * (1 + row.zG δ) / (1 - row.zG δ) ^ 3)) =
      sphereFactor d * (1 + D) * row.Gbar δ := by
    unfold Row.Gbar; ring
  calc _ ≤ ((1 - row.wHaar) * (1 + (row.eta : ℝ)) * D) * (row.xHist / (1 - row.xHist)) +
        ((1 - row.wHaar) * sphereFactor d * (1 + D) / (2 * (row.eta : ℝ))) *
          (Ch * δ ^ 2 * (row.zF δ / (1 - row.zF δ) ^ 2) +
            AF d δ * (row.zF δ * (1 + row.zF δ) / (1 - row.zF δ) ^ 3)) +
        ((1 - row.wHaar) * sphereFactor d * (1 + D)) *
          (Ch * δ ^ 2 * (row.zG δ / (1 - row.zG δ) ^ 2) +
            AG d δ * (row.zG δ * (1 + row.zG δ) / (1 - row.zG δ) ^ 3)) := by
        gcongr
    _ = _ := by rw [key, kF, kG]; ring

end GMCExplicitDelta.Assembly
