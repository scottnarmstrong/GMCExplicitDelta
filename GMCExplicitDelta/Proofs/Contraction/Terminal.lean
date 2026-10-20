module

public import GMCExplicitDelta.Proofs.Contraction.Variance
public import GMCExplicitDelta.Proofs.Contraction.Drop

/-! The terminal barrier from the normalized per-scale inequalities (T1–T3). -/
@[expose] public section

namespace GMCExplicitDelta.Assembly

open Contract Haar Real Finset GMCContraction

variable {d : ℕ}

theorem terminal_lt_of_perScale_proof (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ))
    (hO : row.Obligations) {D F bd : ℝ} (hD : 0 < D) (hF : 0 < F) (hF1 : F ≤ 1)
    (hbd : bd ≤ row.badBudget) (hbar : 0 < row.barrier D F) {f V : ℕ → ℝ} {L : ℕ}
    (hanti : ∀ a b, L ≤ a → a ≤ b → f b ≤ f a) (hf0 : ∀ n, L ≤ n → 0 ≤ f n)
    (hfF : ∀ n, L ≤ n → f n ≤ F)
    (hV : GMCContraction.VarBudget f V L (ellV d) row.rhoV row.cV F (vi D F))
    (hL6 : ∀ m', L + row.g ≤ m' → m' ≤ L + row.h → 0 < f m' → PerScaleIneq row f V L F bd m') :
    f (L + row.h) < row.Fnext F := by
  have _hD := hD
  by_contra hcon
  have ht : row.tStar * F ≤ f (L + row.h) := le_of_not_gt hcon
  obtain ⟨ht0, ht1, hc, hA, hAv, hB, hr, hq⟩ := terminal_constants row hO hF
  obtain ⟨hb, hsb, hbt, hsd, _⟩ := haarB_sums_proof row hd hO
  have hgh := hO.par1.2.2.2.2.1
  have hnug : row.nu ≤ row.g := le_trans (le_max_left _ _) hO.par1.2.2.2.1
  let S := L + row.g
  let T := L + row.h
  let W := Icc S T
  let X : ℝ := ∑ m ∈ W, f m
  let dr : ℕ → ℝ := fun m => ∑ k ∈ Icc 1 (m - L),
    row.haarB k * √(row.yk k / (row.R : ℝ)) * √(f (m - k) - f m)
  let vr : ℕ → ℝ := fun m => ∑ k ∈ range (m - L + 1), row.haarB k * √(V (m - k))
  let nr : ℕ → ℝ := fun m => f (m - row.nu) - f m
  have hm (m : ℕ) (hm : m ∈ W) : L ≤ m ∧ S ≤ m ∧ m ≤ T := by
    have := mem_Icc.mp hm
    dsimp [S, T] at *
    omega
  have hterminal (m : ℕ) (hm' : m ∈ W) : row.tStar * F ≤ f m :=
    ht.trans (hanti m T (hm m hm').1 (hm m hm').2.2)
  have hdr (m : ℕ) : 0 ≤ dr m := sum_nonneg (fun k _ =>
    mul_nonneg (mul_nonneg (hb k) (sqrt_nonneg _)) (sqrt_nonneg _))
  have hvr (m : ℕ) : 0 ≤ vr m := sum_nonneg (fun k _ => mul_nonneg (hb k) (sqrt_nonneg _))
  have hnr (m : ℕ) (hm' : m ∈ W) : 0 ≤ nr m := by
    exact sub_nonneg.mpr (hanti (m - row.nu) m (by have := hm m hm'; dsimp [S] at this; omega) (by omega))
  have hpoint (m : ℕ) (hm' : m ∈ W) :
      (1 - row.tauAbs) * f m ≤
        (row.coefA F * √(row.qStar F)) * (√(f m) * dr m) +
        (row.coefAv / √(row.rStar F)) * (√(f m) * vr m) +
        (row.coefB F * row.qStar F) * nr m + F * row.badBudget := by
    have hmf := hf0 m (hm m hm').1
    obtain ⟨hqp, hqle, hrp, hrle⟩ := matching_comparison row hF1 ht0.le hF.le
      (hterminal m hm') (hfF m (hm m hm').1)
    have hqroot : √(qPair d (f m) * f m) ≤ √(row.qStar F) * √(f m) := by
      rw [sqrt_mul hqp]
      exact mul_le_mul_of_nonneg_right (sqrt_le_sqrt hqle) (sqrt_nonneg _)
    have hvroot : row.coefAv * √(f m) / √(rPair d (f m)) ≤
        row.coefAv / √(row.rStar F) * √(f m) := by
      have h := div_le_div_of_nonneg_left (mul_nonneg hAv (sqrt_nonneg (f m)))
        (sqrt_pos.mpr hr) (sqrt_le_sqrt hrle)
      convert h using 1
      ring
    have h := hL6 m (hm m hm').2.1 (hm m hm').2.2
      (lt_of_lt_of_le (mul_pos ht0 hF) (hterminal m hm'))
    unfold PerScaleIneq at h
    change (1 - row.tauAbs) * f m ≤ _ + _ + row.coefB F * qPair d (f m) * nr m + F * bd at h
    refine h.trans (add_le_add (add_le_add (add_le_add ?_ ?_) ?_) ?_)
    · convert mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hqroot hA) (hdr m) using 1; ring
    · convert mul_le_mul_of_nonneg_right hvroot (hvr m) using 1; ring
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hqle hB) (hnr m hm')
    · exact mul_le_mul_of_nonneg_left hbd hF.le
  have hcard : W.card = row.Mwin := by
    dsimp [W, S, T]
    rw [Nat.card_Icc]
    unfold Row.Mwin
    omega
  have hX : F * (row.Z : ℝ) ≤ X := by
    have h := sum_le_sum (s := W) (fun m hm' => hterminal m hm')
    simp only [sum_const, nsmul_eq_mul, hcard] at h
    have heq : (row.Mwin : ℝ) * (row.tStar * F) = F * (row.Z : ℝ) := by
      unfold Row.tStar
      have hM : (row.Mwin : ℝ) ≠ 0 := by unfold Row.Mwin; positivity
      field_simp
    rwa [heq] at h
  have hdrop := summed_drop_le hanti hf0 hfF (S := S) (T := T) (by dsimp [S]; omega)
    (by dsimp [S, T]; omega) ht hb (hsd (T - L))
  have hvar := row_variance_window row hd hO hF hV ht0.le ht
  have hnu : ∑ m ∈ W, nr m ≤ (row.nu : ℝ) * (F * (1 - row.tStar)) := by
    by_cases hn : row.nu = 0
    · simp only [nr, hn, Nat.sub_zero, sub_self, sum_const_zero, Nat.cast_zero, zero_mul, le_refl]
    · exact T1_nu hanti hfF (by dsimp [T]; omega) ht (by omega) hnug
  have hsum := sum_le_sum hpoint
  simp only [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul, hcard] at hsum
  have h1 := mul_le_mul_of_nonneg_left hdrop (mul_nonneg hA (sqrt_nonneg (row.qStar F)))
  have h2 := mul_le_mul_of_nonneg_left hvar (div_nonneg hAv (sqrt_nonneg (row.rStar F)))
  have h3 := mul_le_mul_of_nonneg_left hnu (mul_nonneg hB hq.le)
  have heq : (row.coefA F * √(row.qStar F)) *
        (√X * √(F * (1 - row.tStar)) * row.Sd) +
      (row.coefAv / √(row.rStar F)) *
        (√X * √F * (row.Sb * √(row.Qt0 D F + row.Qfor F * (1 - row.tStar ^ 2)) +
          row.Btail * √(row.Qf0 D F + row.Qfor F * (1 - row.tStar ^ 2)))) +
      (row.coefB F * row.qStar F) * ((row.nu : ℝ) * (F * (1 - row.tStar))) +
      (row.Mwin : ℝ) * (F * row.badBudget) =
      (row.Cbar D F * √F) * √X +
        F * ((row.nu : ℝ) * row.coefB F * (1 - row.tStar) * row.qStar F +
          (row.Mwin : ℝ) * row.badBudget) := by
    rw [sqrt_mul hF.le]
    unfold Row.Cbar
    ring
  have hfinal : (1 - row.tauAbs) * X ≤ (row.Cbar D F * √F) * √X +
      F * ((row.nu : ℝ) * row.coefB F * (1 - row.tStar) * row.qStar F +
        (row.Mwin : ℝ) * row.badBudget) := by
    rw [← heq]
    exact hsum.trans (add_le_add (add_le_add (add_le_add h1 h2) h3) (le_of_eq (by ring)))
  have hSb : 0 ≤ row.Sb := by simpa only [range_zero, sum_empty] using hsb 0
  have hSd : 0 ≤ row.Sd := by simpa only [Icc_eq_empty_of_lt (by omega : (0 : ℕ) < 1), sum_empty] using hsd 0
  have hBt : 0 ≤ row.Btail := by simpa only [Ioc_self, sum_empty] using hbt row.Kprime
  have hC : 0 ≤ row.Cbar D F := by unfold Row.Cbar; positivity
  have hbad : 0 ≤ (row.badBudget : ℝ) := by exact_mod_cast hO.par2.2.2.2.2.1.le
  have hc0 : 0 ≤ (row.nu : ℝ) * row.coefB F * (1 - row.tStar) * row.qStar F +
      (row.Mwin : ℝ) * row.badBudget := by positivity
  have hscaled : 0 < (1 - row.tauAbs) * (F * (row.Z : ℝ)) -
      (row.Cbar D F * √F) * √(F * (row.Z : ℝ)) -
      F * ((row.nu : ℝ) * row.coefB F * (1 - row.tStar) * row.qStar F +
        (row.Mwin : ℝ) * row.badBudget) := by
    rw [sqrt_mul hF.le]
    convert mul_pos hF hbar using 1
    unfold Row.barrier
    ring_nf
    rw [sq_sqrt hF.le]
    ring
  exact T3_false hO.geo4.1.le hO.geo4.2 (mul_nonneg hC (sqrt_nonneg _))
    (mul_nonneg hF.le hc0) (mul_pos hF (by exact_mod_cast hO.bar1.1)) hscaled hX hfinal

end GMCExplicitDelta.Assembly
