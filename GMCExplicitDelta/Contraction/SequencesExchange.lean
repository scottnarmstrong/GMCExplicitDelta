module

public import GMCExplicitDelta.Contraction.SequencesBudget

/-!
# Exchange of summation and Cauchy-Schwarz (step V5)

Abstract inequality
`∑_{m=S}^T √(f m) ∑_{k=0}^{m-L} b_k √(V(m-k)) ≤ (∑ f)^{1/2} ∑_k b_k (∑_m V(m-k))^{1/2}`
and its split at `K'`.
-/

@[expose] public section

namespace GMCContraction

open Finset

/-- Cauchy-Schwarz for square roots with nonnegativity only on the index set. -/
theorem sum_sqrt_mul_sqrt_le_on {ι : Type*} (s : Finset ι) {u w : ι → ℝ}
    (hu : ∀ i ∈ s, 0 ≤ u i) (hw : ∀ i ∈ s, 0 ≤ w i) :
    ∑ i ∈ s, √(u i) * √(w i) ≤ √(∑ i ∈ s, u i) * √(∑ i ∈ s, w i) := by
  have h := Real.sum_sqrt_mul_sqrt_le s (f := fun i => max (u i) 0) (g := fun i => max (w i) 0)
    (fun i => le_max_right _ _) (fun i => le_max_right _ _)
  have e1 : ∑ i ∈ s, max (u i) 0 = ∑ i ∈ s, u i := sum_congr rfl fun i hi => max_eq_left (hu i hi)
  have e2 : ∑ i ∈ s, max (w i) 0 = ∑ i ∈ s, w i := sum_congr rfl fun i hi => max_eq_left (hw i hi)
  have e3 : ∑ i ∈ s, √(u i) * √(w i) = ∑ i ∈ s, √(max (u i) 0) * √(max (w i) 0) :=
    sum_congr rfl fun i hi => by rw [max_eq_left (hu i hi), max_eq_left (hw i hi)]
  rw [e3]; rwa [e1, e2] at h

/-- Shifting a window of a nonnegative sequence into a larger window. -/
theorem sum_Icc_shift_le_of_nonneg {V : ℕ → ℝ} {L : ℕ} (hV : ∀ n, L ≤ n → 0 ≤ V n)
    {a c k T : ℕ} (hk : k ≤ a) (hc : c ≤ a - k) (hLc : L ≤ c) :
    ∑ m ∈ Icc a T, V (m - k) ≤ ∑ n ∈ Icc c T, V n := by
  have hinj : Set.InjOn (fun m => m - k) (Icc a T : Set ℕ) := fun x hx y hy h => by
    simp only [coe_Icc, Set.mem_Icc] at hx hy
    simp only at h; omega
  rw [← sum_image hinj]
  refine sum_le_sum_of_subset_of_nonneg ?_ fun n hn _ => hV n (by
    have := mem_Icc.mp hn; omega)
  intro n hn
  obtain ⟨m, hm, rfl⟩ := mem_image.mp hn
  have := mem_Icc.mp hm
  exact mem_Icc.mpr ⟨by omega, by omega⟩

/-- **V5 (exchange + Cauchy-Schwarz)**; the inner `m`-range for fixed `k` is
`Icc (max S (L+k)) T`. -/
theorem V5_exchange {f V b : ℕ → ℝ} {L S T : ℕ} (hLS : L ≤ S)
    (hf : ∀ n, L ≤ n → 0 ≤ f n) (hV : ∀ n, L ≤ n → 0 ≤ V n) (hb : ∀ k, 0 ≤ b k) :
    ∑ m ∈ Icc S T, √(f m) * ∑ k ∈ range (m - L + 1), b k * √(V (m - k)) ≤
      √(∑ m ∈ Icc S T, f m) *
        ∑ k ∈ range (T - L + 1),
          b k * √(∑ m ∈ Icc (max S (L + k)) T, V (m - k)) := by
  simp_rw [mul_sum]
  rw [sum_comm' (t' := range (T - L + 1)) (s' := fun k => Icc (max S (L + k)) T)
    (fun m k => by simp only [mem_Icc, mem_range, max_le_iff]; omega)]
  refine sum_le_sum fun k hk => ?_
  have hk' := mem_range.mp hk
  have hmem : ∀ m ∈ Icc (max S (L + k)) T, L + k ≤ m ∧ S ≤ m := fun m hm => by
    have := mem_Icc.mp hm
    simp only [max_le_iff] at this
    omega
  have hcs := sum_sqrt_mul_sqrt_le_on (Icc (max S (L + k)) T) (u := f) (w := fun m => V (m - k))
    (fun m hm => hf m (by have := hmem m hm; omega))
    (fun m hm => hV _ (by have := hmem m hm; omega))
  have e : ∑ m ∈ Icc (max S (L + k)) T, √(f m) * (b k * √(V (m - k))) =
      b k * ∑ m ∈ Icc (max S (L + k)) T, √(f m) * √(V (m - k)) := by
    rw [mul_sum]; exact sum_congr rfl fun m _ => by ring
  rw [e]
  have hsub : ∑ m ∈ Icc (max S (L + k)) T, f m ≤ ∑ m ∈ Icc S T, f m :=
    sum_le_sum_of_subset_of_nonneg (fun m hm => by
      have := mem_Icc.mp hm
      simp only [max_le_iff] at this
      exact mem_Icc.mpr ⟨by omega, this.2⟩)
      fun m hm _ => hf m (by have := mem_Icc.mp hm; omega)
  calc b k * ∑ m ∈ Icc (max S (L + k)) T, √(f m) * √(V (m - k))
      ≤ b k * (√(∑ m ∈ Icc (max S (L + k)) T, f m) *
          √(∑ m ∈ Icc (max S (L + k)) T, V (m - k))) :=
        mul_le_mul_of_nonneg_left hcs (hb k)
    _ ≤ b k * (√(∑ m ∈ Icc S T, f m) * √(∑ m ∈ Icc (max S (L + k)) T, V (m - k))) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hsub)
          (Real.sqrt_nonneg _)) (hb k)
    _ = √(∑ m ∈ Icc S T, f m) * (b k * √(∑ m ∈ Icc (max S (L + k)) T, V (m - k))) := by ring

/-- **V5 (split at `K'`)**: with `S = L + K' + j`, `j ≥ 1`, window bounds `W1`, `W2` for
`∑_{n=L+j}^T V` and `∑_{n=L}^T V`, and bounds `Sb`, `Bt` for `∑_{k ≤ K'} b_k`,
`∑_{K' < k ≤ T-L} b_k`. -/
theorem V5_split {f V b : ℕ → ℝ} {L K' j S T : ℕ} {W1 W2 Sb Bt : ℝ}
    (hS : S = L + K' + j) (hj : 1 ≤ j)
    (hf : ∀ n, L ≤ n → 0 ≤ f n) (hV : ∀ n, L ≤ n → 0 ≤ V n) (hb : ∀ k, 0 ≤ b k)
    (hW1 : ∑ n ∈ Icc (L + j) T, V n ≤ W1) (hW2 : ∑ n ∈ Icc L T, V n ≤ W2)
    (hSb : ∑ k ∈ (range (T - L + 1)).filter (fun k => k ≤ K'), b k ≤ Sb)
    (hBt : ∑ k ∈ (range (T - L + 1)).filter (fun k => ¬ k ≤ K'), b k ≤ Bt) :
    ∑ m ∈ Icc S T, √(f m) * ∑ k ∈ range (m - L + 1), b k * √(V (m - k)) ≤
      √(∑ m ∈ Icc S T, f m) * (Sb * √W1 + Bt * √W2) := by
  have h := V5_exchange (f := f) (V := V) (b := b) (L := L) (S := S) (T := T)
    (by omega) hf hV hb
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
  rw [← sum_filter_add_sum_filter_not (range (T - L + 1)) (fun k => k ≤ K')]
  have h1 : ∑ k ∈ (range (T - L + 1)).filter (fun k => k ≤ K'),
      b k * √(∑ m ∈ Icc (max S (L + k)) T, V (m - k)) ≤
      ∑ k ∈ (range (T - L + 1)).filter (fun k => k ≤ K'), b k * √W1 := by
    refine sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (hb k)
    have := (mem_filter.mp hk).2
    refine le_trans (sum_Icc_shift_le_of_nonneg hV (c := L + j) (by omega) (by omega)
      (by omega)) hW1
  have h2 : ∑ k ∈ (range (T - L + 1)).filter (fun k => ¬ k ≤ K'),
      b k * √(∑ m ∈ Icc (max S (L + k)) T, V (m - k)) ≤
      ∑ k ∈ (range (T - L + 1)).filter (fun k => ¬ k ≤ K'), b k * √W2 := by
    refine sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (hb k)
    refine le_trans (sum_Icc_shift_le_of_nonneg hV (c := L) (by omega) (by omega)
      le_rfl) hW2
  rw [← sum_mul] at h1 h2
  have := Real.sqrt_nonneg W1
  have := Real.sqrt_nonneg W2
  nlinarith

end GMCContraction
