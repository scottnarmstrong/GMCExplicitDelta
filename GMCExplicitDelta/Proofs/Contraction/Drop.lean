module

public import GMCExplicitDelta.Contraction.SequencesExchange

/-! The variable-window version of the T2 drop estimate. -/
@[expose] public section

namespace GMCExplicitDelta.Assembly

open Finset Real GMCContraction

/-- T2 with all admissible Haar depths, including depths exceeding the window start. -/
theorem summed_drop_le {f b y : ℕ → ℝ} {L S T : ℕ} {F t R Sd : ℝ}
    (hanti : ∀ a c, L ≤ a → a ≤ c → f c ≤ f a)
    (hf0 : ∀ n, L ≤ n → 0 ≤ f n) (hfF : ∀ n, L ≤ n → f n ≤ F)
    (hLS : L ≤ S) (hST : S ≤ T) (ht : t * F ≤ f T)
    (hb : ∀ k, 0 ≤ b k)
    (hsd : ∑ k ∈ Icc 1 (T - L), b k * √((k : ℝ) * y k / R) ≤ Sd) :
    ∑ m ∈ Icc S T, √(f m) *
      ∑ k ∈ Icc 1 (m - L), b k * √(y k / R) * √(f (m - k) - f m) ≤
      √(∑ m ∈ Icc S T, f m) * √(F * (1 - t)) * Sd := by
  simp_rw [mul_sum]
  rw [sum_comm' (t' := Icc 1 (T - L)) (s' := fun k => Icc (max S (L + k)) T)
    (fun m k => by simp only [mem_Icc, max_le_iff]; omega)]
  have hcell (k : ℕ) (hk : k ∈ Icc 1 (T - L)) :
      ∑ m ∈ Icc (max S (L + k)) T,
        √(f m) * (b k * √(y k / R) * √(f (m - k) - f m)) ≤
      (√(∑ m ∈ Icc S T, f m) * √(F * (1 - t))) *
        (b k * √((k : ℝ) * y k / R)) := by
    have hm (m : ℕ) (hm : m ∈ Icc (max S (L + k)) T) : L + k ≤ m ∧ S ≤ m := by
      have h := mem_Icc.mp hm
      simp only [max_le_iff] at h
      omega
    have hcs := sum_sqrt_mul_sqrt_le_on (Icc (max S (L + k)) T) (u := f)
      (w := fun m => f (m - k) - f m)
      (fun m h => hf0 m (by have := hm m h; omega))
      (fun m h => sub_nonneg.mpr (hanti _ _ (by have := hm m h; omega) (by omega)))
    have hsub : ∑ m ∈ Icc (max S (L + k)) T, f m ≤ ∑ m ∈ Icc S T, f m :=
      sum_le_sum_of_subset_of_nonneg (fun m h => mem_Icc.mpr ⟨(hm m h).2, (mem_Icc.mp h).2⟩)
        (fun m h _ => hf0 m (by have := mem_Icc.mp h; omega))
    have hdiff := T1_shift hanti hfF hLS hST ht (mem_Icc.mp hk).1
    have hbound := hcs.trans (mul_le_mul (sqrt_le_sqrt hsub) (sqrt_le_sqrt hdiff)
      (sqrt_nonneg _) (sqrt_nonneg _))
    have heq : (∑ m ∈ Icc (max S (L + k)) T,
        √(f m) * (b k * √(y k / R) * √(f (m - k) - f m))) =
        (b k * √(y k / R)) * ∑ m ∈ Icc (max S (L + k)) T,
          √(f m) * √(f (m - k) - f m) := by
      rw [mul_sum]
      exact sum_congr rfl (fun _ _ => by ring)
    rw [heq]
    refine (mul_le_mul_of_nonneg_left hbound (mul_nonneg (hb k) (sqrt_nonneg _))).trans_eq ?_
    rw [sqrt_mul (Nat.cast_nonneg k)]
    have he : (k : ℝ) * y k / R = (k : ℝ) * (y k / R) := by ring
    rw [he, sqrt_mul (Nat.cast_nonneg k)]
    ring
  calc
    _ ≤ ∑ k ∈ Icc 1 (T - L), (√(∑ m ∈ Icc S T, f m) * √(F * (1 - t))) *
        (b k * √((k : ℝ) * y k / R)) := sum_le_sum hcell
    _ = (√(∑ m ∈ Icc S T, f m) * √(F * (1 - t))) *
        ∑ k ∈ Icc 1 (T - L), b k * √((k : ℝ) * y k / R) := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsd (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _))

end GMCExplicitDelta.Assembly
