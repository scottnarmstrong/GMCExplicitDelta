module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Abstract real-sequence lemmas: finite-window telescopes, Cauchy-Schwarz drop, barrier

T1, T2 (drop term), T3.  Sequences are `ℕ → ℝ`; no GMC objects.
-/

@[expose] public section

namespace GMCContraction

open Finset

/-- Shifted-difference identity: `∑_{x<n} (g(p+x) - g(p+x+k)) = ∑_{j<k} g(p+j) - ∑_{j<k} g(p+n+j)`. -/
theorem sum_range_shift_sub (g : ℕ → ℝ) (p k n : ℕ) :
    ∑ x ∈ range n, (g (p + x) - g (p + x + k)) =
      ∑ j ∈ range k, g (p + j) - ∑ j ∈ range k, g (p + n + j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    have h1 := sum_range_succ (fun j => g (p + n + j)) k
    have h2 := sum_range_succ' (fun j => g (p + n + j)) k
    have h3 : ∑ j ∈ range k, g (p + (n + 1) + j) = ∑ j ∈ range k, g (p + n + (j + 1)) :=
      sum_congr rfl fun j _ => by congr 1; omega
    rw [h3]
    simp only [add_zero] at h2
    linarith

/-- Range form of the finite-window telescope. -/
theorem sum_range_shift_le {g : ℕ → ℝ} {G : ℝ} {L' : ℕ}
    (hanti : ∀ a b, L' ≤ a → a ≤ b → g b ≤ g a) (hbd : ∀ m, L' ≤ m → g m ≤ G)
    {p k n T : ℕ} (hp : L' ≤ p) (hT : p + n + k ≤ T + 1) :
    ∑ x ∈ range n, (g (p + x) - g (p + x + k)) ≤ k * (G - g T) := by
  rw [sum_range_shift_sub]
  have h1 : ∑ j ∈ range k, g (p + j) ≤ k * G := by
    calc ∑ j ∈ range k, g (p + j) ≤ ∑ _j ∈ range k, G :=
          sum_le_sum fun j _ => hbd _ (by omega)
      _ = k * G := by simp
  have h2 : (k : ℝ) * g T ≤ ∑ j ∈ range k, g (p + n + j) := by
    calc (k : ℝ) * g T = ∑ _j ∈ range k, g T := by simp
      _ ≤ _ := sum_le_sum fun j hj => by
        have := mem_range.mp hj
        exact hanti _ _ (by omega) (by omega)
  linarith

/-- Icc form of the finite-window telescope for a general nonincreasing `g ≤ G`. -/
theorem sum_Icc_shift_le {g : ℕ → ℝ} {G : ℝ} {L : ℕ}
    (hanti : ∀ a b, L ≤ a → a ≤ b → g b ≤ g a) (hbd : ∀ m, L ≤ m → g m ≤ G)
    {k a T : ℕ} (hk : 1 ≤ k) (ha : L + k ≤ a) (hT : L ≤ T) :
    ∑ m ∈ Icc a T, (g (m - k) - g m) ≤ k * (G - g T) := by
  rcases lt_or_ge T a with h | h
  · rw [Icc_eq_empty_of_lt h, sum_empty]
    have := hbd T hT
    have : (0:ℝ) ≤ k := by positivity
    nlinarith
  · have hI : Icc a T = Ico a (T + 1) := by ext; simp
    rw [hI, sum_Ico_eq_sum_range]
    have := sum_range_shift_le (p := a - k) (n := T + 1 - a) (k := k) (T := T) hanti hbd
      (by omega) (by omega)
    refine le_trans (le_of_eq (sum_congr rfl fun x _ => ?_)) this
    have e1 : a + x - k = a - k + x := by omega
    have e2 : a - k + x + k = a + x := by omega
    rw [e1, e2]

/-- **T1** (first form). -/
theorem T1_shift {f : ℕ → ℝ} {F t : ℝ} {L S T k : ℕ}
    (hanti : ∀ a b, L ≤ a → a ≤ b → f b ≤ f a)
    (hF : ∀ n, L ≤ n → f n ≤ F) (hLS : L ≤ S) (hST : S ≤ T) (ht : t * F ≤ f T)
    (hk : 1 ≤ k) :
    ∑ m ∈ Icc (max S (L + k)) T, (f (m - k) - f m) ≤ k * (F * (1 - t)) := by
  have := sum_Icc_shift_le hanti hF (k := k) (a := max S (L + k)) (T := T) hk
    (le_max_right _ _) (by omega)
  refine this.trans ?_
  have : (0:ℝ) ≤ k := by positivity
  nlinarith

/-- **T1** (second form): `S = L + g`, `1 ≤ ν ≤ g`. -/
theorem T1_nu {f : ℕ → ℝ} {F t : ℝ} {L g T ν : ℕ}
    (hanti : ∀ a b, L ≤ a → a ≤ b → f b ≤ f a)
    (hF : ∀ n, L ≤ n → f n ≤ F) (hST : L + g ≤ T) (ht : t * F ≤ f T)
    (hν : 1 ≤ ν) (hνg : ν ≤ g) :
    ∑ m ∈ Icc (L + g) T, (f (m - ν) - f m) ≤ ν * (F * (1 - t)) := by
  have h := T1_shift hanti hF (S := L + g) (k := ν) (by omega) hST ht hν
  rwa [max_eq_left (by omega)] at h

/-- **T2 (drop term)**: Cauchy-Schwarz in `m`. -/
theorem T2_drop {f : ℕ → ℝ} {F t : ℝ} {L S T k : ℕ}
    (hanti : ∀ a b, L ≤ a → a ≤ b → f b ≤ f a) (hf0 : ∀ n, L ≤ n → 0 ≤ f n)
    (hF : ∀ n, L ≤ n → f n ≤ F) (hFpos : 0 < F) (hLS : L ≤ S) (hST : S ≤ T)
    (ht : t * F ≤ f T) (hk : 1 ≤ k) (hkS : L + k ≤ S) :
    ∑ m ∈ Icc S T, √(f m) * √(f (m - k) - f m) ≤
      √(F * (F⁻¹ * ∑ m ∈ Icc S T, f m)) * √(k * (F * (1 - t))) := by
  have h1 := T1_shift hanti hF hLS hST ht hk
  rw [max_eq_left hkS] at h1
  have hmem : ∀ m ∈ Icc S T, L + k ≤ m := fun m hm => by
    have := (mem_Icc.mp hm).1; omega
  have hcs := Real.sum_sqrt_mul_sqrt_le (Icc S T) (f := fun m => max (f m) 0)
    (g := fun m => max (f (m - k) - f m) 0) (fun m => le_max_right _ _)
    (fun m => le_max_right _ _)
  have e1 : ∑ m ∈ Icc S T, max (f m) 0 = ∑ m ∈ Icc S T, f m :=
    sum_congr rfl fun m hm => max_eq_left (hf0 m (by have := hmem m hm; omega))
  have e2 : ∑ m ∈ Icc S T, max (f (m - k) - f m) 0 = ∑ m ∈ Icc S T, (f (m - k) - f m) :=
    sum_congr rfl fun m hm => max_eq_left (by
      have := hmem m hm
      have := hanti (m - k) m (by omega) (by omega)
      linarith)
  have e3 : ∑ m ∈ Icc S T, √(f m) * √(f (m - k) - f m) =
      ∑ m ∈ Icc S T, √(max (f m) 0) * √(max (f (m - k) - f m) 0) :=
    sum_congr rfl fun m hm => by
      have := hmem m hm
      have h1 := hf0 m (by omega)
      have h2 := hanti (m - k) m (by omega) (by omega)
      rw [max_eq_left h1, max_eq_left (by linarith)]
  rw [e3]
  refine hcs.trans ?_
  rw [e1, e2, mul_inv_cancel_left₀ hFpos.ne']
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h1) (Real.sqrt_nonneg _)

/-- **T3** barrier monotonicity. -/
theorem T3_barrier {τ C c₀ Z X : ℝ} (hτ0 : 0 ≤ τ) (hτ : τ < 1) (hC : 0 ≤ C) (hc : 0 ≤ c₀)
    (hZ : 0 < Z) (h : 0 < (1 - τ) * Z - C * √Z - c₀) (hX : Z ≤ X) :
    0 < (1 - τ) * X - C * √X - c₀ := by
  have hz : 0 < √Z := Real.sqrt_pos.mpr hZ
  have hzs : √Z ≤ √X := Real.sqrt_le_sqrt hX
  have e1 := Real.sq_sqrt hZ.le
  have e2 := Real.sq_sqrt (hZ.le.trans hX)
  have hlt : C < (1 - τ) * √Z := by
    by_contra hcon
    push Not at hcon
    have : (1 - τ) * √Z * √Z ≤ C * √Z := mul_le_mul_of_nonneg_right hcon hz.le
    nlinarith
  have hpos : 0 ≤ (1 - τ) * (√X + √Z) - C := by nlinarith
  have := mul_nonneg (sub_nonneg.mpr hzs) hpos
  nlinarith

/-- **T3** contradiction form. -/
theorem T3_false {τ C c₀ Z X : ℝ} (hτ0 : 0 ≤ τ) (hτ : τ < 1) (hC : 0 ≤ C) (hc : 0 ≤ c₀)
    (hZ : 0 < Z) (h : 0 < (1 - τ) * Z - C * √Z - c₀) (hX : Z ≤ X)
    (hle : (1 - τ) * X ≤ C * √X + c₀) : False := by
  have := T3_barrier hτ0 hτ hC hc hZ h hX
  linarith

end GMCContraction
