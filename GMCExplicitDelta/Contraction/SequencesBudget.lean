module

public import GMCExplicitDelta.Contraction.Sequences

/-!
# Abstract recurrence budgets (step V4)

If `V n ≤ ρ V(n-ℓ) + c (f(n-ℓ)² - f n²)` for `n ≥ L+1+ℓ` with `f` nonincreasing, then the
windowed sums of `V` are bounded by a geometric initial part plus a telescoped forcing part.
-/

@[expose] public section

namespace GMCContraction

open Finset

/-- Hypotheses of V4. -/
structure VarBudget (f V : ℕ → ℝ) (L ℓ : ℕ) (ρ c F vi : ℝ) : Prop where
  one_le : 1 ≤ ℓ
  rho_nonneg : 0 ≤ ρ
  rho_lt : ρ < 1
  c_nonneg : 0 ≤ c
  anti : ∀ a b, L ≤ a → a ≤ b → f b ≤ f a
  f_nonneg : ∀ n, L ≤ n → 0 ≤ f n
  f_le : ∀ n, L ≤ n → f n ≤ F
  V_nonneg : ∀ n, L ≤ n → 0 ≤ V n
  V_le : ∀ n, L ≤ n → V n ≤ F * vi
  recur : ∀ n, L + 1 + ℓ ≤ n → V n ≤ ρ * V (n - ℓ) + c * (f (n - ℓ) ^ 2 - f n ^ 2)

namespace VarBudget

variable {f V : ℕ → ℝ} {L ℓ : ℕ} {ρ c F vi : ℝ}

theorem F_nonneg (H : VarBudget f V L ℓ ρ c F vi) : 0 ≤ F :=
  (H.f_nonneg L le_rfl).trans (H.f_le L le_rfl)

theorem Fvi_nonneg (H : VarBudget f V L ℓ ρ c F vi) : 0 ≤ F * vi :=
  (H.V_nonneg L le_rfl).trans (H.V_le L le_rfl)

theorem rec' (H : VarBudget f V L ℓ ρ c F vi) {a x : ℕ} (ha : L + 1 ≤ a) :
    V (a + ℓ + x) ≤ ρ * V (a + x) + c * (f (a + x) ^ 2 - f (a + x + ℓ) ^ 2) := by
  have := H.recur (a + ℓ + x) (by omega)
  have e1 : a + ℓ + x - ℓ = a + x := by omega
  have e2 : a + ℓ + x = a + x + ℓ := by omega
  rw [e1] at this
  rw [e2] at this ⊢
  exact this

/-- Telescoped forcing sum. -/
theorem forcing (H : VarBudget f V L ℓ ρ c F vi) {a N T' : ℕ} (ha : L ≤ a)
    (hT : a + N + ℓ ≤ T' + 1) :
    ∑ x ∈ range N, (f (a + x) ^ 2 - f (a + x + ℓ) ^ 2) ≤ ℓ * (F ^ 2 - f T' ^ 2) := by
  have := sum_range_shift_le (g := fun n => f n ^ 2) (G := F ^ 2) (L' := L)
    (fun a b h1 h2 => by
      have := H.anti a b h1 h2
      have := H.f_nonneg b (by omega)
      nlinarith)
    (fun m hm => by
      have := H.f_le m hm
      have := H.f_nonneg m hm
      nlinarith) (p := a) (k := ℓ) (n := N) (T := T') ha hT
  exact this

/-- Core block bound by induction on the number of unrolling steps. -/
theorem block (H : VarBudget f V L ℓ ρ c F vi) {T' : ℕ} (hT' : L ≤ T') :
    ∀ (i a N : ℕ), L + 1 + i * ℓ ≤ a → a + N ≤ T' + 1 →
      ∑ x ∈ range N, V (a + x) ≤
        ρ ^ i * (ℓ * (F * vi) / (1 - ρ)) + c * ℓ * (F ^ 2 - f T' ^ 2) / (1 - ρ) := by
  have h1 : 0 < 1 - ρ := by linarith [H.rho_lt]
  have hD : 0 ≤ F ^ 2 - f T' ^ 2 := by
    have := H.f_le T' hT'
    have := H.f_nonneg T' hT'
    nlinarith
  have hl : (0 : ℝ) ≤ ℓ := by positivity
  have hX0 : 0 ≤ (ℓ : ℝ) * (F * vi) / (1 - ρ) := by
    have := H.Fvi_nonneg; positivity
  have hY0 : 0 ≤ c * ℓ * (F ^ 2 - f T' ^ 2) / (1 - ρ) := by
    have := H.c_nonneg; positivity
  set X := (ℓ : ℝ) * (F * vi) / (1 - ρ) with hXdef
  set Y := c * ℓ * (F ^ 2 - f T' ^ 2) / (1 - ρ) with hYdef
  have hXe : X * (1 - ρ) = ℓ * (F * vi) := by rw [hXdef]; field_simp
  have hYe : Y * (1 - ρ) = c * ℓ * (F ^ 2 - f T' ^ 2) := by rw [hYdef]; field_simp
  have hρ0 := H.rho_nonneg
  have hXge : ℓ * (F * vi) ≤ X := by nlinarith
  intro i
  induction i with
  | zero =>
    intro a N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro ha hN
      simp only [zero_mul, add_zero, pow_zero, one_mul] at ha ⊢
      by_cases hNl : N ≤ ℓ
      · calc ∑ x ∈ range N, V (a + x) ≤ ∑ _x ∈ range N, F * vi :=
              sum_le_sum fun x _ => H.V_le _ (by omega)
          _ = N * (F * vi) := by simp
          _ ≤ ℓ * (F * vi) := mul_le_mul_of_nonneg_right (by exact_mod_cast hNl) H.Fvi_nonneg
          _ ≤ X + Y := by linarith
      · obtain ⟨N', rfl⟩ : ∃ N', N = ℓ + N' := ⟨N - ℓ, by omega⟩
        have hlt : N' < ℓ + N' := by have := H.one_le; omega
        have ih' := ih N' hlt (by omega) (by omega)
        have eA : ∑ x ∈ range N', V (a + (ℓ + x)) = ∑ x ∈ range N', V (a + ℓ + x) :=
          sum_congr rfl fun x _ => by rw [add_assoc]
        rw [sum_range_add, eA]
        simp only [pow_zero, one_mul] at ih'
        have hfirst : ∑ x ∈ range ℓ, V (a + x) ≤ ℓ * (F * vi) := by
          calc ∑ x ∈ range ℓ, V (a + x) ≤ ∑ _x ∈ range ℓ, F * vi :=
                sum_le_sum fun x _ => H.V_le _ (by omega)
            _ = ℓ * (F * vi) := by simp
        have hsec : ∑ x ∈ range N', V (a + ℓ + x) ≤
            ρ * ∑ x ∈ range N', V (a + x) +
              c * ∑ x ∈ range N', (f (a + x) ^ 2 - f (a + x + ℓ) ^ 2) := by
          rw [mul_sum, mul_sum, ← sum_add_distrib]
          exact sum_le_sum fun x _ => H.rec' (by omega)
        have hf := H.forcing (a := a) (N := N') (T' := T') (by omega) (by omega)
        have := H.c_nonneg
        have hc2 := mul_le_mul_of_nonneg_left hf this
        have hr := mul_le_mul_of_nonneg_left ih' hρ0
        nlinarith
  | succ i ih =>
    intro a N ha hN
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + ℓ := ⟨a - ℓ, by
      have := H.one_le
      have e : (i + 1) * ℓ = i * ℓ + ℓ := by ring
      omega⟩
    have ha' : L + 1 + i * ℓ ≤ a' := by
      have e : (i + 1) * ℓ = i * ℓ + ℓ := by ring
      omega
    have ih' := ih a' N ha' (by omega)
    have hsec : ∑ x ∈ range N, V (a' + ℓ + x) ≤
        ρ * ∑ x ∈ range N, V (a' + x) +
          c * ∑ x ∈ range N, (f (a' + x) ^ 2 - f (a' + x + ℓ) ^ 2) := by
      rw [mul_sum, mul_sum, ← sum_add_distrib]
      exact sum_le_sum fun x _ => H.rec' (by omega)
    have hf := H.forcing (a := a') (N := N) (T' := T') (by omega) (by omega)
    have hc2 := mul_le_mul_of_nonneg_left hf H.c_nonneg
    have hr := mul_le_mul_of_nonneg_left ih' hρ0
    have e : ρ ^ (i + 1) = ρ * ρ ^ i := by ring
    rw [e]
    nlinarith

/-- **V4, tail form**: `∑_{n=L+j}^{T'} V n`. -/
theorem sum_tail_le (H : VarBudget f V L ℓ ρ c F vi) {T' j : ℕ} (hT' : L ≤ T') (hj : 1 ≤ j) :
    ∑ n ∈ Icc (L + j) T', V n ≤
      F * (ℓ * vi * ρ ^ ((j - 1) / ℓ) / (1 - ρ)) +
        ℓ * c * (F ^ 2 - f T' ^ 2) / (1 - ρ) := by
  have h1 : 0 < 1 - ρ := by linarith [H.rho_lt]
  have key : ∑ n ∈ Icc (L + j) T', V n ≤
      ρ ^ ((j - 1) / ℓ) * (ℓ * (F * vi) / (1 - ρ)) +
        c * ℓ * (F ^ 2 - f T' ^ 2) / (1 - ρ) := by
    rcases lt_or_ge T' (L + j) with h | h
    · rw [Icc_eq_empty_of_lt h, sum_empty]
      have hD : 0 ≤ F ^ 2 - f T' ^ 2 := by
        have := H.f_le T' hT'
        have := H.f_nonneg T' hT'
        nlinarith
      have := H.Fvi_nonneg
      have := H.c_nonneg
      have := H.rho_nonneg
      positivity
    · have hI : Icc (L + j) T' = Ico (L + j) (T' + 1) := by ext; simp
      rw [hI, sum_Ico_eq_sum_range]
      refine H.block hT' ((j - 1) / ℓ) (L + j) (T' + 1 - (L + j)) ?_ (by omega)
      have := Nat.div_mul_le_self (j - 1) ℓ
      omega
  refine key.trans (le_of_eq ?_)
  field_simp

/-- **V4, full form**: `∑_{n=L}^{T'} V n`. -/
theorem sum_full_le (H : VarBudget f V L ℓ ρ c F vi) {T' : ℕ} (hT' : L ≤ T') :
    ∑ n ∈ Icc L T', V n ≤
      F * (vi * (1 + ℓ / (1 - ρ))) + ℓ * c * (F ^ 2 - f T' ^ 2) / (1 - ρ) := by
  have h1 : 0 < 1 - ρ := by linarith [H.rho_lt]
  have hI : Icc L T' = Ico L (T' + 1) := by ext; simp
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hT'
  rw [hI, sum_Ico_eq_sum_range, show L + d + 1 - L = d + 1 by omega, sum_range_succ']
  have hb := H.block (T' := L + d) hT' 0 (L + 1) d (by simp) (by omega)
  simp only [pow_zero, one_mul] at hb
  have e : ∑ x ∈ range d, V (L + (x + 1)) = ∑ x ∈ range d, V (L + 1 + x) :=
    sum_congr rfl fun x _ => by congr 1; omega
  rw [e]
  have h0 := H.V_le L le_rfl
  have : V (L + 0) ≤ F * vi := by simpa using h0
  have e2 : F * (vi * (1 + ℓ / (1 - ρ))) = F * vi + ℓ * (F * vi) / (1 - ρ) := by
    field_simp
  rw [e2]
  have e3 : (ℓ : ℝ) * c * (F ^ 2 - f (L + d) ^ 2) / (1 - ρ) =
      c * ℓ * (F ^ 2 - f (L + d) ^ 2) / (1 - ρ) := by ring
  rw [e3]
  linarith

/-- form of V4 (tail), for `F > 0`. -/
theorem sum_tail_le' (H : VarBudget f V L ℓ ρ c F vi) {T' j : ℕ} (hT' : L ≤ T') (hj : 1 ≤ j)
    (hF : 0 < F) :
    ∑ n ∈ Icc (L + j) T', V n ≤
      F * (ℓ * vi * ρ ^ ((j - 1) / ℓ) / (1 - ρ) +
        ℓ * c * (F ^ 2 - f T' ^ 2) / (F * (1 - ρ))) := by
  have h1 : 0 < 1 - ρ := by linarith [H.rho_lt]
  refine (H.sum_tail_le hT' hj).trans (le_of_eq ?_)
  field_simp

/-- form of V4 (full), for `F > 0`. -/
theorem sum_full_le' (H : VarBudget f V L ℓ ρ c F vi) {T' : ℕ} (hT' : L ≤ T') (hF : 0 < F) :
    ∑ n ∈ Icc L T', V n ≤
      F * (vi * (1 + ℓ / (1 - ρ)) + ℓ * c * (F ^ 2 - f T' ^ 2) / (F * (1 - ρ))) := by
  have h1 : 0 < 1 - ρ := by linarith [H.rho_lt]
  refine (H.sum_full_le hT').trans (le_of_eq ?_)
  field_simp

end VarBudget

/-- Corollary: if `f T' ≥ t F` (`t, F ≥ 0`) then the forcing factor is at most `F²(1-t²)`. -/
theorem sq_defect_le {f F t : ℝ} (ht0 : 0 ≤ t) (hF : 0 ≤ F) (ht : t * F ≤ f) :
    F ^ 2 - f ^ 2 ≤ F ^ 2 * (1 - t ^ 2) := by
  have h : (t * F) ^ 2 ≤ f ^ 2 := pow_le_pow_left₀ (mul_nonneg ht0 hF) ht 2
  nlinarith

end GMCContraction
