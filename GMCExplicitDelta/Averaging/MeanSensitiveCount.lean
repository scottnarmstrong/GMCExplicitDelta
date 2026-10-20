module

public import GMCExplicitDelta.Averaging.MeanSensitiveStirling
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.GCongr
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Counting index tuples with no singleton fibre

`goodCount p n k` is the number of `f : Fin p → Fin n` all of whose nonempty fibres have size at
least `2` and whose image has `k` elements.  We prove `goodCount p n k ≤ 𝒜(p,k) n^k`.
-/

@[expose] public section

namespace GMCExplicitDelta.Averaging

open Finset

/-- Fibre size of `a` under `f`. -/
def cnt {p n : ℕ} (f : Fin p → Fin n) (a : Fin n) : ℕ := ∑ j, if f j = a then 1 else 0

/-- No fibre of `f` is a singleton. -/
def NoSingleton {p n : ℕ} (f : Fin p → Fin n) : Prop := ∀ a, cnt f a ≠ 1

instance {p n : ℕ} (f : Fin p → Fin n) : Decidable (NoSingleton f) :=
  inferInstanceAs (Decidable (∀ a, cnt f a ≠ 1))

/-- The image of `f`, as the set of values with nonempty fibre. -/
def supp {p n : ℕ} (f : Fin p → Fin n) : Finset (Fin n) := univ.filter fun a => 0 < cnt f a

/-- Number of functions `Fin p → Fin n` with no singleton fibre and `k` values. -/
def goodCount (p n k : ℕ) : ℕ :=
  (univ.filter fun f : Fin p → Fin n => NoSingleton f ∧ (supp f).card = k).card

theorem cnt_cons {m n : ℕ} (v : Fin n) (g : Fin m → Fin n) (a : Fin n) :
    cnt (Fin.cons v g : Fin (m + 1) → Fin n) a = cnt g a + if v = a then 1 else 0 := by
  unfold cnt
  rw [Fin.sum_univ_succ]
  simp [Fin.cons_zero, Fin.cons_succ, add_comm]

theorem cnt_succAbove {m n : ℕ} (g : Fin (m + 1) → Fin n) (j : Fin (m + 1)) (a : Fin n) :
    cnt g a = (if g j = a then 1 else 0) + cnt (fun i => g (j.succAbove i)) a := by
  unfold cnt
  rw [Fin.sum_univ_succAbove _ j]

theorem goodCount_zero (n k : ℕ) : goodCount 0 n k = if k = 0 then 1 else 0 := by
  unfold goodCount
  rw [Finset.card_filter]
  rw [Fintype.sum_unique]
  by_cases hk : k = 0
  · subst hk
    simp [NoSingleton, supp, cnt]
  · simp [NoSingleton, supp, cnt, hk, Ne.symm hk]

theorem goodCount_one (n k : ℕ) : goodCount 1 n k = 0 := by
  unfold goodCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro f _ ⟨h, _⟩
  apply h (f 0)
  unfold cnt
  rw [Fin.sum_univ_one]
  simp

theorem goodCount_succ_succ_zero (p n : ℕ) : goodCount (p + 2) n 0 = 0 := by
  unfold goodCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro f _ ⟨_, hk⟩
  rw [Finset.card_eq_zero] at hk
  have : f 0 ∈ supp f := by
    simp only [supp, mem_filter, mem_univ, true_and]
    have : (if f 0 = f 0 then 1 else 0) ≤ cnt f (f 0) :=
      Finset.single_le_sum (f := fun j => if f j = f 0 then 1 else 0)
        (fun _ _ => Nat.zero_le _) (mem_univ 0)
    simp at this
    omega
  rw [hk] at this
  simp at this

/-- Pointwise comparison for the removal of the first coordinate. -/
theorem step_pointwise {p n k : ℕ} (v : Fin n) (g : Fin (p + 1) → Fin n)
    (h : NoSingleton (Fin.cons v g : Fin (p + 2) → Fin n) ∧
      (supp (Fin.cons v g : Fin (p + 2) → Fin n)).card = k + 1) :
    ∃ j : Fin (p + 1), (NoSingleton g ∧ (supp g).card = k + 1 ∧ v ∈ supp g) ∨
      (g j = v ∧ NoSingleton (fun i => g (j.succAbove i)) ∧
        (supp (fun i => g (j.succAbove i))).card = k) := by
  obtain ⟨hns, hk⟩ := h
  have hc : ∀ a, cnt (Fin.cons v g : Fin (p + 2) → Fin n) a = cnt g a + if v = a then 1 else 0 :=
    cnt_cons v g
  by_cases h2 : 2 ≤ cnt g v
  · refine ⟨0, Or.inl ?_⟩
    have hsupp : supp g = supp (Fin.cons v g : Fin (p + 2) → Fin n) := by
      ext a
      simp only [supp, mem_filter, mem_univ, true_and, hc]
      by_cases hav : v = a
      · subst hav; simp; omega
      · simp [hav]
    refine ⟨?_, by rw [hsupp, hk], ?_⟩
    · intro a
      by_cases hav : v = a
      · subst hav; omega
      · have := hns a
        rw [hc] at this
        simpa [hav] using this
    · rw [hsupp]
      simp only [supp, mem_filter, mem_univ, true_and, hc]
      simp
  · have h1 := hns v
    rw [hc] at h1
    simp only [ite_true] at h1
    have hg1 : cnt g v = 1 := by omega
    have hex : ∃ j, g j = v := by
      by_contra hne
      push Not at hne
      simp [cnt, hne] at hg1
    obtain ⟨j, hj⟩ := hex
    have hr : ∀ a, cnt g a = (if v = a then 1 else 0) + cnt (fun i => g (j.succAbove i)) a := by
      intro a; rw [cnt_succAbove g j a, hj]
    refine ⟨j, Or.inr ⟨hj, ?_, ?_⟩⟩
    · intro a
      by_cases hav : v = a
      · subst hav
        have := hr v
        simp at this; omega
      · have := hns a
        rw [hc] at this
        have h3 := hr a
        simp [hav] at this h3
        omega
    · have hmem : v ∈ supp (Fin.cons v g : Fin (p + 2) → Fin n) := by
        simp only [supp, mem_filter, mem_univ, true_and, hc]
        simp
      have : supp (fun i => g (j.succAbove i)) =
          (supp (Fin.cons v g : Fin (p + 2) → Fin n)).erase v := by
        ext a
        simp only [supp, mem_filter, mem_univ, true_and, mem_erase, hc]
        by_cases hav : v = a
        · subst hav
          have := hr v
          simp at this ⊢; omega
        · have h3 := hr a
          simp [hav] at h3 ⊢
          rw [← h3]
          exact ⟨fun h => ⟨fun e => hav e.symm, h⟩, fun h => h.2⟩
      rw [this, card_erase_of_mem hmem, hk]; rfl

theorem goodCount_eq_sum_cons (p n k : ℕ) :
    goodCount (p + 1) n k = ∑ v : Fin n, ∑ g : Fin p → Fin n,
      if NoSingleton (Fin.cons v g : Fin (p + 1) → Fin n) ∧
        (supp (Fin.cons v g : Fin (p + 1) → Fin n)).card = k then 1 else 0 := by
  unfold goodCount
  rw [Finset.card_filter]
  rw [← Fintype.sum_prod_type' (f := fun v g => if NoSingleton
    (Fin.cons v g : Fin (p + 1) → Fin n) ∧
      (supp (Fin.cons v g : Fin (p + 1) → Fin n)).card = k then 1 else 0)]
  exact (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (p + 1) => Fin n)) _ _ (fun _ => rfl)).symm

theorem sum_removeNth {p n : ℕ} (j : Fin (p + 1)) (v : Fin n) (R : (Fin p → Fin n) → Prop)
    [DecidablePred R] :
    (∑ g : Fin (p + 1) → Fin n, if g j = v ∧ R (fun i => g (j.succAbove i)) then 1 else 0) =
      ∑ h : Fin p → Fin n, if R h then 1 else 0 := by
  rw [← Fintype.sum_equiv (Fin.insertNthEquiv (fun _ : Fin (p + 1) => Fin n) j)
    (fun x => if (Fin.insertNthEquiv (fun _ : Fin (p + 1) => Fin n) j x) j = v ∧
      R (fun i => (Fin.insertNthEquiv (fun _ : Fin (p + 1) => Fin n) j x) (j.succAbove i))
      then 1 else 0) _ (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  simp [Fin.insertNthEquiv]
  rw [Finset.sum_eq_single v (fun b _ hb => by simp [hb]) (by simp)]
  simp

theorem sum_mem_supp {p n k : ℕ} (g : Fin p → Fin n) :
    (∑ v : Fin n, if NoSingleton g ∧ (supp g).card = k ∧ v ∈ supp g then 1 else 0) =
      if NoSingleton g ∧ (supp g).card = k then k else 0 := by
  by_cases h : NoSingleton g ∧ (supp g).card = k
  · simp [h]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun v _ => ?_
    rw [if_neg]
    exact fun hh => h ⟨hh.1, hh.2.1⟩

theorem goodCount_step (p n k : ℕ) :
    goodCount (p + 2) n (k + 1) ≤
      (k + 1) * goodCount (p + 1) n (k + 1) + (p + 1) * n * goodCount p n k := by
  rw [goodCount_eq_sum_cons (p + 1)]
  calc _ ≤ ∑ v : Fin n, ∑ g : Fin (p + 1) → Fin n,
        ((if NoSingleton g ∧ (supp g).card = k + 1 ∧ v ∈ supp g then 1 else 0) +
        ∑ j : Fin (p + 1), if g j = v ∧ NoSingleton (fun i => g (j.succAbove i)) ∧
          (supp (fun i => g (j.succAbove i))).card = k then 1 else 0) := by
        refine Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun g _ => ?_
        by_cases hP : NoSingleton (Fin.cons v g : Fin (p + 2) → Fin n) ∧
            (supp (Fin.cons v g : Fin (p + 2) → Fin n)).card = k + 1
        · rw [if_pos hP]
          obtain ⟨j, hj | hj⟩ := step_pointwise v g hP
          · rw [if_pos hj]; exact Nat.le_add_right _ _
          · refine le_trans ?_ (Nat.le_add_left _ _)
            refine le_trans ?_ (Finset.single_le_sum (f := fun j => if g j = v ∧
              NoSingleton (fun i => g (j.succAbove i)) ∧
              (supp (fun i => g (j.succAbove i))).card = k then 1 else 0)
              (fun _ _ => Nat.zero_le _) (mem_univ j))
            rw [if_pos hj]
        · rw [if_neg hP]; exact Nat.zero_le _
    _ = (∑ g : Fin (p + 1) → Fin n, ∑ v : Fin n,
          if NoSingleton g ∧ (supp g).card = k + 1 ∧ v ∈ supp g then 1 else 0) +
        ∑ v : Fin n, ∑ j : Fin (p + 1), ∑ g : Fin (p + 1) → Fin n,
          if g j = v ∧ NoSingleton (fun i => g (j.succAbove i)) ∧
          (supp (fun i => g (j.succAbove i))).card = k then 1 else 0 := by
        simp only [Finset.sum_add_distrib]
        rw [Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun v _ => Finset.sum_comm
    _ = _ := by
        congr 1
        · simp only [sum_mem_supp]
          unfold goodCount
          rw [Finset.card_filter, Finset.mul_sum]
          refine Finset.sum_congr rfl fun g _ => ?_
          by_cases h : NoSingleton g ∧ (supp g).card = k + 1 <;> simp [h]
        · have key : ∀ (j : Fin (p + 1)) (v : Fin n),
              (∑ g : Fin (p + 1) → Fin n, if g j = v ∧ NoSingleton (fun i => g (j.succAbove i)) ∧
                (supp (fun i => g (j.succAbove i))).card = k then 1 else 0) = goodCount p n k := by
            intro j v
            exact (sum_removeNth j v (fun h => NoSingleton h ∧ (supp h).card = k)).trans
              (Finset.card_filter _ _).symm
          simp only [key, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
          ring

theorem goodCount_le (p n k : ℕ) : goodCount p n k ≤ assocStirling p k * n ^ k := by
  induction p using Nat.strong_induction_on generalizing k with
  | _ p ih =>
    match p, k with
    | 0, k =>
      rw [goodCount_zero]
      by_cases hk : k = 0
      · subst hk; simp [assocStirling]
      · simp [hk, assocStirling]
    | 1, k => simp [goodCount_one]
    | p + 2, 0 => simp [goodCount_succ_succ_zero]
    | p + 2, k + 1 =>
      refine (goodCount_step p n k).trans ?_
      have h1 := ih (p + 1) (by omega) (k + 1)
      have h2 := ih p (by omega) k
      rw [assocStirling_succ_succ]
      calc _ ≤ (k + 1) * (assocStirling (p + 1) (k + 1) * n ^ (k + 1)) +
          (p + 1) * n * (assocStirling p k * n ^ k) := by gcongr
        _ = _ := by ring

end GMCExplicitDelta.Averaging
