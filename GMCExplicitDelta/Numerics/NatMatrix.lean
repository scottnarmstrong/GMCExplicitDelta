module

public import GMCExplicitDelta.Numerics.CeilDiv
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.List.Range

/-!
# Fixed-point nonnegative matrices over `ℕ`

A matrix is a `List (List ℕ)`; the entry `x` stands for the real number `x / S`.
Products are computed exactly in `ℕ` and rounded up once per entry (`ceilDiv · S`), so every
computed matrix dominates the real one.  All computational definitions are structurally
recursive so that `decide +kernel` can evaluate them.
-/

@[expose] public section

namespace GMCNumerics

open Matrix

/-! ### Computational definitions -/

/-- Exact dot product of two lists (truncating to the shorter). -/
def dot : List ℕ → List ℕ → ℕ
  | a :: as, b :: bs => a * b + dot as bs
  | _, _ => 0

/-- Entry accessor, missing entries are `0`. -/
def getE (A : List (List ℕ)) (i j : ℕ) : ℕ := (A.getD i []).getD j 0

/-- The columns `0..n-1` of `B` as lists. -/
def cols (n : ℕ) (B : List (List ℕ)) : List (List ℕ) :=
  (List.range n).map fun j => B.map fun r => r.getD j 0

/-- Fixed-point product rounding up: exact integer sums, one `ceilDiv` by `S` per entry. -/
def mulUp (S n : ℕ) (A B : List (List ℕ)) : List (List ℕ) :=
  let Bt := cols n B
  A.map fun r => Bt.map fun c => ceilDiv (dot r c) S

/-- Fixed-point identity. -/
def identUp (S n : ℕ) : List (List ℕ) :=
  (List.range n).map fun i => (List.range n).map fun j => if i = j then S else 0

/-- Binary powering with fuel; computes `p * w ^ m` style products (see `mpowUp_sound`). -/
def mpowUp (S n : ℕ) : ℕ → ℕ → List (List ℕ) → List (List ℕ) → List (List ℕ)
  | 0, _, p, _ => p
  | fuel + 1, m, p, w =>
    if m = 0 then p else
    let p' := if m % 2 = 1 then mulUp S n p w else p
    let m' := m / 2
    if m' = 0 then p' else mpowUp S n fuel m' p' (mulUp S n w w)

/-- `B ^ k` rounded up; correct when `k < 2 ^ fuel`. -/
def powUp (S n fuel : ℕ) (B : List (List ℕ)) (k : ℕ) : List (List ℕ) :=
  mpowUp S n fuel k (identUp S n) B

/-- Matrix-vector product rounding up. -/
def mulVecUp (S : ℕ) (A : List (List ℕ)) (v : List ℕ) : List ℕ :=
  A.map fun r => ceilDiv (dot r v) S

/-- Well-formedness: `n × n`. -/
def wfM (n : ℕ) (A : List (List ℕ)) : Bool :=
  A.length == n && A.all fun r => r.length == n

/-- Final check: entry `i` of `B^k v` (rounded up) is at most `c` (in units of `1/S`). -/
def checkVec (S n fuel : ℕ) (B : List (List ℕ)) (k : ℕ) (v : List ℕ) (i c : ℕ) : Bool :=
  wfM n B && v.length == n && Nat.ble (powUp S n fuel B k |> fun P => mulVecUp S P v |>.getD i 0) c

/-! ### Real semantics -/

/-- Real matrix of a fixed-point list matrix. -/
noncomputable def toReal (S n : ℕ) (A : List (List ℕ)) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (getE A i j : ℝ) / S

/-- Real vector of a fixed-point list. -/
noncomputable def toRealV (S n : ℕ) (v : List ℕ) : Fin n → ℝ :=
  fun i => (v.getD i 0 : ℝ) / S

/-- Entrywise domination of a nonnegative real matrix by a fixed-point matrix. -/
def Dom (S n : ℕ) (X : Matrix (Fin n) (Fin n) ℝ) (A : List (List ℕ)) : Prop :=
  (∀ i j, 0 ≤ X i j) ∧ ∀ i j, X i j ≤ toReal S n A i j

/-- Same for vectors. -/
def DomV (S n : ℕ) (x : Fin n → ℝ) (v : List ℕ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ ∀ i, x i ≤ toRealV S n v i

/-! ### Lemmas -/

theorem dot_eq_sum (r c : List ℕ) :
    dot r c = ∑ k ∈ Finset.range (min r.length c.length), r.getD k 0 * c.getD k 0 := by
  induction r generalizing c with
  | nil => simp [dot]
  | cons a as ih =>
    cases c with
    | nil => simp [dot]
    | cons b bs =>
      simp only [dot, ih, List.length_cons, Nat.add_min_add_right]
      rw [Finset.sum_range_succ' _ (min as.length bs.length)]
      simp [add_comm]

theorem dot_eq_sum_of_len {n : ℕ} {r c : List ℕ} (hr : r.length = n) (hc : c.length = n) :
    dot r c = ∑ k ∈ Finset.range n, r.getD k 0 * c.getD k 0 := by
  rw [dot_eq_sum, hr, hc, min_self]

/-- Well-formed. -/
def WF (n : ℕ) (A : List (List ℕ)) : Prop := A.length = n ∧ ∀ r ∈ A, r.length = n

theorem wfM_iff {n : ℕ} {A : List (List ℕ)} : wfM n A = true ↔ WF n A := by
  simp [wfM, WF]

theorem getE_eq_getD {A : List (List ℕ)} {i : ℕ} (hi : i < A.length) (j : ℕ) :
    getE A i j = (A[i]'hi).getD j 0 := by
  simp [getE, List.getD_eq_getElem?_getD, hi]

theorem WF_cols {n : ℕ} {B : List (List ℕ)} (hB : WF n B) : WF n (cols n B) := by
  refine ⟨by simp [cols], ?_⟩
  intro r hr
  simp only [cols, List.mem_map] at hr
  obtain ⟨j, -, rfl⟩ := hr
  simp [hB.1]

theorem getD_cols {n : ℕ} {B : List (List ℕ)} {j : ℕ} (hj : j < n) (k : ℕ) :
    ((cols n B).getD j []).getD k 0 = getE B k j := by
  have : (cols n B).getD j [] = B.map fun r => r.getD j 0 := by
    simp [cols, hj, List.getD_eq_getElem?_getD]
  rw [this]
  by_cases hk : k < B.length
  · simp [getE, List.getD_eq_getElem?_getD, hk]
  · simp [getE, List.getD_eq_getElem?_getD, hk]

theorem getE_mulUp {S n : ℕ} {A B : List (List ℕ)} (hA : WF n A) (hB : WF n B)
    {i j : ℕ} (hi : i < n) (hj : j < n) :
    getE (mulUp S n A B) i j = ceilDiv (∑ k ∈ Finset.range n, getE A i k * getE B k j) S := by
  have hiA : i < A.length := by rw [hA.1]; exact hi
  have hcl : (cols n B).length = n := (WF_cols hB).1
  have hjc : j < (cols n B).length := by rw [hcl]; exact hj
  have hrow : (A[i]'hiA).length = n := hA.2 _ (List.getElem_mem hiA)
  have hcol : ((cols n B)[j]'hjc).length = n := (WF_cols hB).2 _ (List.getElem_mem hjc)
  have e1 : getE (mulUp S n A B) i j = ceilDiv (dot (A[i]'hiA) ((cols n B)[j]'hjc)) S := by
    simp [getE, mulUp, List.getD_eq_getElem?_getD, hiA, hjc]
  rw [e1, dot_eq_sum_of_len hrow hcol]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  have e2 : ((cols n B)[j]'hjc).getD k 0 = getE B k j := by
    rw [← getD_cols hj k]; simp [List.getD_eq_getElem?_getD, hjc]
  rw [e2, getE_eq_getD hiA]

theorem WF_mulUp {S n : ℕ} {A B : List (List ℕ)} (hA : WF n A) : WF n (mulUp S n A B) := by
  refine ⟨by simp [mulUp, hA.1], ?_⟩
  intro r hr
  simp only [mulUp, List.mem_map] at hr
  obtain ⟨a, -, rfl⟩ := hr
  simp [cols]

theorem WF_identUp (S n : ℕ) : WF n (identUp S n) := by
  refine ⟨by simp [identUp], ?_⟩
  intro r hr
  simp only [identUp, List.mem_map] at hr
  obtain ⟨a, -, rfl⟩ := hr
  simp

theorem getE_identUp {S n i j : ℕ} (hi : i < n) (hj : j < n) :
    getE (identUp S n) i j = if i = j then S else 0 := by
  simp [getE, identUp, List.getD_eq_getElem?_getD, hi, hj]

theorem Dom_mul {S n : ℕ} (hS : 0 < S) {X Y : Matrix (Fin n) (Fin n) ℝ} {A B : List (List ℕ)}
    (hA : WF n A) (hB : WF n B) (hX : Dom S n X A) (hY : Dom S n Y B) :
    Dom S n (X * Y) (mulUp S n A B) := by
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · simp only [Matrix.mul_apply]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hX.1 i k) (hY.1 k j)
  · simp only [Matrix.mul_apply, toReal]
    rw [getE_mulUp hA hB i.2 j.2]
    have h1 : ∑ k : Fin n, X i k * Y k j ≤
        ∑ k : Fin n, ((getE A i k : ℝ) / S) * ((getE B k j : ℝ) / S) :=
      Finset.sum_le_sum fun k _ => mul_le_mul (hX.2 i k) (hY.2 k j) (hY.1 k j)
        (le_trans (hX.1 i k) (hX.2 i k))
    refine h1.trans ?_
    have h2 : ∑ k : Fin n, ((getE A i k : ℝ) / S) * ((getE B k j : ℝ) / S)
        = ((∑ k ∈ Finset.range n, getE A i k * getE B k j : ℕ) : ℝ) / S / S := by
      rw [← Fin.sum_univ_eq_sum_range (fun k => getE A i k * getE B k j) n]
      push_cast
      rw [Finset.sum_div, Finset.sum_div]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [div_mul_div_comm, div_div]
    rw [h2]
    exact div_le_div_of_nonneg_right (div_le_ceilDiv hS) hS'.le

theorem Dom_one {S n : ℕ} (hS : 0 < S) : Dom S n (1 : Matrix (Fin n) (Fin n) ℝ) (identUp S n) := by
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · by_cases h : i = j <;> simp [Matrix.one_apply, h]
  · simp only [toReal, getE_identUp i.2 j.2, Fin.val_inj, Matrix.one_apply]
    by_cases h : i = j <;> simp [h, hS'.ne']

theorem Dom_mpowUp {S n : ℕ} (hS : 0 < S) {X : Matrix (Fin n) (Fin n) ℝ} (_hX0 : ∀ i j, 0 ≤ X i j) :
    ∀ (fuel m a b : ℕ) (p w : List (List ℕ)), WF n p → WF n w → m < 2 ^ fuel →
      Dom S n (X ^ a) p → Dom S n (X ^ b) w →
      Dom S n (X ^ (a + b * m)) (mpowUp S n fuel m p w) := by
  intro fuel
  induction fuel with
  | zero =>
    intro m a b p w _ _ hm hp _
    have : m = 0 := by simpa using hm
    subst this
    simpa [mpowUp] using hp
  | succ fuel ih =>
    intro m a b p w hpW hwW hm hp hw
    by_cases h0 : m = 0
    · subst h0; simpa [mpowUp] using hp
    · simp only [mpowUp, h0, ite_false]
      have hwf' : WF n (if m % 2 = 1 then mulUp S n p w else p) := by
        split_ifs
        · exact WF_mulUp hpW
        · exact hpW
      have hp' : Dom S n (X ^ (a + b * (m % 2))) (if m % 2 = 1 then mulUp S n p w else p) := by
        split_ifs with h
        · rw [h, mul_one, pow_add]; exact Dom_mul hS hpW hwW hp hw
        · have : m % 2 = 0 := by omega
          rw [this]; simpa using hp
      have hmm : m = m % 2 + 2 * (m / 2) := by omega
      by_cases h1 : m / 2 = 0
      · simp only [h1, ite_true]
        have e0 : m % 2 = m := by omega
        have e : a + b * m = a + b * (m % 2) := by rw [e0]
        rw [e]; exact hp'
      · simp only [h1, ite_false]
        have hlt : m / 2 < 2 ^ fuel := by
          rw [pow_succ] at hm; omega
        have hw2 : Dom S n (X ^ (2 * b)) (mulUp S n w w) := by
          rw [two_mul, pow_add]; exact Dom_mul hS hwW hwW hw hw
        have := ih (m / 2) (a + b * (m % 2)) (2 * b) _ _ hwf' (WF_mulUp hwW) hlt hp' hw2
        have e : a + b * m = a + b * (m % 2) + 2 * b * (m / 2) := by
          calc a + b * m = a + b * (m % 2 + 2 * (m / 2)) := by rw [← hmm]
            _ = _ := by ring
        rw [e]; exact this

theorem WF_mpowUp {S n : ℕ} :
    ∀ (fuel m : ℕ) (p w : List (List ℕ)), WF n p → WF n (mpowUp S n fuel m p w) := by
  intro fuel
  induction fuel with
  | zero => intro m p w hp; simpa [mpowUp] using hp
  | succ fuel ih =>
    intro m p w hp
    by_cases h0 : m = 0
    · subst h0; simpa [mpowUp] using hp
    · simp only [mpowUp, h0, ite_false]
      have hwf' : WF n (if m % 2 = 1 then mulUp S n p w else p) := by
        split_ifs
        · exact WF_mulUp hp
        · exact hp
      by_cases h1 : m / 2 = 0
      · simp only [h1, ite_true]; exact hwf'
      · simp only [h1, ite_false]; exact ih _ _ _ hwf'

/-- Soundness of `powUp`. -/
theorem Dom_powUp {S n fuel k : ℕ} (hS : 0 < S) {B : List (List ℕ)} (hB : WF n B)
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : Dom S n X B) (hk : k < 2 ^ fuel) :
    Dom S n (X ^ k) (powUp S n fuel B k) := by
  have := Dom_mpowUp hS hX.1 fuel k 0 1 (identUp S n) B (WF_identUp S n) hB hk
    (by simpa using Dom_one hS) (by simpa using hX)
  simpa [powUp] using this

theorem getD_mulVecUp {S : ℕ} {A : List (List ℕ)} (v : List ℕ) {i : ℕ} (hi : i < A.length) :
    (mulVecUp S A v).getD i 0 = ceilDiv (dot (A[i]'hi) v) S := by
  simp [mulVecUp, List.getD_eq_getElem?_getD, hi]

theorem DomV_mulVec {S n : ℕ} (hS : 0 < S) {X : Matrix (Fin n) (Fin n) ℝ} {x : Fin n → ℝ}
    {A : List (List ℕ)} {v : List ℕ} (hA : WF n A) (hv : v.length = n)
    (hX : Dom S n X A) (hx : DomV S n x v) (i : Fin n) :
    (X *ᵥ x) i ≤ ((ceilDiv (dot (A[i.1]'(hA.1 ▸ i.2)) v) S : ℕ) : ℝ) / S := by
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  have hiA : i.1 < A.length := by rw [hA.1]; exact i.2
  have hrow : (A[i.1]'hiA).length = n := hA.2 _ (List.getElem_mem hiA)
  simp only [Matrix.mulVec, dotProduct]
  have h1 : ∑ k : Fin n, X i k * x k ≤
      ∑ k : Fin n, ((getE A i k : ℝ) / S) * ((v.getD k 0 : ℝ) / S) :=
    Finset.sum_le_sum fun k _ => mul_le_mul (hX.2 i k) (hx.2 k) (hx.1 k)
      (le_trans (hX.1 i k) (hX.2 i k))
  refine h1.trans ?_
  have h2 : ∑ k : Fin n, ((getE A i k : ℝ) / S) * ((v.getD k 0 : ℝ) / S)
      = ((dot (A[i.1]'hiA) v : ℕ) : ℝ) / S / S := by
    rw [dot_eq_sum_of_len hrow hv,
      ← Fin.sum_univ_eq_sum_range (fun k => (A[i.1]'hiA).getD k 0 * v.getD k 0) n]
    push_cast
    rw [Finset.sum_div, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [getE_eq_getD hiA]
    rw [div_mul_div_comm, div_div]
  rw [h2]
  exact div_le_div_of_nonneg_right (div_le_ceilDiv hS) hS'.le

/-- Main soundness: a successful `checkVec` yields a real bound `(X ^ k *ᵥ x) i ≤ c / S`. -/
theorem checkVec_sound {S n fuel k : ℕ} {B : List (List ℕ)} {v : List ℕ} {i c : ℕ}
    (hS : 0 < S) (hk : k < 2 ^ fuel) (hi : i < n)
    (hchk : checkVec S n fuel B k v i c = true)
    {X : Matrix (Fin n) (Fin n) ℝ} {x : Fin n → ℝ}
    (hX : Dom S n X B) (hx : DomV S n x v) :
    ((X ^ k) *ᵥ x) ⟨i, hi⟩ ≤ (c : ℝ) / S := by
  simp only [checkVec, Bool.and_eq_true, beq_iff_eq] at hchk
  obtain ⟨⟨hB, hv⟩, hle⟩ := hchk
  have hB' : WF n B := wfM_iff.mp hB
  have hP := Dom_powUp hS hB' hX hk
  have hWF : WF n (powUp S n fuel B k) := by
    exact WF_mpowUp _ _ _ _ (WF_identUp S n)
  have hiP : i < (powUp S n fuel B k).length := by rw [hWF.1]; exact hi
  have := DomV_mulVec hS hWF hv hP hx ⟨i, hi⟩
  refine this.trans ?_
  rw [getD_mulVecUp _ hiP] at hle
  have hle' := Nat.le_of_ble_eq_true hle
  exact div_le_div_of_nonneg_right (by exact_mod_cast hle') (by exact_mod_cast hS.le)

/-! ### Entrywise comparison of two list matrices -/

/-- Entrywise `≤` of two lists. -/
def leL : List ℕ → List ℕ → Bool
  | a :: as, b :: bs => Nat.ble a b && leL as bs
  | [], [] => true
  | _, _ => false

/-- Entrywise `≤` of two list matrices. -/
def leM : List (List ℕ) → List (List ℕ) → Bool
  | a :: as, b :: bs => leL a b && leM as bs
  | [], [] => true
  | _, _ => false

theorem leL_getD : ∀ (r s : List ℕ), leL r s = true → ∀ j, r.getD j 0 ≤ s.getD j 0
  | [], [], _, j => by simp
  | a :: as, b :: bs, h, j => by
    simp only [leL, Bool.and_eq_true] at h
    cases j with
    | zero => simpa using Nat.le_of_ble_eq_true h.1
    | succ j => simpa using leL_getD as bs h.2 j
  | [], _ :: _, h, _ => by simp [leL] at h
  | _ :: _, [], h, _ => by simp [leL] at h

theorem leM_getE : ∀ (A R : List (List ℕ)), leM A R = true → ∀ i j, getE A i j ≤ getE R i j
  | [], [], _, i, j => by simp [getE]
  | a :: as, b :: bs, h, i, j => by
    simp only [leM, Bool.and_eq_true] at h
    cases i with
    | zero => simpa [getE] using leL_getD a b h.1 j
    | succ i => simpa [getE] using leM_getE as bs h.2 i j
  | [], _ :: _, h, _, _ => by simp [leM] at h
  | _ :: _, [], h, _, _ => by simp [leM] at h

/-- Matrix form: a successful `leM (powUp ..) R` bounds every entry of `X ^ k`. -/
theorem powUp_le_sound {S n fuel k : ℕ} {B R : List (List ℕ)} (hS : 0 < S) (hk : k < 2 ^ fuel)
    (hB : wfM n B = true) (hle : leM (powUp S n fuel B k) R = true)
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : Dom S n X B) :
    ∀ i j, (X ^ k) i j ≤ toReal S n R i j := by
  intro i j
  have hP := Dom_powUp hS (wfM_iff.mp hB) hX hk
  refine (hP.2 i j).trans ?_
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  simp only [toReal]
  exact div_le_div_of_nonneg_right (by exact_mod_cast leM_getE _ _ hle i j) hS'.le

/-- Convenience: the matrix `toReal S n B` itself is dominated by `B`. -/
theorem Dom_toReal (S n : ℕ) (B : List (List ℕ)) : Dom S n (toReal S n B) B :=
  ⟨fun i j => by simp only [toReal]; positivity, fun _ _ => le_rfl⟩

theorem DomV_toRealV (S n : ℕ) (v : List ℕ) : DomV S n (toRealV S n v) v :=
  ⟨fun i => by simp only [toRealV]; positivity, fun _ => le_rfl⟩

end GMCNumerics
