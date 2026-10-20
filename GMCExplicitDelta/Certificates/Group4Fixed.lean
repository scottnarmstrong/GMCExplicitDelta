module

public import GMCExplicitDelta.Numerics.NatMatrix
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Abel

/-!
# Fixed-point matrix toolkit for the group 4 certificates

Scaling by a rational, entrywise sums and `+1` per entry, on top of `NatMatrix` (`mulUp`,
`Dom`).  Every operation rounds up, with a `Dom` soundness lemma.
-/

@[expose] public section

namespace GMCExplicitDelta.Certificates.Group4

open GMCNumerics Matrix

/-- Entrywise `⌈(p/q) x⌉`. -/
def scaleUp (p q : ℕ) (A : List (List ℕ)) : List (List ℕ) :=
  A.map fun r => r.map fun x => ceilDiv (p * x) q

/-- Entrywise sum of lists (missing entries are `0`). -/
def addL : List ℕ → List ℕ → List ℕ
  | a :: as, b :: bs => (a + b) :: addL as bs
  | as, [] => as
  | [], bs => bs

/-- Entrywise sum of list matrices. -/
def addM : List (List ℕ) → List (List ℕ) → List (List ℕ)
  | a :: as, b :: bs => addL a b :: addM as bs
  | as, [] => as
  | [], bs => bs

/-- Add one unit to every entry. -/
def addOne (A : List (List ℕ)) : List (List ℕ) := A.map fun r => r.map fun x => x + 1

/-- The zero `n × n` list matrix. -/
def zeroM (n : ℕ) : List (List ℕ) := (List.range n).map fun _ => (List.range n).map fun _ => 0

theorem ceilDiv_zero (q : ℕ) : ceilDiv 0 q = 0 := by
  unfold ceilDiv
  rcases Nat.eq_zero_or_pos q with h | h
  · simp [h]
  · exact Nat.div_eq_of_lt (by omega)

theorem getD_addL : ∀ (a b : List ℕ) (j : ℕ), (addL a b).getD j 0 = a.getD j 0 + b.getD j 0
  | [], [], j => by simp [addL]
  | [], b :: bs, j => by simp [addL]
  | a :: as, [], j => by simp [addL]
  | a :: as, b :: bs, j => by
    cases j with
    | zero => simp [addL]
    | succ j => simpa [addL] using getD_addL as bs j

theorem length_addL : ∀ (a b : List ℕ), (addL a b).length = max a.length b.length
  | [], [] => by simp [addL]
  | [], b :: bs => by simp [addL]
  | a :: as, [] => by simp [addL]
  | a :: as, b :: bs => by simp [addL, length_addL as bs]

theorem getE_addM : ∀ (A B : List (List ℕ)) (i j : ℕ),
    getE (addM A B) i j = getE A i j + getE B i j
  | [], [], i, j => by simp [addM, getE]
  | [], b :: bs, i, j => by simp [addM, getE]
  | a :: as, [], i, j => by simp [addM, getE]
  | a :: as, b :: bs, i, j => by
    cases i with
    | zero => simpa [addM, getE] using getD_addL a b j
    | succ i => simpa [addM, getE] using getE_addM as bs i j

theorem length_addM : ∀ (A B : List (List ℕ)), (addM A B).length = max A.length B.length
  | [], [] => by simp [addM]
  | [], b :: bs => by simp [addM]
  | a :: as, [] => by simp [addM]
  | a :: as, b :: bs => by simp [addM, length_addM as bs]

theorem rows_addM {n : ℕ} : ∀ (A B : List (List ℕ)), (∀ r ∈ A, r.length = n) →
    (∀ r ∈ B, r.length = n) → ∀ r ∈ addM A B, r.length = n
  | [], [], _, _ => by simp [addM]
  | [], b :: bs, _, hB => by simpa [addM] using hB
  | a :: as, [], hA, _ => by simpa [addM] using hA
  | a :: as, b :: bs, hA, hB => by
    intro r hr
    simp only [addM, List.mem_cons] at hr
    rcases hr with rfl | hr
    · rw [length_addL, hA a (by simp), hB b (by simp), max_self]
    · exact rows_addM as bs (fun r hr => hA r (by simp [hr])) (fun r hr => hB r (by simp [hr])) r hr

theorem WF_addM {n : ℕ} {A B : List (List ℕ)} (hA : WF n A) (hB : WF n B) : WF n (addM A B) :=
  ⟨by rw [length_addM, hA.1, hB.1, max_self], rows_addM A B hA.2 hB.2⟩

theorem getE_map_map (f : ℕ → ℕ) (hf : f 0 = 0) (A : List (List ℕ)) (i j : ℕ) :
    getE (A.map fun r => r.map f) i j = f (getE A i j) := by
  by_cases hi : i < A.length
  · by_cases hj : j < (A[i]).length
    · simp [getE, List.getD_eq_getElem?_getD, hi, hj]
    · simp [getE, List.getD_eq_getElem?_getD, hi, hj, hf]
  · simp [getE, List.getD_eq_getElem?_getD, hi, hf]

theorem getE_scaleUp (p q : ℕ) (A : List (List ℕ)) (i j : ℕ) :
    getE (scaleUp p q A) i j = ceilDiv (p * getE A i j) q := by
  unfold scaleUp
  exact getE_map_map (fun x => ceilDiv (p * x) q) (by simp [ceilDiv_zero]) A i j

theorem WF_map_map {n : ℕ} (f : ℕ → ℕ) {A : List (List ℕ)} (hA : WF n A) :
    WF n (A.map fun r => r.map f) := by
  refine ⟨by simp [hA.1], ?_⟩
  intro r hr
  simp only [List.mem_map] at hr
  obtain ⟨a, ha, rfl⟩ := hr
  simp [hA.2 a ha]

theorem WF_scaleUp {n : ℕ} (p q : ℕ) {A : List (List ℕ)} (hA : WF n A) : WF n (scaleUp p q A) :=
  WF_map_map _ hA

theorem WF_addOne {n : ℕ} {A : List (List ℕ)} (hA : WF n A) : WF n (addOne A) :=
  WF_map_map _ hA

theorem WF_zeroM (n : ℕ) : WF n (zeroM n) := by
  refine ⟨by simp [zeroM], ?_⟩
  intro r hr
  simp only [zeroM, List.mem_map] at hr
  obtain ⟨a, -, rfl⟩ := hr
  simp

theorem getE_zeroM {n i j : ℕ} (hi : i < n) (hj : j < n) : getE (zeroM n) i j = 0 := by
  simp [getE, zeroM, List.getD_eq_getElem?_getD, hi, hj]

theorem Dom_scaleUp {S n p q : ℕ} (hS : 0 < S) (hq : 0 < q) {X : Matrix (Fin n) (Fin n) ℝ}
    {A : List (List ℕ)} (hX : Dom S n X A) :
    Dom S n (((p : ℝ) / q) • X) (scaleUp p q A) := by
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · simp only [Matrix.smul_apply, smul_eq_mul]
    exact mul_nonneg (by positivity) (hX.1 i j)
  · simp only [Matrix.smul_apply, smul_eq_mul, toReal, getE_scaleUp]
    have h1 := hX.2 i j
    simp only [toReal] at h1
    have h2 : ((p : ℝ) * getE A i j) / q ≤ ceilDiv (p * getE A i j) q := by
      have := div_le_ceilDiv (a := p * getE A i j) hq
      push_cast at this; exact this
    calc (p : ℝ) / q * X i j ≤ (p : ℝ) / q * ((getE A i j : ℝ) / S) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ((p : ℝ) * getE A i j) / q / S := by field_simp
      _ ≤ (ceilDiv (p * getE A i j) q : ℝ) / S := by gcongr

theorem Dom_addM {S n : ℕ} (hS : 0 < S) {X Y : Matrix (Fin n) (Fin n) ℝ} {A B : List (List ℕ)}
    (hX : Dom S n X A) (hY : Dom S n Y B) : Dom S n (X + Y) (addM A B) := by
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  refine ⟨fun i j => add_nonneg (hX.1 i j) (hY.1 i j), fun i j => ?_⟩
  simp only [Matrix.add_apply, toReal, getE_addM]
  have h1 := hX.2 i j
  have h2 := hY.2 i j
  simp only [toReal] at h1 h2
  push_cast
  rw [add_div]
  exact add_le_add h1 h2

theorem getE_addOne {A : List (List ℕ)} {i j : ℕ} (hi : i < A.length) (hj : j < (A[i]).length) :
    getE (addOne A) i j = getE A i j + 1 := by
  simp [addOne, getE, List.getD_eq_getElem?_getD, hi, hj]

theorem Dom_addOne {S n : ℕ} (hS : 0 < S) {X : Matrix (Fin n) (Fin n) ℝ} {A : List (List ℕ)}
    (hA : WF n A) (hX : Dom S n X A) :
    Dom S n (fun i j => X i j + 1 / (S : ℝ)) (addOne A) := by
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  refine ⟨fun i j => add_nonneg (hX.1 i j) (by positivity), fun i j => ?_⟩
  have hi : i.1 < A.length := by rw [hA.1]; exact i.2
  have hj : j.1 < (A[i.1]).length := by rw [hA.2 _ (List.getElem_mem hi)]; exact j.2
  simp only [toReal, getE_addOne hi hj]
  have h1 := hX.2 i j
  simp only [toReal] at h1
  push_cast
  rw [add_div]
  exact add_le_add h1 le_rfl

theorem Dom_zeroM {S n : ℕ} (hS : 0 < S) : Dom S n (0 : Matrix (Fin n) (Fin n) ℝ) (zeroM n) := by
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  refine ⟨fun i j => le_rfl, fun i j => ?_⟩
  simp [toReal, getE_zeroM i.2 j.2]

/-! ### The truncated exponential-type series -/

/-- Iterates `T_{k+1} = (1/(k+1)) (Ms * T_k)` with the running sum of the `T_k`. -/
def serAux (S n : ℕ) (Ms : List (List ℕ)) : ℕ → ℕ → List (List ℕ) → List (List ℕ) →
    List (List ℕ) × List (List ℕ)
  | 0, _, T, acc => (T, acc)
  | j + 1, k, T, acc =>
    let T' := scaleUp 1 (k + 1) (mulUp S n Ms T)
    serAux S n Ms j (k + 1) T' (addM acc T')

theorem WF_serAux {S n : ℕ} {Ms : List (List ℕ)} (hM : WF n Ms) :
    ∀ (j k : ℕ) (T acc : List (List ℕ)), WF n T → WF n acc →
      WF n (serAux S n Ms j k T acc).1 ∧ WF n (serAux S n Ms j k T acc).2 := by
  intro j
  induction j with
  | zero => intro k T acc hT hacc; exact ⟨hT, hacc⟩
  | succ j ih =>
    intro k T acc hT hacc
    have hT' : WF n (scaleUp 1 (k + 1) (mulUp S n Ms T)) := WF_scaleUp _ _ (WF_mulUp hM)
    exact ih (k + 1) _ _ hT' (WF_addM hacc hT')

theorem serAux_add (S n : ℕ) (Ms : List (List ℕ)) :
    ∀ (a b k : ℕ) (T acc : List (List ℕ)),
      serAux S n Ms (a + b) k T acc =
        serAux S n Ms b (k + a) (serAux S n Ms a k T acc).1 (serAux S n Ms a k T acc).2 := by
  intro a
  induction a with
  | zero => intro b k T acc; simp [serAux]
  | succ a ih =>
    intro b k T acc
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [serAux]
    rw [ih b (k + 1), show k + 1 + a = k + (a + 1) by omega]

/-- Soundness of `serAux` for the terms `(Mr ^ k) / k!`. -/
theorem Dom_serAux {S n : ℕ} (hS : 0 < S) {Ms : List (List ℕ)} (hM : WF n Ms)
    {Mr : Matrix (Fin n) (Fin n) ℝ} (hMr : Dom S n Mr Ms) :
    ∀ (j k : ℕ) (T acc : List (List ℕ)), WF n T → WF n acc →
      Dom S n (((k.factorial : ℝ))⁻¹ • Mr ^ k) T →
      ∀ X : Matrix (Fin n) (Fin n) ℝ, Dom S n X acc →
        Dom S n (((k + j).factorial : ℝ)⁻¹ • Mr ^ (k + j)) (serAux S n Ms j k T acc).1 ∧
        Dom S n (X + ∑ i ∈ Finset.range j, (((k + 1 + i).factorial : ℝ))⁻¹ • Mr ^ (k + 1 + i))
          (serAux S n Ms j k T acc).2 := by
  intro j
  induction j with
  | zero =>
    intro k T acc hT hacc hTd X hX
    refine ⟨by simpa [serAux] using hTd, by simpa [serAux] using hX⟩
  | succ j ih =>
    intro k T acc hT hacc hTd X hX
    have hT' : WF n (scaleUp 1 (k + 1) (mulUp S n Ms T)) := WF_scaleUp _ _ (WF_mulUp hM)
    have hmul : Dom S n (Mr * (((k.factorial : ℝ))⁻¹ • Mr ^ k)) (mulUp S n Ms T) :=
      Dom_mul hS hM hT hMr hTd
    have hsc := Dom_scaleUp (p := 1) (q := k + 1) hS (by omega) hmul
    have e1 : (((1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ)) • (Mr * (((k.factorial : ℝ))⁻¹ • Mr ^ k)) =
        (((k + 1).factorial : ℝ))⁻¹ • Mr ^ (k + 1) := by
      rw [Matrix.mul_smul, smul_smul, ← pow_succ', Nat.factorial_succ]
      congr 1
      push_cast
      field_simp
    rw [e1] at hsc
    have hadd := Dom_addM hS hX hsc
    have := ih (k + 1) _ _ hT' (WF_addM hacc hT') hsc _ hadd
    simp only [serAux]
    refine ⟨?_, ?_⟩
    · have e2 : k + 1 + j = k + (j + 1) := by omega
      rw [← e2]; exact this.1
    · have e3 : X + ∑ i ∈ Finset.range (j + 1), (((k + 1 + i).factorial : ℝ))⁻¹ • Mr ^ (k + 1 + i)
          = X + (((k + 1).factorial : ℝ))⁻¹ • Mr ^ (k + 1) +
            ∑ i ∈ Finset.range j, (((k + 1 + 1 + i).factorial : ℝ))⁻¹ • Mr ^ (k + 1 + 1 + i) := by
        rw [Finset.sum_range_succ' (fun i => (((k + 1 + i).factorial : ℝ))⁻¹ • Mr ^ (k + 1 + i)) j]
        have h3 : ∑ i ∈ Finset.range j, (((k + 1 + (i + 1)).factorial : ℝ))⁻¹ • Mr ^ (k + 1 + (i + 1))
            = ∑ i ∈ Finset.range j, (((k + 1 + 1 + i).factorial : ℝ))⁻¹ • Mr ^ (k + 1 + 1 + i) :=
          Finset.sum_congr rfl fun i _ => by rw [show k + 1 + (i + 1) = k + 1 + 1 + i by omega]
        rw [h3]
        simp only [Nat.add_zero]
        abel
      rw [e3]; exact this.2

end GMCExplicitDelta.Certificates.Group4
