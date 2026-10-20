module

public import GMCExplicitDelta.Haar.NeumannModes

/-!
# Test fields for the H5 duality and their Hessian identity (H3 for cosine polynomials)

For a finite set `S` of natural frequency vectors and coefficients `β`, the test fields
`v_j = ∑_{q ∈ S} (-β_q f_{q,j}) M_{j,q}` (`f_{q,j} = π q_j/ℓ`, `M_{j,q}` the mixed mode, sine in
coordinate `j`) are the partial derivatives `∂_j z` of `z = ∑ β_q C_q`. Their line derivatives
`∂_i v_j = testHess` are box-mode polynomials, and by orthogonality
`∑_{i,j} ‖∂_i v_j‖² = ∑_q β_q² λ_q² / m_q` (`λ_q = ∑_j f_{q,j}²`, `m_q = ∏ᵢ (1 or 2)`), the
cosine-polynomial case of the Neumann `H²` identity H3.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open Homogenization

namespace GMCExplicitDelta.Haar

variable {d : ℕ}

open Torus

/-- The multiplicity `m_q = ∏ᵢ (1 if qᵢ = 0, else 2)` (`⨍ C_q² = 1/m_q`). -/
def modeMult (q : Fin d → ℕ) : ℝ := ∏ i, if q i = 0 then (1 : ℝ) else 2

theorem modeMult_pos (q : Fin d → ℕ) : 0 < modeMult q :=
  Finset.prod_pos fun i _ => by split_ifs <;> norm_num

theorem boxNormSq_eq_inv_modeMult (O : Finset (Fin d)) (q : Fin d → ℕ)
    (hO : ∀ k ∈ O, q k ≠ 0) : boxNormSq O q = (modeMult q)⁻¹ := by
  unfold boxNormSq modeMult
  rw [← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  unfold factorNormSq
  by_cases hk : k ∈ O
  · rw [if_pos hk, if_neg (hO k hk), if_neg (hO k hk)]
    norm_num
  · rw [if_neg hk]
    split_ifs <;> norm_num

theorem mul_boxNormSq_eq_div (O : Finset (Fin d)) (q : Fin d → ℕ) {X : ℝ}
    (hX : ∀ k ∈ O, q k = 0 → X = 0) : X * boxNormSq O q = X / modeMult q := by
  by_cases hall : ∀ k ∈ O, q k ≠ 0
  · rw [boxNormSq_eq_inv_modeMult O q hall, div_eq_mul_inv]
  · push_neg at hall
    obtain ⟨k, hk, hqk⟩ := hall
    rw [hX k hk hqk, zero_mul, zero_div]

theorem cubeFreq_natVec_eq_zero (Q : TriadicCube d) {q : Fin d → ℕ} {k : Fin d} (h : q k = 0) :
    cubeFreq Q (natVec q) k = 0 := by
  simp [cubeFreq, natVec, h]

theorem cubeEig_natVec_pos (Q : TriadicCube d) {q : Fin d → ℕ} (hq : q ≠ 0) :
    0 < cubeEig Q (natVec q) := by
  obtain ⟨i, hi⟩ : ∃ i, q i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hq (funext h)
  have hℓ := cubeScaleFactor_pos' Q
  have hf : cubeFreq Q (natVec q) i ≠ 0 := by
    unfold cubeFreq natVec
    have : ((q i : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hi
    exact div_ne_zero (mul_ne_zero Real.pi_ne_zero this) hℓ.ne'
  unfold cubeEig
  exact lt_of_lt_of_le (pow_pos (abs_pos.2 hf) 2 |>.trans_eq (sq_abs _))
    (Finset.single_le_sum (fun j _ => sq_nonneg (cubeFreq Q (natVec q) j)) (Finset.mem_univ i))

/-! ### The test fields -/

/-- `v_j = ∑_{q ∈ S} (-β_q f_{q,j}) M_{j,q}`. -/
def testField (Q : TriadicCube d) (S : Finset (Fin d → ℕ)) (β : (Fin d → ℕ) → ℝ) (j : Fin d)
    (x : Vec d) : ℝ :=
  ∑ q ∈ S, (-(β q) * cubeFreq Q (natVec q) j) *
    boxMode (cubeCorner Q) (cubeScaleFactor Q) {j} (natVec q) x

/-- The coordinates switched in `∂_i M_{j,q}`. -/
def hessSet (i j : Fin d) : Finset (Fin d) := if i = j then ∅ else {i, j}

/-- The coefficient of `∂_i v_j` on the mode `q`. -/
def hessCoef (Q : TriadicCube d) (β : (Fin d → ℕ) → ℝ) (j i : Fin d) (q : Fin d → ℕ) : ℝ :=
  -(β q) * cubeFreq Q (natVec q) j * ((if i = j then 1 else -1) * cubeFreq Q (natVec q) i)

/-- `∂_i v_j`. -/
def testHess (Q : TriadicCube d) (S : Finset (Fin d → ℕ)) (β : (Fin d → ℕ) → ℝ) (j i : Fin d)
    (x : Vec d) : ℝ :=
  ∑ q ∈ S, hessCoef Q β j i q *
    boxMode (cubeCorner Q) (cubeScaleFactor Q) (hessSet i j) (natVec q) x

theorem continuous_testField (Q : TriadicCube d) (S : Finset (Fin d → ℕ))
    (β : (Fin d → ℕ) → ℝ) (j : Fin d) : Continuous (testField Q S β j) :=
  continuous_sum_boxMode _ _ _ S _

theorem continuous_testHess (Q : TriadicCube d) (S : Finset (Fin d → ℕ))
    (β : (Fin d → ℕ) → ℝ) (j i : Fin d) : Continuous (testHess Q S β j i) :=
  continuous_sum_boxMode _ _ _ S _

theorem memLp_testField (Q : TriadicCube d) (S : Finset (Fin d → ℕ)) (β : (Fin d → ℕ) → ℝ)
    (j : Fin d) : MemLp (testField Q S β j) 2 (normalizedCubeMeasure Q) :=
  memLp_of_continuous_bound (continuous_testField Q S β j) _
    (fun x => abs_sum_boxMode_le _ _ _ S _ x) 2

theorem memLp_testHess (Q : TriadicCube d) (S : Finset (Fin d → ℕ)) (β : (Fin d → ℕ) → ℝ)
    (j i : Fin d) : MemLp (testHess Q S β j i) 2 (normalizedCubeMeasure Q) :=
  memLp_of_continuous_bound (continuous_testHess Q S β j i) _
    (fun x => abs_sum_boxMode_le _ _ _ S _ x) 2

/-- `testHess` is the line derivative of `testField`. -/
theorem hasDerivAt_testField (Q : TriadicCube d) (S : Finset (Fin d → ℕ))
    (β : (Fin d → ℕ) → ℝ) (j i : Fin d) (x : Vec d) :
    HasDerivAt (fun t => testField Q S β j (Function.update x i t)) (testHess Q S β j i x)
      (x i) := by
  have h := HasDerivAt.fun_sum (u := S) fun q _ =>
    (hasDerivAt_boxMode_update (cubeCorner Q) (cubeScaleFactor Q) {j} (natVec q) i x).const_mul
      (-(β q) * cubeFreq Q (natVec q) j)
  refine h.congr_deriv ?_
  unfold testHess
  refine Finset.sum_congr rfl fun q _ => ?_
  unfold hessCoef hessSet cubeFreq
  by_cases hij : i = j
  · subst hij
    simp only [Finset.mem_singleton_self, Finset.erase_singleton, if_true, eq_self_iff_true]
    ring
  · simp only [hij, if_false, Finset.mem_singleton]
    ring

/-- `‖∂_i v_j‖² = ∑_q β_q² f_{q,j}² f_{q,i}² / m_q`. -/
theorem energy_testHess (Q : TriadicCube d) (S : Finset (Fin d → ℕ)) (β : (Fin d → ℕ) → ℝ)
    (j i : Fin d) :
    energy Q (testHess Q S β j i) =
      ∑ q ∈ S, β q ^ 2 * cubeFreq Q (natVec q) j ^ 2 * cubeFreq Q (natVec q) i ^ 2 /
        modeMult q := by
  rw [energy_eq_integral_sq, ← boxMeasure_eq_normalizedCubeMeasure]
  unfold testHess
  rw [integral_sq_sum_boxMode _ (cubeScaleFactor_pos' Q)]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hsq : hessCoef Q β j i q ^ 2 =
      β q ^ 2 * cubeFreq Q (natVec q) j ^ 2 * cubeFreq Q (natVec q) i ^ 2 := by
    unfold hessCoef
    split_ifs <;> ring
  rw [hsq]
  refine mul_boxNormSq_eq_div _ q fun k hk hqk => ?_
  unfold hessSet at hk
  split_ifs at hk with hij
  · simp at hk
  · rcases Finset.mem_insert.1 hk with h | h
    · rw [h] at hqk
      rw [cubeFreq_natVec_eq_zero Q hqk]
      ring
    · rw [Finset.mem_singleton.1 h] at hqk
      rw [cubeFreq_natVec_eq_zero Q hqk]
      ring

/-- **Hessian identity** for cosine polynomials: `∑_{i,j} ‖∂_i v_j‖² = ∑_q β_q² λ_q² / m_q`. -/
theorem sum_energy_testHess (Q : TriadicCube d) (S : Finset (Fin d → ℕ))
    (β : (Fin d → ℕ) → ℝ) :
    ∑ j, ∑ i, energy Q (testHess Q S β j i) =
      ∑ q ∈ S, β q ^ 2 * cubeEig Q (natVec q) ^ 2 / modeMult q := by
  simp_rw [energy_testHess]
  have key : ∀ q, ∑ j, ∑ i, β q ^ 2 * cubeFreq Q (natVec q) j ^ 2 *
      cubeFreq Q (natVec q) i ^ 2 / modeMult q =
        β q ^ 2 * cubeEig Q (natVec q) ^ 2 / modeMult q := by
    intro q
    unfold cubeEig
    rw [sq (∑ j, cubeFreq Q (natVec q) j ^ 2), Finset.sum_mul_sum, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  calc ∑ j, ∑ i, ∑ q ∈ S, β q ^ 2 * cubeFreq Q (natVec q) j ^ 2 *
        cubeFreq Q (natVec q) i ^ 2 / modeMult q
      = ∑ j, ∑ q ∈ S, ∑ i, β q ^ 2 * cubeFreq Q (natVec q) j ^ 2 *
        cubeFreq Q (natVec q) i ^ 2 / modeMult q :=
        Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ q ∈ S, ∑ j, ∑ i, β q ^ 2 * cubeFreq Q (natVec q) j ^ 2 *
        cubeFreq Q (natVec q) i ^ 2 / modeMult q := Finset.sum_comm
    _ = ∑ q ∈ S, β q ^ 2 * cubeEig Q (natVec q) ^ 2 / modeMult q :=
        Finset.sum_congr rfl fun q _ => key q

/-- The pairing of a field component with a test field. -/
theorem pairing_testField (Q : TriadicCube d) (S : Finset (Fin d → ℕ))
    (β : (Fin d → ℕ) → ℝ) (j : Fin d) {h : Vec d → ℝ}
    (hh : MemLp h 2 (normalizedCubeMeasure Q)) :
    pairing Q h (testField Q S β j) =
      ∑ q ∈ S, (-(β q) * cubeFreq Q (natVec q) j) *
        ∫ x, cubeSin Q j (natVec q) x * h x ∂normalizedCubeMeasure Q := by
  unfold pairing testField
  rw [cubeAverage_eq_integral_normalizedCubeMeasure]
  have hint : ∀ q ∈ S, Integrable (fun x => h x * ((-(β q) * cubeFreq Q (natVec q) j) *
      boxMode (cubeCorner Q) (cubeScaleFactor Q) {j} (natVec q) x))
      (normalizedCubeMeasure Q) := fun q _ =>
    ((memLp_mode_mul hh (continuous_boxMode _ _ {j} (natVec q))
      (abs_boxMode_le _ _ {j} (natVec q))).const_mul
        (-(β q) * cubeFreq Q (natVec q) j)).congr
      (Eventually.of_forall fun x => by beta_reduce; ring)
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← integral_const_mul]
  congr 1
  funext x
  unfold cubeSin
  ring

end GMCExplicitDelta.Haar
