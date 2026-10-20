module

public import GMCExplicitDelta.Contract.DerivedFresh
public import GMCExplicitDelta.Numerics.NatMatrix
public import GMCExplicitDelta.Numerics.Enclosures
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Group 4: from fixed-point bounds to the fresh moment, seeds and the map `Φ`

Row-independent real lemmas: the profile bound `μ_r ≤ ρ_r`, the bound on `D_next`, vector
domination, the fresh moment and the seed sums via `checkVec_sound`, 32nd-root comparisons and
monotonicity of `Φ_γ`.
-/

@[expose] public section

open Matrix GMCNumerics GMCExplicitDelta.Contract Real

namespace GMCExplicitDelta.Certificates.Group4

/-! ### Roots -/

theorem rpow32_lt {x D : ℝ} (hx : 0 ≤ x) (hD : 0 ≤ D) (h : x < D ^ 32) :
    x ^ ((1 : ℝ) / 32) < D := by
  by_contra hc
  push_neg at hc
  have h1 := pow_le_pow_left₀ hD hc 32
  have h2 : (x ^ ((1 : ℝ) / 32)) ^ 32 = x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num
  linarith

theorem rpow32_le {x s : ℝ} (hx : 0 ≤ x) (hs : 0 ≤ s) (h : x ≤ s ^ 32) :
    x ^ ((1 : ℝ) / 32) ≤ s := by
  by_contra hc
  push_neg at hc
  have h1 := pow_lt_pow_left₀ hc hs (by norm_num : (32 : ℕ) ≠ 0)
  have h2 : (x ^ ((1 : ℝ) / 32)) ^ 32 = x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num
  linarith

theorem pow_rpow_div_eq {x : ℝ} (hx : 0 ≤ x) (m n : ℕ) (hn : 0 < n) :
    (x ^ ((m : ℝ) / n)) ^ n = x ^ m := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  have : (m : ℝ) / n * n = m := div_mul_cancel₀ _ (by positivity)
  rw [this, Real.rpow_natCast]

/-! ### The old moment profile -/

theorem profile_nonneg {d : ℕ} (row : Row d) {D F : ℝ} (hFn : 0 < row.Fnext F)
    (hDn : 0 < row.Dnext D F) (r : ℕ) : 0 ≤ row.profile D F r := by
  unfold Row.profile
  split_ifs
  · exact zero_le_one
  · exact mul_nonneg (Real.rpow_nonneg hFn.le _) (Real.rpow_nonneg hDn.le _)

theorem profile_le {d : ℕ} (row : Row d) {D F Fp ρ : ℝ} (r : ℕ) (hr1 : 1 ≤ r) (hr : r ≤ 32)
    (hFn : 0 < row.Fnext F) (hDn : 0 < row.Dnext D F) (hDF : row.Dnext D F ≤ Fp)
    (hρ0 : 0 ≤ ρ) (hρ : row.Fnext F ^ (32 - r) * Fp ^ (32 * (r - 1)) ≤ ρ ^ 31) :
    row.profile D F r ≤ ρ := by
  have hr0 : r ≠ 0 := by omega
  unfold Row.profile
  rw [if_neg hr0]
  have h1 : (32 - (r : ℝ)) = ((32 - r : ℕ) : ℝ) := by rw [Nat.cast_sub hr]; norm_num
  have h2 : (32 * ((r : ℝ) - 1)) = ((32 * (r - 1) : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_sub hr1]; norm_num
  rw [h1, h2]
  set X := row.Fnext F ^ (((32 - r : ℕ) : ℝ) / 31) * row.Dnext D F ^
    (((32 * (r - 1) : ℕ) : ℝ) / 31) with hX
  have hX0 : 0 ≤ X := mul_nonneg (Real.rpow_nonneg hFn.le _) (Real.rpow_nonneg hDn.le _)
  have hX31 : X ^ 31 = row.Fnext F ^ (32 - r) * row.Dnext D F ^ (32 * (r - 1)) := by
    rw [hX, mul_pow]
    have a1 := pow_rpow_div_eq hFn.le (32 - r) 31 (by norm_num)
    have a2 := pow_rpow_div_eq hDn.le (32 * (r - 1)) 31 (by norm_num)
    simp only [Nat.cast_ofNat] at a1 a2
    rw [a1, a2]
  have : X ^ 31 ≤ ρ ^ 31 := by
    rw [hX31]
    refine le_trans ?_ hρ
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hDn.le hDF _) (by positivity)
  exact le_of_pow_le_pow_left₀ (by norm_num) hρ0 this

/-! ### Vector domination -/

theorem domV_profile {d : ℕ} (row : Row d) {D F Fp : ℝ} {S : ℕ} (hS : 0 < S) {ρ : List ℕ}
    (hρ0 : ρ.getD 0 0 = S) (hFn : 0 < row.Fnext F) (hDn : 0 < row.Dnext D F)
    (hDF : row.Dnext D F ≤ Fp)
    (hρ : ∀ r : ℕ, 1 ≤ r → r ≤ 32 →
      row.Fnext F ^ (32 - r) * Fp ^ (32 * (r - 1)) ≤ (((ρ.getD r 0 : ℕ) : ℝ) / S) ^ 31) :
    DomV S 33 (fun r : Fin 33 => row.profile D F r) ρ := by
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  refine ⟨fun r => profile_nonneg row hFn hDn _, fun r => ?_⟩
  simp only [toRealV]
  by_cases h0 : (r : ℕ) = 0
  · rw [h0, hρ0]
    simp [Row.profile, hS'.ne']
  · exact profile_le row (r : ℕ) (by omega) (by omega) hFn hDn hDF (by positivity)
      (hρ (r : ℕ) (by omega) (by omega))

/-- The powers `x₀^r` are dominated by `⌈(X/S)^r⌉` when `0 ≤ x₀ ≤ X/S`. -/
def powList (S X : ℕ) : List ℕ :=
  (List.range 33).map fun r => if r = 0 then S else ceilDiv (X ^ r) (S ^ (r - 1))

theorem domV_pow {S X : ℕ} (hS : 0 < S) {x0 : ℝ} (h0 : 0 ≤ x0) (hx : x0 ≤ (X : ℝ) / S) :
    DomV S 33 (fun r : Fin 33 => x0 ^ (r : ℕ)) (powList S X) := by
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  refine ⟨fun r => pow_nonneg h0 _, fun r => ?_⟩
  simp only [toRealV, powList]
  have hr : (r : ℕ) < 33 := r.2
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, hr, if_true,
    Option.map_some, Option.getD_some]
  by_cases h : (r : ℕ) = 0
  · simp [h, hS'.ne']
  · simp only [h, if_false]
    have hSp : 0 < S ^ ((r : ℕ) - 1) := by positivity
    have h1 : (X : ℝ) ^ (r : ℕ) / ((S ^ ((r : ℕ) - 1) : ℕ) : ℝ) ≤
        (ceilDiv (X ^ (r : ℕ)) (S ^ ((r : ℕ) - 1)) : ℕ) := by
      have := div_le_ceilDiv (a := X ^ (r : ℕ)) hSp
      push_cast at this ⊢
      exact this
    calc x0 ^ (r : ℕ) ≤ ((X : ℝ) / S) ^ (r : ℕ) := pow_le_pow_left₀ h0 hx _
      _ = ((X : ℝ) ^ (r : ℕ) / ((S ^ ((r : ℕ) - 1) : ℕ) : ℝ)) / S := by
          rw [div_pow]
          have : (S : ℝ) ^ (r : ℕ) = (S : ℝ) ^ ((r : ℕ) - 1) * S := by
            rw [← pow_succ]; congr 1; omega
          rw [this]; push_cast; field_simp
      _ ≤ _ := by gcongr

/-! ### Fresh moment and seed sums -/

theorem freshSum_bounds {δ : ℝ} {h S fuel c : ℕ} {B : List (List ℕ)} {v : List ℕ}
    {x : Fin 33 → ℝ} (hS : 0 < S) (hk : h < 2 ^ fuel)
    (hB : Dom S 33 (bandMatrix δ) B) (hchk : checkVec S 33 fuel B h v 32 c = true)
    (hx : DomV S 33 x v) :
    0 ≤ ∑ r : Fin 33, bandRow δ h r * x r ∧ ∑ r : Fin 33, bandRow δ h r * x r ≤ (c : ℝ) / S := by
  have hWF : WF 33 B := by
    simp only [checkVec, Bool.and_eq_true] at hchk
    exact wfM_iff.mp hchk.1.1
  have hP := Dom_powUp (fuel := fuel) hS hWF hB hk
  constructor
  · exact Finset.sum_nonneg fun r _ => mul_nonneg (hP.1 32 r) (hx.1 r)
  · have := checkVec_sound (i := 32) (by omega) hk (by omega) hchk hB hx
    simpa [Matrix.mulVec, dotProduct, bandRow] using this

end GMCExplicitDelta.Certificates.Group4
