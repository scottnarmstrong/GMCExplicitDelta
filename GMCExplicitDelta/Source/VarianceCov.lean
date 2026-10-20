module

public import GMCExplicitDelta.Source.VarianceProc
public import GMCExplicitDelta.Source.VarianceIBP
public import GMCExplicitDelta.Source.Toeplitz

/-!
# The diagonal covariance and `r ≥ π² s`

For the abstract diagonal process: `C(t) = E G(0) G(t)` is positive semidefinite on the lattice
`ℤ/n`, vanishes for `t ≥ 1`, hence `C(1/n) ≤ s cos(π/(n+1))` (Toeplitz), while
`C(h) ≥ s - r h²/2`; so `π² s ≤ r`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace GMCExplicitDelta.Source

open MeasureTheory ProbabilityTheory

namespace DiagProc

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {G G' : ℝ → Ω → ℝ} {a b c : Ω → ℝ} (H : DiagProc P G G' a b c)

/-- The covariance sampled on the lattice `ℤ/n`. -/
noncomputable def covLat (n : ℕ) (k : ℤ) : ℝ := H.cov ((k : ℝ) / n)

include H

theorem covLat_even (n : ℕ) (k : ℤ) : H.covLat n (-k) = H.covLat n k := by
  unfold covLat
  rw [← H.cov_even ((k : ℝ) / n)]
  congr 1; push_cast; ring

theorem covLat_supp (n : ℕ) (hn : 0 < n) (k : ℤ) (hk : n ≤ k.natAbs) : H.covLat n k = 0 := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have h1 : (1:ℝ) ≤ (k.natAbs : ℝ) / n := by
    rw [le_div_iff₀ hnpos, one_mul]; exact_mod_cast hk
  rcases Int.natAbs_eq k with h | h
  · have hk' : (k : ℝ) = (k.natAbs : ℝ) := by
      have := congrArg (Int.cast : ℤ → ℝ) h
      simpa using this
    unfold covLat
    rw [hk']
    exact H.cov_of_one_le h1
  · have hk' : (k : ℝ) = -(k.natAbs : ℝ) := by
      have := congrArg (Int.cast : ℤ → ℝ) h
      simpa using this
    unfold covLat
    rw [hk', neg_div, H.cov_even]
    exact H.cov_of_one_le h1

theorem covLat_psd (n N : ℕ) (x : Fin N → ℝ) :
    0 ≤ ∑ j : Fin N, ∑ l : Fin N, x j * x l * H.covLat n (((j : ℕ) : ℤ) - ((l : ℕ) : ℤ)) := by
  set f : Fin N → Ω → ℝ := fun i => G (((i : ℕ) : ℝ) / n) with hf
  have hq := integral_sq_sum (P := P) (f := f) (fun i j => H.int_GG _ _) x
  have h0 : 0 ≤ ∫ ω, (∑ i, x i * f i ω) ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
  rw [hq] at h0
  refine h0.trans_eq (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_)
  congr 1
  simp only [hf]
  rw [H.cov_shift]
  unfold covLat
  rw [← H.cov_even]
  congr 1; push_cast; ring

/-- Toeplitz step: `C(1/n) ≤ s cos(π/(n+1))`. -/
theorem cov_le (n : ℕ) (hn : 2 ≤ n) :
    H.cov (1 / (n : ℝ)) ≤ H.cov 0 * Real.cos (Real.pi / ((n : ℝ) + 1)) := by
  have hn0 : 0 < n := by omega
  have hF := fun θ => fejer_nonneg n (H.covLat n) (H.covLat_even n) (H.covLat_supp n hn0)
    (H.covLat_psd n) θ
  have key := coeff_le_of_nonneg_at_nodes n hn (fun j => H.covLat n (j : ℤ))
    (fun k _ => by simpa using hF (node n k))
  simpa [covLat] using key

theorem integral_sq_sub (h : ℝ) :
    ∫ ω, (G h ω - G 0 ω) ^ 2 ∂P = 2 * ∫ ω, G 0 ω ^ 2 ∂P - 2 * H.cov h := by
  have e : ∀ ω, (G h ω - G 0 ω) ^ 2 = (G h ω ^ 2 + G 0 ω ^ 2) - 2 * (G 0 ω * G h ω) := fun ω => by ring
  simp_rw [e]
  have i1 : Integrable (fun ω => G h ω ^ 2 + G 0 ω ^ 2) P := (H.int_sq_G h).add H.int_sq_G0
  have i2 : Integrable (fun ω => 2 * (G 0 ω * G h ω)) P := (H.int_GG 0 h).const_mul 2
  rw [integral_sub i1 i2, integral_add (H.int_sq_G h) H.int_sq_G0, integral_const_mul,
    H.integral_sq_G h]
  unfold cov; ring

theorem measurable_uncurry_G' : Measurable (Function.uncurry G') :=
  measurable_uncurry_of_continuous_of_measurable (fun ω => H.cont' ω) H.mG'

theorem int_sq_sub (h : ℝ) : Integrable (fun ω => (G h ω - G 0 ω) ^ 2) P := by
  have e : ∀ ω, (G h ω - G 0 ω) ^ 2 = (G h ω ^ 2 + G 0 ω ^ 2) - 2 * (G 0 ω * G h ω) := fun ω => by ring
  simp_rw [e]
  exact ((H.int_sq_G h).add H.int_sq_G0).sub ((H.int_GG 0 h).const_mul 2)

/-- Fubini for `∫₀ʰ G'(τ)² dτ`. -/
theorem fubini_sq_G' {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    Integrable (fun ω => ∫ τ in (0:ℝ)..h, G' τ ω ^ 2) P ∧
    ∫ ω, (∫ τ in (0:ℝ)..h, G' τ ω ^ 2) ∂P = h * ∫ ω, G' 0 ω ^ 2 ∂P := by
  have hmeas : Measurable (Function.uncurry fun (τ : ℝ) (ω : Ω) => G' τ ω ^ 2) :=
    H.measurable_uncurry_G'.pow_const 2
  obtain ⟨hI, hS⟩ := integral_intervalIntegral_swap (P := P) hmeas hh (B := fun ω => b ω ^ 2)
    H.int_sq_b (fun ω t ht => by
      rw [abs_of_nonneg (sq_nonneg _), ← sq_abs (G' t ω)]
      exact pow_le_pow_left₀ (abs_nonneg _) (H.bG' ω t ⟨ht.1, ht.2.trans hh1⟩) 2)
  refine ⟨hI, ?_⟩
  rw [← hS]
  simp_rw [H.integral_sq_G']
  simp

theorem sq_increment_le {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    ∫ ω, (G h ω - G 0 ω) ^ 2 ∂P ≤ h * (h * ∫ ω, G' 0 ω ^ 2 ∂P) := by
  obtain ⟨hI, hS⟩ := H.fubini_sq_G' hh hh1
  calc ∫ ω, (G h ω - G 0 ω) ^ 2 ∂P
      ≤ ∫ ω, h * (∫ τ in (0:ℝ)..h, G' τ ω ^ 2) ∂P := by
        refine integral_mono (H.int_sq_sub h) (hI.const_mul h) fun ω => ?_
        have hftc := ftc_diag (G := fun s => G s ω) (G' := fun s => G' s ω) (H.hasDeriv ω) (H.cont' ω) 0 h
        rw [← hftc]
        exact sq_integral_le (H.cont' ω) hh
    _ = h * ∫ ω, (∫ τ in (0:ℝ)..h, G' τ ω ^ 2) ∂P := integral_const_mul _ _
    _ = h * (h * ∫ ω, G' 0 ω ^ 2 ∂P) := by rw [hS]

theorem cov_lower {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    ∫ ω, G 0 ω ^ 2 ∂P - (∫ ω, G' 0 ω ^ 2 ∂P) * h ^ 2 / 2 ≤ H.cov h := by
  have := H.sq_increment_le hh hh1
  rw [H.integral_sq_sub] at this
  nlinarith

/-- `r ≥ π² s`. -/
theorem pi_sq_le : Real.pi ^ 2 * ∫ ω, G 0 ω ^ 2 ∂P ≤ ∫ ω, G' 0 ω ^ 2 ∂P := by
  refine ge_pi_sq_mul_of_forall _ _ fun n hn => ?_
  have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h1 := H.cov_le n hn
  rw [H.cov_zero] at h1
  have h2 := H.cov_lower (h := 1 / (n:ℝ)) (by positivity)
    (by rw [div_le_one hnpos]; exact_mod_cast (by omega : 1 ≤ n))
  set s := ∫ ω, G 0 ω ^ 2 ∂P
  set r := ∫ ω, G' 0 ω ^ 2 ∂P
  set cs := Real.cos (Real.pi / ((n:ℝ) + 1))
  have h3 : s * (1 - cs) ≤ r * (1 / (n:ℝ)) ^ 2 / 2 := by linarith
  have h4 : 2 * (n:ℝ) ^ 2 * (1 - cs) * s = 2 * (n:ℝ) ^ 2 * (s * (1 - cs)) := by ring
  rw [h4]
  calc 2 * (n:ℝ) ^ 2 * (s * (1 - cs)) ≤ 2 * (n:ℝ) ^ 2 * (r * (1 / (n:ℝ)) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = r := by field_simp

end DiagProc

end GMCExplicitDelta.Source
