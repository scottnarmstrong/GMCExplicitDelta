module

public import GMCExplicitDelta.Source.VarianceBound

/-!
# The six terms of the variance lower bound (step S6)
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace GMCExplicitDelta.Source

open MeasureTheory ProbabilityTheory

namespace DiagProc

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {G G' : ℝ → Ω → ℝ} {a b c : Ω → ℝ} (H : DiagProc P G G' a b c)
include H

theorem int_G'G (s t : ℝ) : Integrable (fun ω => G' s ω * G t ω) P :=
  (H.int_GG' t s).congr (Filter.Eventually.of_forall fun ω => mul_comm _ _)

theorem term_a : ∫ ω, G 0 ω ^ 2 ∂P ≤ ∫ ω, a ω ^ 2 ∂P :=
  integral_mono H.int_sq_G0 H.int_sq_a fun ω => by
    rw [← sq_abs (G 0 ω)]
    exact pow_le_pow_left₀ (abs_nonneg _) (H.bG ω 0 ⟨le_rfl, zero_le_one⟩) 2

theorem term_b : ∫ ω, G' 0 ω ^ 2 ∂P ≤ ∫ ω, b ω ^ 2 ∂P :=
  integral_mono H.int_sq_G'0 H.int_sq_b fun ω => by
    rw [← sq_abs (G' 0 ω)]
    exact pow_le_pow_left₀ (abs_nonneg _) (H.bG' ω 0 ⟨le_rfl, zero_le_one⟩) 2

theorem term_ab : ∫ ω, G 0 ω ^ 2 ∂P ≤ ∫ ω, a ω * b ω ∂P := by
  have h1 : ∫ ω, (G 1 ω - G 0 ω) ^ 2 ∂P ≤ ∫ ω, 2 * (a ω * b ω) ∂P :=
    integral_mono (H.int_sq_sub 1) (H.int_ab.const_mul 2) fun ω => by
      have hb : |G 1 ω - G 0 ω| ≤ b ω :=
        abs_sub_le_of_deriv (G := fun s => G s ω) (G' := fun s => G' s ω) (H.hasDeriv ω)
          (H.cont' ω) (fun t ht => H.bG' ω t ht)
      have ha : |G 1 ω - G 0 ω| ≤ 2 * a ω :=
        (abs_sub _ _).trans (by linarith [H.bG ω 1 ⟨zero_le_one, le_rfl⟩, H.bG ω 0 ⟨le_rfl, zero_le_one⟩])
      have := mul_le_mul ha hb (abs_nonneg _) (by linarith [H.a_nonneg ω])
      rw [← sq_abs (G 1 ω - G 0 ω), sq]
      linarith
  rw [H.integral_sq_sub, H.cov_of_one_le le_rfl, integral_const_mul] at h1
  linarith

theorem term_ac : ∫ ω, G' 0 ω ^ 2 ∂P ≤ ∫ ω, a ω * c ω ∂P := by
  obtain ⟨hI, hS⟩ := H.fubini_sq_G' (zero_le_one) le_rfl
  have hint : Integrable (fun ω => ((∫ τ in (0:ℝ)..1, G' τ ω ^ 2) - G 1 ω * G' 1 ω) +
      G 0 ω * G' 0 ω) P := (hI.sub (H.int_GG' 1 1)).add (H.int_GG' 0 0)
  have h1 : ∫ ω, (((∫ τ in (0:ℝ)..1, G' τ ω ^ 2) - G 1 ω * G' 1 ω) + G 0 ω * G' 0 ω) ∂P ≤
      ∫ ω, a ω * c ω ∂P :=
    integral_mono hint H.int_ac fun ω =>
      ibp_bound (G := fun s => G s ω) (G' := fun s => G' s ω) (H.hasDeriv ω) (H.cont' ω)
        (fun t ht => H.bG ω t ht) (fun t ht => H.bG' ω t ht) (H.lip ω)
  have i1 : Integrable (fun ω => (∫ τ in (0:ℝ)..1, G' τ ω ^ 2) - G 1 ω * G' 1 ω) P :=
    hI.sub (H.int_GG' 1 1)
  have i2 : Integrable (fun ω => G 0 ω * G' 0 ω) P := H.int_GG' 0 0
  rw [integral_add i1 i2, integral_sub hI (H.int_GG' 1 1), hS] at h1
  have e1 : ∫ ω, G 1 ω * G' 1 ω ∂P = ∫ ω, G 0 ω * G' 0 ω ∂P := by
    simpa only [zero_add] using H.shift_GG' 0 0 1
  rw [e1] at h1
  linarith

theorem term_bc : (1 + Real.sqrt 2) * ∫ ω, G' 0 ω ^ 2 ∂P ≤ ∫ ω, b ω * c ω ∂P := by
  set R : ℝ → ℝ := fun t => ∫ ω, G' 0 ω * G' t ω ∂P with hR
  set K := ∫ ω, b ω * c ω ∂P with hK
  have hK0 : 0 ≤ K := integral_nonneg fun ω => mul_nonneg (H.b_nonneg ω) (H.c_nonneg ω)
  have hlip : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1, |R s - R t| ≤ K * |s - t| := by
    intro s hs t ht
    have e : R s - R t = ∫ ω, G' 0 ω * (G' s ω - G' t ω) ∂P := by
      simp only [hR]
      rw [← integral_sub (H.int_G'G' 0 s) (H.int_G'G' 0 t)]
      congr 1; ext ω; ring
    rw [e, ← Real.norm_eq_abs]
    calc ‖∫ ω, G' 0 ω * (G' s ω - G' t ω) ∂P‖ ≤ ∫ ω, b ω * c ω * |s - t| ∂P :=
          norm_integral_le_of_norm_le (H.int_bc.mul_const _) (Filter.Eventually.of_forall fun ω => by
            rw [Real.norm_eq_abs, abs_mul]
            have h1 := H.bG' ω 0 ⟨le_rfl, zero_le_one⟩
            have h2 := H.lip ω s hs t ht
            calc |G' 0 ω| * |G' s ω - G' t ω| ≤ b ω * (c ω * |s - t|) :=
                  mul_le_mul h1 h2 (abs_nonneg _) (H.b_nonneg ω)
              _ = b ω * c ω * |s - t| := by ring)
      _ = K * |s - t| := integral_mul_const _ _
  have hcont : ContinuousOn R (Set.Icc 0 1) := by
    refine (LipschitzOnWith.of_dist_le_mul (K := K.toNNReal) fun x hx y hy => ?_).continuousOn
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal K hK0]
    exact hlip x hx y hy
  have h0 : R 0 = ∫ ω, G' 0 ω ^ 2 ∂P :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => (sq _).symm)
  have h1 : R 1 = 0 := H.indep_G'0_G'1
  have hint : ∫ t in (0:ℝ)..1, R t = 0 := by
    have hmeas : Measurable (Function.uncurry fun (τ : ℝ) (ω : Ω) => G' 0 ω * G' τ ω) :=
      measurable_uncurry_of_continuous_of_measurable
        (fun ω => continuous_const.mul (H.cont' ω)) (fun τ => (H.mG' 0).mul (H.mG' τ))
    obtain ⟨_, hS⟩ := integral_intervalIntegral_swap (P := P) hmeas zero_le_one
      (B := fun ω => b ω * b ω) (H.int_sq_b.congr (Filter.Eventually.of_forall fun ω => sq _))
      (fun ω t ht => by
        rw [abs_mul]
        exact mul_le_mul (H.bG' ω 0 ⟨le_rfl, zero_le_one⟩) (H.bG' ω t ht) (abs_nonneg _) (H.b_nonneg ω))
    have hin : ∀ ω, ∫ τ in (0:ℝ)..1, G' 0 ω * G' τ ω = G' 0 ω * (G 1 ω - G 0 ω) := fun ω => by
      rw [intervalIntegral.integral_const_mul]
      congr 1
      exact ftc_diag (G := fun s => G s ω) (G' := fun s => G' s ω) (H.hasDeriv ω) (H.cont' ω) 0 1
    show ∫ t in (0:ℝ)..1, (∫ ω, G' 0 ω * G' t ω ∂P) = 0
    rw [hS]
    simp_rw [hin]
    have e : ∀ ω, G' 0 ω * (G 1 ω - G 0 ω) = G' 0 ω * G 1 ω - G 0 ω * G' 0 ω := fun ω => by ring
    simp_rw [e]
    rw [integral_sub (H.int_G'G 0 1) (H.int_GG' 0 0), H.indep_G'0_G1, H.cross_zero]; simp
  exact envelope_lower (integral_nonneg fun ω => sq_nonneg _) hcont hlip h0 h1 hint

theorem term_c : 32 * ∫ ω, G 0 ω ^ 2 ∂P + 8 * ∫ ω, G' 0 ω ^ 2 ∂P ≤ ∫ ω, c ω ^ 2 ∂P := by
  set s := ∫ ω, G 0 ω ^ 2 ∂P with hs
  set r := ∫ ω, G' 0 ω ^ 2 ∂P with hr
  set f : Fin 4 → Ω → ℝ := ![G 0, G 1, G' 0, G' 1] with hf
  set x : Fin 4 → ℝ := ![-1, 1, -1 / 2, -1 / 2] with hx
  have hi : ∀ i j, Integrable (fun ω => f i ω * f j ω) P := by
    intro i j; fin_cases i <;> fin_cases j <;> simp only [hf] <;> simp
    all_goals first
      | exact H.int_GG _ _ | exact H.int_GG' _ _ | exact H.int_G'G _ _ | exact H.int_G'G' _ _
  have e00 : ∫ ω, G 0 ω * G 0 ω ∂P = s := by simp [hs, sq]
  have e11 : ∫ ω, G 1 ω * G 1 ω ∂P = s := by simp only [← sq]; rw [H.integral_sq_G 1]
  have e22 : ∫ ω, G' 0 ω * G' 0 ω ∂P = r := by simp [hr, sq]
  have e33 : ∫ ω, G' 1 ω * G' 1 ω ∂P = r := by simp only [← sq]; rw [H.integral_sq_G' 1]
  have comm : ∀ u v : Ω → ℝ, ∫ ω, u ω * v ω ∂P = ∫ ω, v ω * u ω ∂P := fun u v =>
    integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)
  have z01 : ∫ ω, G 0 ω * G 1 ω ∂P = 0 := by
    have := H.cov_of_one_le (le_refl (1:ℝ)); exact this
  have z10 : ∫ ω, G 1 ω * G 0 ω ∂P = 0 := by
    exact (comm _ _).trans z01
  have z02 : ∫ ω, G 0 ω * G' 0 ω ∂P = 0 := H.cross_zero
  have z20 : ∫ ω, G' 0 ω * G 0 ω ∂P = 0 := by
    exact (comm _ _).trans z02
  have z03 : ∫ ω, G 0 ω * G' 1 ω ∂P = 0 := H.indep_G0_G'1
  have z30 : ∫ ω, G' 1 ω * G 0 ω ∂P = 0 := by
    exact (comm _ _).trans z03
  have z12 : ∫ ω, G 1 ω * G' 0 ω ∂P = 0 := by
    exact (comm _ _).trans H.indep_G'0_G1
  have z21 : ∫ ω, G' 0 ω * G 1 ω ∂P = 0 := H.indep_G'0_G1
  have z13 : ∫ ω, G 1 ω * G' 1 ω ∂P = 0 := by
    have : ∫ ω, G 1 ω * G' 1 ω ∂P = ∫ ω, G 0 ω * G' 0 ω ∂P := by
      simpa only [zero_add] using H.shift_GG' 0 0 1
    rw [this]; exact H.cross_zero
  have z31 : ∫ ω, G' 1 ω * G 1 ω ∂P = 0 := by
    exact (comm _ _).trans z13
  have z23 : ∫ ω, G' 0 ω * G' 1 ω ∂P = 0 := H.indep_G'0_G'1
  have z32 : ∫ ω, G' 1 ω * G' 0 ω ∂P = 0 := by
    exact (comm _ _).trans z23
  have hq := integral_sq_sum (P := P) hi x
  have hT : ∀ ω, (∑ i, x i * f i ω) ^ 2 = (G 1 ω - G 0 ω - (G' 0 ω + G' 1 ω) / 2) ^ 2 := fun ω => by
    simp [Fin.sum_univ_four, hf, hx]; ring
  have hET : ∫ ω, (G 1 ω - G 0 ω - (G' 0 ω + G' 1 ω) / 2) ^ 2 ∂P = 2 * s + r / 2 := by
    simp_rw [← hT]
    rw [hq]
    simp [Fin.sum_univ_four, hf, hx, e00, e11, e22, e33, z01, z10, z02, z20, z03, z30, z12, z21,
      z13, z31, z23, z32]
    ring
  have hTi : Integrable (fun ω => (G 1 ω - G 0 ω - (G' 0 ω + G' 1 ω) / 2) ^ 2) P := by
    have := integrable_sq_sum (P := P) hi x
    simpa only [hT] using this
  have h1 : ∫ ω, 16 * (G 1 ω - G 0 ω - (G' 0 ω + G' 1 ω) / 2) ^ 2 ∂P ≤ ∫ ω, c ω ^ 2 ∂P :=
    integral_mono (hTi.const_mul 16) H.int_sq_c fun ω => by
      have h := trapezoid_bound (G := fun s => G s ω) (G' := fun s => G' s ω) (H.hasDeriv ω)
        (H.cont' ω) (fun t ht => H.bG' ω t ht) (H.lip ω)
      have h2 : (G 1 ω - G 0 ω - (G' 0 ω + G' 1 ω) / 2) ^ 2 ≤ (c ω / 4) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) h 2
      nlinarith
  rw [integral_const_mul, hET] at h1
  linarith

/-- The six-term lower bound `E (a+b+c)² ≥ 35 s + (13 + 2√2) r`. -/
theorem variance_lower :
    35 * ∫ ω, G 0 ω ^ 2 ∂P + (13 + 2 * Real.sqrt 2) * ∫ ω, G' 0 ω ^ 2 ∂P ≤
      ∫ ω, (a ω + b ω + c ω) ^ 2 ∂P := by
  set f : Fin 3 → Ω → ℝ := ![a, b, c] with hf
  have hi : ∀ i j, Integrable (fun ω => f i ω * f j ω) P := by
    intro i j; fin_cases i <;> fin_cases j <;> simp only [hf] <;> simp
    all_goals first
      | exact H.int_ab | exact H.int_ac | exact H.int_bc
      | exact H.int_sq_a.congr (Filter.Eventually.of_forall fun ω => sq _)
      | exact H.int_sq_b.congr (Filter.Eventually.of_forall fun ω => sq _)
      | exact H.int_sq_c.congr (Filter.Eventually.of_forall fun ω => sq _)
      | exact (H.int_ab).congr (Filter.Eventually.of_forall fun ω => mul_comm _ _)
      | exact (H.int_ac).congr (Filter.Eventually.of_forall fun ω => mul_comm _ _)
      | exact (H.int_bc).congr (Filter.Eventually.of_forall fun ω => mul_comm _ _)
  have hq := integral_sq_sum (P := P) hi (fun _ => (1:ℝ))
  have hT : ∀ ω, (∑ i, (fun _ : Fin 3 => (1:ℝ)) i * f i ω) ^ 2 = (a ω + b ω + c ω) ^ 2 := fun ω => by
    simp [Fin.sum_univ_three, hf]
  simp_rw [hT] at hq
  rw [hq]
  have caa : ∫ ω, a ω * a ω ∂P = ∫ ω, a ω ^ 2 ∂P := by simp [sq]
  have cbb : ∫ ω, b ω * b ω ∂P = ∫ ω, b ω ^ 2 ∂P := by simp [sq]
  have ccc : ∫ ω, c ω * c ω ∂P = ∫ ω, c ω ^ 2 ∂P := by simp [sq]
  have cba : ∫ ω, b ω * a ω ∂P = ∫ ω, a ω * b ω ∂P :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)
  have cca : ∫ ω, c ω * a ω ∂P = ∫ ω, a ω * c ω ∂P :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)
  have ccb : ∫ ω, c ω * b ω ∂P = ∫ ω, b ω * c ω ∂P :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)
  simp [Fin.sum_univ_three, hf, caa, cbb, ccc, cba, cca, ccb]
  have ta := H.term_a
  have tb := H.term_b
  have tab := H.term_ab
  have tac := H.term_ac
  have tbc := H.term_bc
  have tc := H.term_c
  have hr : 0 ≤ ∫ ω, G' 0 ω ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
  nlinarith

end DiagProc

end GMCExplicitDelta.Source
