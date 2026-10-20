module

public import GMCExplicitDelta.Proofs.Scaling.Band
public import GMCExplicitDelta.Coarse.Phi

/-!
# R4(g), I10: fresh returns and seeds at smaller disorder

Proof of `freshReturns_scale_le` (statement copied from `Targets/AssemblyScaling.lean`).
-/

@[expose] public section

open Real

namespace GMCExplicitDelta.Assembly

open Contract

variable {d : ℕ}

theorem exp_mul_le_one_add {l t : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    Real.exp (l * t) ≤ 1 + l * (Real.exp t - 1) := by
  have h := convexOn_exp.2 (Set.mem_univ t) (Set.mem_univ 0) hl0 (by linarith : 0 ≤ 1 - l)
    (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero] at h
  linarith

theorem rpow32_scale_le {l X Y : ℝ} (hl : 0 ≤ l) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (h : Y ≤ l ^ 32 * X) : Y ^ ((1 : ℝ) / 32) ≤ l * X ^ ((1 : ℝ) / 32) := by
  calc Y ^ ((1 : ℝ) / 32) ≤ (l ^ 32 * X) ^ ((1 : ℝ) / 32) :=
        Real.rpow_le_rpow hY h (by norm_num)
    _ = l * X ^ ((1 : ℝ) / 32) := by
        rw [Real.mul_rpow (by positivity) hX]
        congr 1
        rw [← Real.rpow_natCast, ← Real.rpow_mul hl]
        norm_num

theorem sigmaNorm_nonneg (d : ℕ) : (0 : ℝ) ≤ (sigmaNorm d : ℝ) := by
  unfold sigmaNorm; split_ifs <;> norm_num

theorem nativeCap_nonneg (d k : ℕ) {D F : ℝ} (hD : 0 ≤ D) (hF : 0 ≤ F) :
    0 ≤ nativeCap d k D F := by
  unfold nativeCap
  refine le_min hD ?_
  have h1 : 0 ≤ Bbar32 (3 ^ (d * (k - 1))) D F := rpow_one_div_32_nonneg _
  have := sigmaNorm_nonneg d
  positivity

theorem sphereFactorPow_nonneg (d : ℕ) : (0 : ℝ) ≤ (sphereFactorPow d : ℝ) := by
  unfold sphereFactorPow
  have : (0 : ℚ) ≤ (Nat.choose 64 32 : ℚ) := Nat.cast_nonneg _
  split_ifs <;> push_cast <;> positivity

section Row

variable (row : Row d)

theorem Fnext_nonneg (hO : row.Obligations) (F : ℝ) (hF : 0 ≤ F) : 0 ≤ row.Fnext F := by
  have hZ : (0 : ℚ) < row.Z := hO.bar1.1
  unfold Row.Fnext Row.tStar
  have : (0 : ℝ) ≤ (row.Z : ℝ) := by exact_mod_cast hZ.le
  positivity

theorem profile_nonneg (hO : row.Obligations) {D F : ℝ} (hD : 0 ≤ D) (hF : 0 ≤ F) (r : ℕ) :
    0 ≤ row.profile D F r := by
  unfold Row.profile
  split_ifs
  · exact zero_le_one
  · have h1 := Fnext_nonneg row hO F hF
    have h2 : 0 ≤ row.Dnext D F := nativeCap_nonneg d _ hD hF
    exact mul_nonneg (Real.rpow_nonneg h1 _) (Real.rpow_nonneg h2 _)

theorem profile_smul (hO : row.Obligations) {l D F : ℝ} (hl : 0 < l) (hD : 0 ≤ D) (hF : 0 ≤ F)
    (r : ℕ) : row.profile (l * D) (l * F) r = l ^ r * row.profile D F r := by
  unfold Row.profile
  by_cases hr : r = 0
  · simp [hr]
  · rw [if_neg hr, if_neg hr, Fnext_smul, Dnext_smul row hl]
    have h1 := Fnext_nonneg row hO F hF
    have h2 : 0 ≤ row.Dnext D F := nativeCap_nonneg d _ hD hF
    rw [Real.mul_rpow hl.le h1, Real.mul_rpow hl.le h2]
    have : l ^ ((32 - (r : ℝ)) / 31) * l ^ (32 * ((r : ℝ) - 1) / 31) = l ^ r := by
      rw [← Real.rpow_add hl, ← Real.rpow_natCast]
      congr 1; ring
    calc l ^ ((32 - (r : ℝ)) / 31) * row.Fnext F ^ ((32 - (r : ℝ)) / 31) *
          (l ^ (32 * ((r : ℝ) - 1) / 31) * row.Dnext D F ^ (32 * ((r : ℝ) - 1) / 31))
        = (l ^ ((32 - (r : ℝ)) / 31) * l ^ (32 * ((r : ℝ) - 1) / 31)) *
          (row.Fnext F ^ ((32 - (r : ℝ)) / 31) * row.Dnext D F ^ (32 * ((r : ℝ) - 1) / 31)) := by
          ring
      _ = _ := by rw [this]

theorem delta_sq {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ (row.deltaStar : ℝ)) :
    δ ^ 2 = lamOf row δ * (row.deltaStar : ℝ) ^ 2 := by
  have : (row.deltaStar : ℝ) ≠ 0 := (hδ0.trans_le hδ).ne'
  unfold lamOf; field_simp

theorem freshMoment_le (hO : row.Obligations) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ ≤ (row.deltaStar : ℝ)) :
    row.freshMoment δ (lamOf row δ * row.D) (lamOf row δ * row.F) ≤
      lamOf row δ ^ 32 * row.freshMoment row.deltaStar row.D row.F := by
  have hl := lamOf_pos row hδ0 hδ
  have hl1 := lamOf_le_one row hδ0 hδ
  have hD : (0 : ℝ) ≤ row.D := by exact_mod_cast hO.par1.1.le
  have hF : (0 : ℝ) ≤ row.F := by exact_mod_cast hO.par1.2.1.le
  unfold Row.freshMoment
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun r _ => ?_
  rw [profile_smul row hO hl hD hF]
  have h1 := bandRow_le hl.le hl1 (delta_sq row hδ0 hδ) row.h r
  have h2 := profile_nonneg row hO hD hF r
  have hr : (r : ℕ) ≤ 32 := by omega
  calc bandRow δ row.h r * (lamOf row δ ^ (r : ℕ) * row.profile row.D row.F r)
      ≤ (lamOf row δ ^ (32 - (r : ℕ)) * bandRow (row.deltaStar : ℝ) row.h r) *
          (lamOf row δ ^ (r : ℕ) * row.profile row.D row.F r) :=
        mul_le_mul_of_nonneg_right h1 (mul_nonneg (pow_nonneg hl.le _) h2)
    _ = lamOf row δ ^ 32 * (bandRow (row.deltaStar : ℝ) row.h r * row.profile row.D row.F r) := by
        have : (32 : ℕ) = (32 - (r : ℕ)) + (r : ℕ) := by omega
        conv_rhs => rw [this, pow_add]
        ring

theorem gammaH_scale {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ (row.deltaStar : ℝ)) :
    row.gammaH δ = lamOf row δ * row.gammaH row.deltaStar := by
  unfold Row.gammaH
  rw [delta_sq row hδ0 hδ]; ring

theorem gammaH_nonneg (δ : ℝ) : 0 ≤ row.gammaH δ := by
  unfold Row.gammaH kappaQ1
  positivity

theorem sym_le (hO : row.Obligations) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ (row.deltaStar : ℝ)) :
    row.sym δ (lamOf row δ * row.D) (lamOf row δ * row.F) ≤
      lamOf row δ * row.sym row.deltaStar row.D row.F := by
  have hl := lamOf_pos row hδ0 hδ
  have hD : (0 : ℝ) ≤ row.D := by exact_mod_cast hO.par1.1.le
  have hF : (0 : ℝ) ≤ row.F := by exact_mod_cast hO.par1.2.1.le
  have hM : ∀ δ' D' F' : ℝ, 0 ≤ D' → 0 ≤ F' → 0 ≤ row.freshMoment δ' D' F' := by
    intro δ' D' F' hD' hF'
    exact Finset.sum_nonneg fun r _ => mul_nonneg (bandRow_nonneg _ _ _)
      (profile_nonneg row hO hD' hF' _)
  have hb := sphereFactorPow_nonneg d
  unfold Row.sym
  refine rpow32_scale_le hl.le (mul_nonneg hb (hM _ _ _ hD hF))
    (mul_nonneg hb (hM _ _ _ (by positivity) (by positivity))) ?_
  calc (sphereFactorPow d : ℝ) * row.freshMoment δ (lamOf row δ * row.D) (lamOf row δ * row.F)
      ≤ (sphereFactorPow d : ℝ) * (lamOf row δ ^ 32 * row.freshMoment row.deltaStar row.D row.F) :=
        mul_le_mul_of_nonneg_left (freshMoment_le row hO hδ0 hδ) hb
    _ = _ := by ring

theorem post_le (hO : row.Obligations) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ (row.deltaStar : ℝ)) :
    row.post δ (lamOf row δ * row.D) (lamOf row δ * row.F) ≤
      lamOf row δ * row.post row.deltaStar row.D row.F := by
  have hl := lamOf_pos row hδ0 hδ
  have hl1 := lamOf_le_one row hδ0 hδ
  have hs := sym_le row hO hδ0 hδ
  unfold Row.post
  split_ifs
  · exact hs
  · have hsn := sym_nonneg row row.deltaStar row.D row.F
    have h1 : PhiMap (row.gammaH δ) (row.sym δ (lamOf row δ * row.D) (lamOf row δ * row.F)) ≤
        PhiMap (row.gammaH δ) (lamOf row δ * row.sym row.deltaStar row.D row.F) :=
      Coarse.phi_mono_j (gammaH_nonneg row δ) (sym_nonneg row _ _ _)
        (mul_nonneg hl.le hsn) hs
    have h2 := Coarse.phi_scale hl.le hl1 (gammaH_nonneg row row.deltaStar) hsn
    rw [← gammaH_scale row hδ0 hδ] at h2
    exact h1.trans h2

theorem meanpost_le (hO : row.Obligations) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ (row.deltaStar : ℝ)) :
    row.meanpost δ (lamOf row δ * row.F) ≤ lamOf row δ * row.meanpost row.deltaStar row.F := by
  have hl := lamOf_pos row hδ0 hδ
  have hl1 := lamOf_le_one row hδ0 hδ
  have hF : (0 : ℝ) ≤ row.F := by exact_mod_cast hO.par1.2.1.le
  have hf := Fnext_nonneg row hO _ hF
  set l := lamOf row δ with hldef
  set f := row.Fnext row.F with hfdef
  set γ := row.gammaH row.deltaStar with hγdef
  have hγ0 := gammaH_nonneg row row.deltaStar
  have hg := gammaH_scale row hδ0 hδ
  rw [← hldef] at hg
  unfold Row.meanpost
  rw [Fnext_smul, hg]
  split_ifs
  · have he := exp_mul_le_one_add (t := γ) hl.le hl1
    have hE : 1 ≤ Real.exp γ := Real.one_le_exp hγ0
    have h1 : Real.exp (l * γ) * (1 + l * f) ≤ (1 + l * (Real.exp γ - 1)) * (1 + l * f) :=
      mul_le_mul_of_nonneg_right he (by positivity)
    have h2 : l * l * ((Real.exp γ - 1) * f) ≤ l * ((Real.exp γ - 1) * f) := by
      have hx := mul_nonneg (by linarith : 0 ≤ Real.exp γ - 1) hf
      nlinarith [mul_nonneg (mul_nonneg hl.le (sub_nonneg.2 hl1)) hx]
    nlinarith
  · have he := exp_mul_le_one_add (t := 2 * γ) hl.le hl1
    have hE : 1 ≤ Real.exp (2 * γ) := Real.one_le_exp (by linarith)
    have e1 : Real.exp (2 * (l * γ)) = Real.exp (l * (2 * γ)) := by ring_nf
    rw [e1]
    have h1 : Real.exp (l * (2 * γ)) ≤ Real.exp (2 * γ) := by
      nlinarith
    have h2 : Real.exp (l * (2 * γ)) * (l * f) ≤ Real.exp (2 * γ) * (l * f) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    nlinarith

theorem meanseed_le {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ (row.deltaStar : ℝ)) :
    row.meanseed δ ≤ lamOf row δ * row.meanseed row.deltaStar := by
  have hl := lamOf_pos row hδ0 hδ
  have hl1 := lamOf_le_one row hδ0 hδ
  have hγ0 := gammaH_nonneg row row.deltaStar
  have hg := gammaH_scale row hδ0 hδ
  unfold Row.meanseed
  rw [hg]
  split_ifs
  · have := exp_mul_le_one_add (t := row.gammaH row.deltaStar) hl.le hl1
    linarith
  · have := exp_mul_le_one_add (t := 2 * row.gammaH row.deltaStar) hl.le hl1
    have e1 : Real.exp (2 * (lamOf row δ * row.gammaH row.deltaStar)) =
        Real.exp (lamOf row δ * (2 * row.gammaH row.deltaStar)) := by ring_nf
    rw [e1]
    linarith

theorem seed_le (hO : row.Obligations) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ (row.deltaStar : ℝ)) :
    row.seed δ ≤ lamOf row δ * row.seed row.deltaStar := by
  have hl := lamOf_pos row hδ0 hδ
  have hl1 := lamOf_le_one row hδ0 hδ
  have hx0 : ∀ δ', 0 ≤ row.seedPoint δ' := by
    intro δ'
    unfold Row.seedPoint
    split_ifs
    · exact le_rfl
    · linarith [Real.one_le_cosh (row.gammaH δ')]
  have hxle : row.seedPoint δ ≤ lamOf row δ * row.seedPoint row.deltaStar := by
    unfold Row.seedPoint
    split_ifs
    · simp
    · rw [gammaH_scale row hδ0 hδ]
      exact Coarse.cosh_mul_sub_one_le hl.le hl1
  have hS : ∀ δ', 0 ≤ ∑ r : Fin 33, bandRow δ' row.h r * row.seedPoint δ ^ (r : ℕ) := fun δ' =>
    Finset.sum_nonneg fun r _ => mul_nonneg (bandRow_nonneg _ _ _) (pow_nonneg (hx0 _) _)
  unfold Row.seed
  refine rpow32_scale_le hl.le (Finset.sum_nonneg fun r _ =>
    mul_nonneg (bandRow_nonneg _ _ _) (pow_nonneg (hx0 _) _))
    (Finset.sum_nonneg fun r _ => mul_nonneg (bandRow_nonneg _ _ _) (pow_nonneg (hx0 _) _)) ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun r _ => ?_
  have h1 := bandRow_le hl.le hl1 (delta_sq row hδ0 hδ) row.h r
  have h3 : row.seedPoint δ ^ (r : ℕ) ≤ (lamOf row δ * row.seedPoint row.deltaStar) ^ (r : ℕ) :=
    pow_le_pow_left₀ (hx0 _) hxle _
  have hq := bandRow_nonneg (row.deltaStar : ℝ) row.h r
  have hxs := pow_nonneg (hx0 row.deltaStar) (r : ℕ)
  calc bandRow δ row.h r * row.seedPoint δ ^ (r : ℕ)
      ≤ (lamOf row δ ^ (32 - (r : ℕ)) * bandRow (row.deltaStar : ℝ) row.h r) *
          (lamOf row δ * row.seedPoint row.deltaStar) ^ (r : ℕ) :=
        mul_le_mul h1 h3 (pow_nonneg (hx0 _) _)
          (mul_nonneg (pow_nonneg hl.le _) hq)
    _ = lamOf row δ ^ 32 * (bandRow (row.deltaStar : ℝ) row.h r *
          row.seedPoint row.deltaStar ^ (r : ℕ)) := by
        have : (32 : ℕ) = (32 - (r : ℕ)) + (r : ℕ) := by omega
        conv_rhs => rw [this, pow_add]
        rw [mul_pow]; ring

end Row

end GMCExplicitDelta.Assembly

namespace GMCExplicitDelta.Assembly

open Contract

/-- **R4(g) and I10 (fresh returns and seeds at smaller disorder).** -/
theorem freshReturns_scale_le_proof {d : ℕ} (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ))
    (hO : row.Obligations) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ (row.deltaStar : ℝ)) :
    row.post δ (lamOf row δ * row.D) (lamOf row δ * row.F) ≤
        lamOf row δ * row.post row.deltaStar row.D row.F ∧
      row.meanpost δ (lamOf row δ * row.F) ≤ lamOf row δ * row.meanpost row.deltaStar row.F ∧
      row.seed δ ≤ lamOf row δ * row.seed row.deltaStar ∧
      row.meanseed δ ≤ lamOf row δ * row.meanseed row.deltaStar :=
  ⟨post_le row hO hδ0 hδ, meanpost_le row hO hδ0 hδ, seed_le row hO hδ0 hδ,
    meanseed_le row hδ0 hδ⟩

end GMCExplicitDelta.Assembly
