module

public import GMCExplicitDelta.Assembly.ModelInduction

/-!
# Assembly: the elementary λ-scaling facts of R4

The parts of R4 that are immediate from the definitions of the contract constants: `z_F` is
nondecreasing in `δ` (R4(b)); `ϖ`, hence `B̄₃₂` and `𝔲_ℓ`, are invariant under `(D, F) ↦ (λD, λF)`
(R4(c)); the native caps `U_k`, hence `D_next = U_h`, and `F_next = t_⋆F` are linear (R4(g)); the
disorder ratio `λ = (δ/δ_*)²` lies in `(0, 1]` with `λδ_*² = δ²`. Also `Φ_0(y) = y` and the
nonnegativity of real `32`nd roots (`sym ≥ 0`), used in I9.
-/

@[expose] public section

open Real

namespace GMCExplicitDelta.Assembly

open Contract

variable {d : ℕ}

theorem proxyA_pos : (0 : ℝ) < (proxyA : ℝ) := by
  unfold proxyA; norm_num

theorem kappaH_nonneg (d : ℕ) : 0 ≤ kappaH d := by
  unfold kappaH kappaQ1
  split_ifs
  · exact le_rfl
  · norm_num

/-- R4(b): `z_F` is nondecreasing in `δ > 0`. -/
theorem zF_le_of_le (row : Row d) {δ δ' : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ δ') :
    row.zF δ ≤ row.zF δ' := by
  unfold Row.zF
  have hx : 0 ≤ row.xHist := by unfold Row.xHist; positivity
  have hc : 0 ≤ 128 * (proxyA : ℝ) + 2 * kappaH d := by
    have := proxyA_pos; have := kappaH_nonneg d; positivity
  have hsq : δ ^ 2 ≤ δ' ^ 2 := pow_le_pow_left₀ hδ0.le hδ 2
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsq hc)) hx

theorem varpi_smul {lam : ℝ} (hlam : 0 < lam) (D F : ℝ) :
    varpi (lam * D) (lam * F) = varpi D F := by
  unfold varpi
  rw [mul_div_mul_left _ _ hlam.ne']

theorem Bbar32_smul {lam : ℝ} (hlam : 0 < lam) (n : ℕ) (D F : ℝ) :
    Bbar32 n (lam * D) (lam * F) = Bbar32 n D F := by
  unfold Bbar32 Tvarpi
  rw [varpi_smul hlam]

/-- R4(c): `𝔲_ℓ` does not depend on `λ`. -/
theorem frakU_smul {lam : ℝ} (hlam : 0 < lam) (d ℓ : ℕ) (D F : ℝ) :
    frakU d ℓ (lam * D) (lam * F) = frakU d ℓ D F := by
  unfold frakU
  rw [Bbar32_smul hlam]

/-- R4(g): the native caps are linear in `(D, F)` at fixed `F/D`. -/
theorem nativeCap_smul {lam : ℝ} (hlam : 0 < lam) (d k : ℕ) (D F : ℝ) :
    nativeCap d k (lam * D) (lam * F) = lam * nativeCap d k D F := by
  unfold nativeCap
  rw [Bbar32_smul hlam, mul_min_of_nonneg _ _ hlam.le]
  congr 1
  ring

theorem Dnext_smul (row : Row d) {lam : ℝ} (hlam : 0 < lam) (D F : ℝ) :
    row.Dnext (lam * D) (lam * F) = lam * row.Dnext D F :=
  nativeCap_smul hlam d row.h D F

theorem Fnext_smul (row : Row d) (lam F : ℝ) : row.Fnext (lam * F) = lam * row.Fnext F := by
  unfold Row.Fnext; ring

theorem lamOf_pos (row : Row d) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ (row.deltaStar : ℝ)) :
    0 < lamOf row δ := by
  have : 0 < (row.deltaStar : ℝ) := hδ0.trans_le hδ
  unfold lamOf; positivity

theorem lamOf_le_one (row : Row d) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ (row.deltaStar : ℝ)) :
    lamOf row δ ≤ 1 := by
  have hs : 0 < (row.deltaStar : ℝ) := hδ0.trans_le hδ
  unfold lamOf
  have h1 : δ / (row.deltaStar : ℝ) ≤ 1 := (div_le_one hs).mpr hδ
  have h0 : 0 ≤ δ / (row.deltaStar : ℝ) := by positivity
  nlinarith

/-- `λD = (D/δ_*²)δ²`, the form of the caps in the cascade conclusion. -/
theorem lamOf_mul (row : Row d) (δ X : ℝ) :
    lamOf row δ * X = X / (row.deltaStar : ℝ) ^ 2 * δ ^ 2 := by
  unfold lamOf; ring

/-- `Φ_0(y) = y`. -/
theorem PhiMap_zero (y : ℝ) : PhiMap 0 y = y := by
  simp [PhiMap]

/-- Real `32`nd roots are nonnegative (for a negative base, `x^{1/32} = e^{(log x)/32} cos(π/32)`). -/
theorem rpow_one_div_32_nonneg (x : ℝ) : 0 ≤ x ^ ((1 : ℝ) / 32) := by
  rcases lt_or_ge x 0 with hx | hx
  · rw [Real.rpow_def_of_neg hx]
    refine mul_nonneg (Real.exp_pos _).le (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩).le
    · have := Real.pi_pos; nlinarith
    · have := Real.pi_pos; nlinarith
  · exact Real.rpow_nonneg hx _

theorem sym_nonneg (row : Row d) (δ D F : ℝ) : 0 ≤ row.sym δ D F :=
  rpow_one_div_32_nonneg _

end GMCExplicitDelta.Assembly
