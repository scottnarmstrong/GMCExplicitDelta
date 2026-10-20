module

public import GMCExplicitDelta.Assembly.ModelEvents
public import GMCExplicitDelta.Assembly.Scaling
public import GMCExplicitDelta.Coarse.Order
public import SubdiffusiveProcess.Providers.Section5.ReciprocalLower

/-!
# G9, deterministic part: the matched pairs, the cell as a cube, the caps, `e_⋆ ≥ 0`

G9, with C3, C7 and the monotonicity of `U_k` (A6).

* `frozenJ_planar_le`, `frozenJ_recip_le` (C3 + C7): pointwise,
  `J(U,(1+μ)e,e;b_L) ≤ 𝗋(μ) Φ_{log(1+2F)}(J^max(U))` for `μ ∈ [0,F]` and
  `J(U,√β e,e/√β;b_L) ≤ Φ_{log(1+2F)}(J^max(U))` for `β ∈ [1,1+2F]` (when `J^max(U) < ∞`).
* `cellAt_eq_cubeAt`: a depth-`ν` cell `z + R` of `z + Q_m` is the cube `z' + Q_{m-ν}`.
* `nativeCap_anti`: `k ↦ U_k` is nonincreasing on `k ≥ 1`.
* `eStar_nonneg`: `e_⋆ ≥ 0` at any `δ > 0` with `z_F(δ) < 1`, given `ε_sub ≥ 0` (the sign of `ε_sub`
  is not recorded in `Row.Obligations`; for `d ≥ 3` it enters `U_grid` through `1 + ε_sub⁻¹`).
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta.Assembly.BadResponse

open Contract

variable {d : ℕ}

theorem ahom_pos (M : SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) : 0 < ahom M m :=
  (Real.exp_pos _).trans_le
    (SubdiffusiveProcess.Providers.Section5.homogenized_coefficient_reciprocal_lower M m)

/-- The contract's `Φ` is `Coarse.phi`. -/
theorem PhiMap_eq_phi (t j : ℝ) : PhiMap t j = Coarse.phi t j := rfl

/-! ### C3 + C7 for the matched pairs -/

section Det

variable {U : Ch02.Domain d} {a : Ch02.CoeffOn U} (ha : Ch02.CoeffOn.IsSymmetric a)
include ha

theorem responseJ_smul_smul {e : Homogenization.Vec d} (he : e ⬝ᵥ e = 1) (u v : ℝ) :
    Ch02.responseJ U a (u • e) (v • e) =
      (1 / 2) * u ^ 2 * Coarse.qf (Coarse.XU U a) e +
        (1 / 2) * v ^ 2 * Coarse.qf (Coarse.YU U a) e - u * v := by
  rw [Coarse.responseJ_eq_XY ha, Coarse.posDef_qf_smul, Coarse.posDef_qf_smul, smul_dotProduct,
    dotProduct_smul, he, smul_eq_mul, smul_eq_mul]
  ring

theorem one_le_qf_mul {e : Homogenization.Vec d} (he : e ⬝ᵥ e = 1) :
    1 ≤ Coarse.qf (Coarse.XU U a) e * Coarse.qf (Coarse.YU U a) e := by
  have he0 : e ≠ 0 := by rintro rfl; simp at he
  have hα := Coarse.posDef_qf_pos (Coarse.XU_posDef ha) he0
  have h1 := Coarse.posDef_sq_dot_le (Coarse.XU_posDef ha) e
  have h2 := (Coarse.matLoewnerLE_iff_qf.mp (Coarse.XU_inv_le_YU ha)) e
  rw [he] at h1
  nlinarith

/-- C7 for a rescaled pair `(u e, v e)` with `uv = 1`, `u² = λ`, at the normalization `σ²`:
`J(U, σ⁻¹ue, σve; a) ≤ Φ_{|log λ|}(J(U, σ⁻¹e, σe; a))`. -/
theorem responseJ_pair_le {e : Homogenization.Vec d} (he : e ⬝ᵥ e = 1) {σ lam u v : ℝ}
    (hσ : 0 < σ) (hlam : 0 < lam) (huv : u * v = 1) (hu : u ^ 2 = lam) :
    Ch02.responseJ U a (σ⁻¹ • (u • e)) (σ • (v • e)) ≤
      Coarse.phi |Real.log lam| (Ch02.responseJ U a (σ⁻¹ • e) (σ • e)) := by
  set x := Coarse.qf (Coarse.XU U a) e with hx
  set y := Coarse.qf (Coarse.YU U a) e with hy
  have hxy : 1 ≤ x * y := one_le_qf_mul ha he
  have hσ0 : σ ≠ 0 := hσ.ne'
  have hu0 : u ≠ 0 := by rintro rfl; simp at huv
  have hv : v = u⁻¹ := eq_inv_of_mul_eq_one_right huv
  have hαβ : 1 ≤ (σ⁻¹ ^ 2 * x) * (σ ^ 2 * y) := by
    have e0 : (σ⁻¹ ^ 2 * x) * (σ ^ 2 * y) = x * y := by field_simp
    rw [e0]; exact hxy
  have h := Coarse.half_exp_le_phi hαβ (Real.log lam)
  rw [Real.exp_log hlam, Real.exp_neg, Real.exp_log hlam] at h
  rw [smul_smul, smul_smul, responseJ_smul_smul ha he, responseJ_smul_smul ha he]
  have e1 : (1 / 2) * (σ⁻¹ * u) ^ 2 * x + (1 / 2) * (σ * v) ^ 2 * y - σ⁻¹ * u * (σ * v) =
      (1 / 2) * (lam * (σ⁻¹ ^ 2 * x) + lam⁻¹ * (σ ^ 2 * y)) - 1 := by
    rw [hv, ← hu]
    field_simp
  have e2 : (1 / 2) * σ⁻¹ ^ 2 * x + (1 / 2) * σ ^ 2 * y - σ⁻¹ * σ =
      (σ⁻¹ ^ 2 * x + σ ^ 2 * y) / 2 - 1 := by
    field_simp
  rw [e1, e2]
  exact h

/-- C3 + C7 for the planar pair `(λe, e)`:
`J(U, σ⁻¹λe, σe; a) ≤ λ Φ_{|log λ|}(J(U, σ⁻¹e, σe; a))`. -/
theorem responseJ_planar_le {e : Homogenization.Vec d} (he : e ⬝ᵥ e = 1) {σ lam : ℝ}
    (hσ : 0 < σ) (hlam : 0 < lam) :
    Ch02.responseJ U a (σ⁻¹ • (lam • e)) (σ • e) ≤
      lam * Coarse.phi |Real.log lam| (Ch02.responseJ U a (σ⁻¹ • e) (σ • e)) := by
  set r := Real.sqrt lam with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr hlam
  have hr2 : r ^ 2 = lam := Real.sq_sqrt hlam.le
  have h := responseJ_pair_le ha he hσ hlam (u := r) (v := r⁻¹) (mul_inv_cancel₀ hr0.ne') hr2
  have key : Ch02.responseJ U a (σ⁻¹ • (lam • e)) (σ • e) =
      lam * Ch02.responseJ U a (σ⁻¹ • (r • e)) (σ • (r⁻¹ • e)) := by
    rw [smul_smul, smul_smul, smul_smul, responseJ_smul_smul ha he, responseJ_smul_smul ha he,
      ← hr2]
    have hσ0 : σ ≠ 0 := hσ.ne'
    have hr0' : r ≠ 0 := hr0.ne'
    field_simp
  rw [key]
  exact mul_le_mul_of_nonneg_left h hlam.le

end Det

/-! ### The frozen probes against `J^max` -/

theorem probe_le_normalizedDefect (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (U : Ch02.Domain d) (ω : SubdiffusiveProcess.Model.PotentialSample d)
    {e : Homogenization.Vec d}
    (he : vecNormSq e = 1) :
    ENNReal.ofReal (Ch02.responseJ U (aCutoffCoeffOnData M L ω U).toCoeffOn
      ((Real.sqrt (ahom M L))⁻¹ • e) (Real.sqrt (ahom M L) • e)) ≤ normalizedDefect M L U ω := by
  unfold normalizedDefect paperScalarProbeMaxOn
  exact le_iSup_of_le (⟨e, he⟩ : {e : Homogenization.Vec d // vecNormSq e = 1}) le_rfl

/-- **C3 + C7, planar pair.** For `μ ∈ [0, F]`, pointwise where `J^max(U) < ∞`:
`J(U,(1+μ)e,e;b_L) ≤ 𝗋(μ) Φ_{log(1+2F)}(J^max(U))`. -/
theorem frozenJ_planar_le (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (U : Ch02.Domain d) (ω : SubdiffusiveProcess.Model.PotentialSample d)
    {e : Homogenization.Vec d}
    (he : vecNormSq e = 1) {μ F : ℝ} (hμ : 0 ≤ μ) (hμF : μ ≤ F)
    (hfin : normalizedDefect M L U ω ≠ ⊤) :
    frozenJ M L U ((1 + μ) • e) e ω ≤
      rMatch μ * PhiMap (Real.log (1 + 2 * F)) (normalizedDefect M L U ω).toReal := by
  have ha : Ch02.CoeffOn.IsSymmetric (aCutoffCoeffOnData M L ω U).toCoeffOn :=
    (aCutoffCoeffOnData M L ω U).isSymmetric
  have hσ : 0 < Real.sqrt (ahom M L) := Real.sqrt_pos.mpr (ahom_pos M L)
  have he' : e ⬝ᵥ e = 1 := he
  have hlam : 0 < 1 + μ := by linarith
  have h1 := responseJ_planar_le ha he' hσ hlam
  set j := Ch02.responseJ U (aCutoffCoeffOnData M L ω U).toCoeffOn
    ((Real.sqrt (ahom M L))⁻¹ • e) (Real.sqrt (ahom M L) • e) with hj
  have hj0 : 0 ≤ j := Ch02.responseJ_nonneg _ _ _ _
  have hjm : j ≤ (normalizedDefect M L U ω).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hfin).mp (probe_le_normalizedDefect M L U ω he)
  have hlog0 : 0 ≤ Real.log (1 + μ) := Real.log_nonneg (by linarith)
  have hlog : Real.log (1 + μ) ≤ Real.log (1 + 2 * F) := Real.log_le_log hlam (by linarith)
  have ht : 0 ≤ Real.log (1 + 2 * F) := hlog0.trans hlog
  have h2 : Coarse.phi |Real.log (1 + μ)| j ≤ Coarse.phi (Real.log (1 + 2 * F)) j := by
    rw [abs_of_nonneg hlog0]
    exact Coarse.phi_mono_t hj0 hlog0 ht hlog
  have h3 : Coarse.phi (Real.log (1 + 2 * F)) j ≤
      Coarse.phi (Real.log (1 + 2 * F)) (normalizedDefect M L U ω).toReal :=
    Coarse.phi_mono_j ht hj0 (hj0.trans hjm) hjm
  have hΦ0 : 0 ≤ Coarse.phi (Real.log (1 + 2 * F)) (normalizedDefect M L U ω).toReal :=
    Coarse.phi_nonneg ENNReal.toReal_nonneg ht
  have hr : 1 + μ ≤ rMatch μ := by unfold rMatch; nlinarith
  calc frozenJ M L U ((1 + μ) • e) e ω ≤ (1 + μ) * Coarse.phi |Real.log (1 + μ)| j := h1
    _ ≤ (1 + μ) * Coarse.phi (Real.log (1 + 2 * F)) (normalizedDefect M L U ω).toReal :=
        mul_le_mul_of_nonneg_left (h2.trans h3) hlam.le
    _ ≤ rMatch μ * PhiMap (Real.log (1 + 2 * F)) (normalizedDefect M L U ω).toReal :=
        mul_le_mul_of_nonneg_right hr hΦ0

/-- **C7, reciprocal pair.** For `β ∈ [1, 1+2F]`, pointwise where `J^max(U) < ∞`:
`J(U,√β e,e/√β;b_L) ≤ Φ_{log(1+2F)}(J^max(U))`. -/
theorem frozenJ_recip_le (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (U : Ch02.Domain d) (ω : SubdiffusiveProcess.Model.PotentialSample d)
    {e : Homogenization.Vec d}
    (he : vecNormSq e = 1) {β F : ℝ} (hβ : 1 ≤ β) (hβF : β ≤ 1 + 2 * F)
    (hfin : normalizedDefect M L U ω ≠ ⊤) :
    frozenJ M L U (Real.sqrt β • e) ((Real.sqrt β)⁻¹ • e) ω ≤
      PhiMap (Real.log (1 + 2 * F)) (normalizedDefect M L U ω).toReal := by
  have ha : Ch02.CoeffOn.IsSymmetric (aCutoffCoeffOnData M L ω U).toCoeffOn :=
    (aCutoffCoeffOnData M L ω U).isSymmetric
  have hσ : 0 < Real.sqrt (ahom M L) := Real.sqrt_pos.mpr (ahom_pos M L)
  have he' : e ⬝ᵥ e = 1 := he
  have hβ0 : 0 < β := by linarith
  have hr0 : 0 < Real.sqrt β := Real.sqrt_pos.mpr hβ0
  have h1 := responseJ_pair_le ha he' hσ hβ0 (u := Real.sqrt β) (v := (Real.sqrt β)⁻¹)
    (mul_inv_cancel₀ hr0.ne') (Real.sq_sqrt hβ0.le)
  set j := Ch02.responseJ U (aCutoffCoeffOnData M L ω U).toCoeffOn
    ((Real.sqrt (ahom M L))⁻¹ • e) (Real.sqrt (ahom M L) • e) with hj
  have hj0 : 0 ≤ j := Ch02.responseJ_nonneg _ _ _ _
  have hjm : j ≤ (normalizedDefect M L U ω).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hfin).mp (probe_le_normalizedDefect M L U ω he)
  have hlog0 : 0 ≤ Real.log β := Real.log_nonneg hβ
  have hlog : Real.log β ≤ Real.log (1 + 2 * F) := Real.log_le_log hβ0 hβF
  have ht : 0 ≤ Real.log (1 + 2 * F) := hlog0.trans hlog
  have h2 : Coarse.phi |Real.log β| j ≤ Coarse.phi (Real.log (1 + 2 * F)) j := by
    rw [abs_of_nonneg hlog0]
    exact Coarse.phi_mono_t hj0 hlog0 ht hlog
  have h3 : Coarse.phi (Real.log (1 + 2 * F)) j ≤
      Coarse.phi (Real.log (1 + 2 * F)) (normalizedDefect M L U ω).toReal :=
    Coarse.phi_mono_j ht hj0 (hj0.trans hjm) hjm
  exact h1.trans (h2.trans h3)

/-! ### The cell as a cube -/

theorem domain_ext {U V : Ch02.Domain d} (h : (U : Set (Homogenization.Vec d)) = V) : U = V := by
  obtain ⟨c1, i1, n1⟩ := U
  obtain ⟨c2, i2, n2⟩ := V
  change c1 = c2 at h
  subst h
  rfl

/-- A depth-`ν` cell `z + R` of `z + Q_m` is the cube `z' + Q_{m-ν}`,
`z' = z + 3^{m-ν}·index(R)`. -/
theorem cellAt_eq_cubeAt (z : Homogenization.Vec d) {m ν : ℕ} (hν : ν ≤ m)
    {R : Homogenization.TriadicCube d}
    (hR : R ∈ descendantsAtDepth (originCube d (m : ℤ)) ν) :
    cellAt z R = cubeAt (z + fun i => (R.index i : ℝ) * (3 : ℝ) ^ R.scale) (m - ν) := by
  have hs : R.scale = ((m - ν : ℕ) : ℤ) := by
    rw [scale_eq_sub_of_mem_descendantsAtDepth hR]
    simp only [originCube]
    omega
  apply domain_ext
  show translateSet z (openCubeSet R) =
    translateSet (z + fun i => (R.index i : ℝ) * (3 : ℝ) ^ R.scale)
      (openCubeSet (originCube d ((m - ν : ℕ) : ℤ)))
  ext x
  rw [mem_translateSet_iff_sub_mem, mem_translateSet_iff_sub_mem]
  simp only [openCubeSet, Set.mem_ofPred_eq, cubeScaleFactor, originCube, hs, Pi.sub_apply,
    Pi.add_apply, Pi.zero_apply, Int.cast_zero]
  constructor
  · intro h i
    have := h i
    constructor <;> linarith [this.1, this.2]
  · intro h i
    have := h i
    constructor <;> linarith [this.1, this.2]

/-! ### Monotonicity of the native caps -/

theorem Tvarpi_nonneg {D F : ℝ} (hD : 0 < D) (hF : 0 < F) : 0 ≤ Tvarpi D F := by
  unfold Tvarpi varpi
  exact Real.rpow_nonneg (le_min (div_pos hF hD).le zero_le_one) _

theorem Bbar32_nonneg (n : ℕ) {D F : ℝ} (hD : 0 < D) (hF : 0 < F) : 0 ≤ Bbar32 n D F := by
  have hT := Tvarpi_nonneg hD hF
  unfold Bbar32
  exact Real.rpow_nonneg (Finset.sum_nonneg fun k _ => by positivity) _

theorem Bbar32_anti {D F : ℝ} (hD : 0 < D) (hF : 0 < F) {n₁ n₂ : ℕ} (hn₁ : 1 ≤ n₁)
    (h : n₁ ≤ n₂) : Bbar32 n₂ D F ≤ Bbar32 n₁ D F := by
  have hT := Tvarpi_nonneg hD hF
  have h1 : (0 : ℝ) < n₁ := by exact_mod_cast hn₁
  have h12 : (n₁ : ℝ) ≤ n₂ := by exact_mod_cast h
  unfold Bbar32
  refine Real.rpow_le_rpow (Finset.sum_nonneg fun k _ => by positivity)
    (Finset.sum_le_sum fun k _ => ?_) (by norm_num)
  exact div_le_div_of_nonneg_left (by positivity) (pow_pos h1 _)
    (pow_le_pow_left₀ h1.le h12 _)

theorem sigmaNorm_nonneg' (d : ℕ) : (0 : ℝ) ≤ (sigmaNorm d : ℝ) := by
  unfold sigmaNorm
  split_ifs <;> norm_num

theorem nativeCap_nonneg' (d k : ℕ) {D F : ℝ} (hD : 0 < D) (hF : 0 < F) :
    0 ≤ nativeCap d k D F := by
  have hB := Bbar32_nonneg (3 ^ (d * (k - 1))) hD hF
  have hσ := sigmaNorm_nonneg' d
  unfold nativeCap
  exact le_min hD.le (by positivity)

/-- `k ↦ U_k` is nonincreasing on `k ≥ 1` (A6). -/
theorem nativeCap_anti {D F : ℝ} (hD : 0 < D) (hF : 0 < F) {k₁ k₂ : ℕ} (hk₁ : 1 ≤ k₁)
    (h : k₁ ≤ k₂) : nativeCap d k₂ D F ≤ nativeCap d k₁ D F := by
  have hσ := sigmaNorm_nonneg' d
  have hB := Bbar32_anti hD hF (n₁ := 3 ^ (d * (k₁ - 1))) (n₂ := 3 ^ (d * (k₂ - 1)))
    (Nat.one_le_pow _ _ (by norm_num))
    (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (by omega)))
  unfold nativeCap
  exact min_le_min le_rfl (by gcongr)

/-! ### `e_⋆ ≥ 0` -/

section EStar

variable (row : Row d)

theorem frakU_nonneg' (ℓ : ℕ) {D F : ℝ} (hD : 0 < D) (hF : 0 < F) : 0 ≤ frakU d ℓ D F := by
  have hB := Bbar32_nonneg (3 ^ (d * (ℓ - 1))) hD hF
  have hσ := sigmaNorm_nonneg' d
  unfold frakU
  split_ifs
  · norm_num
  · exact le_min zero_le_one (by positivity)

theorem eStar_nonneg (hO : row.Obligations) (hε : 0 ≤ (row.epsSub : ℝ)) {δ D F : ℝ}
    (hδ : 0 < δ) (hD : 0 < D) (hF : 0 < F) (hzF : row.zF δ < 1) : 0 ≤ row.eStar δ D F := by
  have hs : (0 : ℝ) < (row.s : ℝ) := by exact_mod_cast hO.par1.2.2.2.2.2.1
  have h2s : (d : ℝ) / 32 < 2 * (row.s : ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr hO.par1.2.2.2.2.2.2.2
    push_cast at h
    exact h
  have hη : (0 : ℝ) < (row.eta : ℝ) := by exact_mod_cast hO.par3.1
  have hw0 : 0 ≤ row.wHaar := by unfold Row.wHaar; positivity
  have hw1 : row.wHaar ≤ 1 := by
    unfold Row.wHaar
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hx0 : 0 < row.xHist := by unfold Row.xHist; positivity
  have hx1 : row.xHist < 1 := by
    unfold Row.xHist
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have h1w : 0 ≤ 1 - row.wHaar := by linarith
  have h1x : 0 < 1 - row.xHist := by linarith
  have hC1 : 0 ≤ row.C1 := by
    unfold Row.C1 Row.C0
    positivity
  have hS : 0 ≤ row.Sinf D F := by
    unfold Row.Sinf
    exact tsum_nonneg fun ℓ =>
      mul_nonneg (frakU_nonneg' ℓ hD hF) (pow_nonneg (inv_pos.2 hx0).le _)
  have hk := kappaH_nonneg d
  have ha := proxyA_pos
  have hCh : 0 ≤ Ch := by unfold Ch P32 varsigma; positivity
  have hzF0 : 0 ≤ row.zF δ := by unfold Row.zF; positivity
  have hzG0 : 0 ≤ row.zG δ := by unfold Row.zG; positivity
  have hzGF : row.zG δ ≤ row.zF δ := by
    unfold Row.zG Row.zF
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hx0.le
    have : 0 ≤ (96 * (proxyA : ℝ) + kappaH d) * δ ^ 2 := by positivity
    nlinarith
  have h1zF : 0 < 1 - row.zF δ := by linarith
  have h1zG : 0 < 1 - row.zG δ := by linarith
  have hF0 : 0 ≤ row.Fbar δ := by
    unfold Row.Fbar AF
    have : 0 ≤ √Ch := Real.sqrt_nonneg _
    positivity
  have hG0 : 0 ≤ row.Gbar δ := by
    unfold Row.Gbar AG
    have : 0 ≤ √Ch := Real.sqrt_nonneg _
    have : 0 ≤ varsigma := by unfold varsigma; positivity
    positivity
  have hM1 : 0 ≤ row.M1 δ := by
    unfold Row.M1
    exact Real.iSup_nonneg fun t => by positivity
  have hM2 : 0 ≤ row.M2 δ := by
    unfold Row.M2
    exact Real.iSup_nonneg fun t => by positivity
  have hU : 0 ≤ row.Ugrid δ := by
    have hP : 0 ≤ P32 := by unfold P32; positivity
    have hi : 0 ≤ (row.epsSub : ℝ)⁻¹ := inv_nonneg.mpr hε
    have hb : 0 ≤ (if d = 2 then P32 * δ ^ 2 * row.M1 δ
        else (1 + (row.epsSub : ℝ)) * P32 * δ ^ 2 * row.M1 δ +
          (1 + (row.epsSub : ℝ)⁻¹) * kappaH d ^ 2 * δ ^ 4 * row.M2 δ) := by
      split_ifs <;> positivity
    unfold Row.Ugrid Row.hbar varsigma
    positivity
  have hβ : 0 ≤ sphereFactor d := by
    unfold sphereFactor
    refine Real.rpow_nonneg ?_ _
    unfold sphereFactorPow
    split_ifs <;> positivity
  have hH : 0 ≤ row.Hhist δ D := by
    unfold Row.Hhist
    positivity
  unfold Row.eStar
  positivity

end EStar

end GMCExplicitDelta.Assembly.BadResponse
