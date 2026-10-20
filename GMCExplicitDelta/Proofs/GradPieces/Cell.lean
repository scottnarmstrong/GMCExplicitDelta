module

public import GMCExplicitDelta.Localization.GoodEvent
public import GMCExplicitDelta.Localization.Bridge
public import GMCExplicitDelta.Coarse.Order
public import GMCExplicitDelta.Coarse.Scaling
public import GMCExplicitDelta.Coarse.Affine

/-!
Pieces of the localization argument on the good event (steps L2, G1).
Helper declarations live in the namespace `Localization.GradPieces`.

# Localization pieces: cell-level energy-to-mean inequalities (C5, C6) for the frozen coefficient

For a domain `U` on which `J^max(U; b_L) ≤ θ`, the spectral bounds `ā⁻¹ X_U ≤ 𝗑(θ)` and
`ā Y_U ≤ 𝗑(θ)` (C6) give, for every solution `w` of the cutoff equation on `U`,
`ā |(∇w)_U|² ≤ 𝗑(θ) ⨍ a_L|∇w|²` (C5).
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta.Localization.GradPieces

open Assembly Contract

variable {d : ℕ}

/-- The cutoff coefficient on `U`. -/
noncomputable abbrev cutA (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) (U : Ch02.Domain d) : Ch02.CoeffOn U :=
  (aCutoffCoeffOnData M L ω U).toCoeffOn

theorem cutA_symm (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) (U : Ch02.Domain d) :
    Ch02.CoeffOn.IsSymmetric (cutA M L ω U) :=
  Coarse.scalarCoeffOn_isSymmetric (aCutoffCoeffOnData M L ω U)

/-- For a unit vector, `J(U,e,e;b_L) = ½ ā⁻¹ e·X e + ½ ā e·Y e - 1`. -/
theorem frozenJ_unit_eq (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) (U : Ch02.Domain d)
    (e : Homogenization.Vec d) (he : e ⬝ᵥ e = 1) :
    frozenJ M L U e e ω =
      (1 / 2) * ((ahom M L)⁻¹ * Coarse.qf (Coarse.XU U (cutA M L ω U)) e) +
        (1 / 2) * (ahom M L * Coarse.qf (Coarse.YU U (cutA M L ω U)) e) - 1 := by
  have hs := ahom_pos' M L
  have hsq : 0 < Real.sqrt (ahom M L) := Real.sqrt_pos.mpr hs
  have hsq2 : Real.sqrt (ahom M L) ^ 2 = ahom M L := Real.sq_sqrt hs.le
  unfold frozenJ
  show Ch02.responseJ U (cutA M L ω U) _ _ = _
  rw [Coarse.responseJ_eq_XY (cutA_symm M L ω U), Coarse.posDef_qf_smul, Coarse.posDef_qf_smul,
    smul_dotProduct, dotProduct_smul, he, smul_eq_mul, smul_eq_mul, inv_pow, hsq2]
  have : (Real.sqrt (ahom M L))⁻¹ * (Real.sqrt (ahom M L) * 1) = 1 := by
    field_simp
  rw [this]

/-- **C6 on a cell**: a defect bound on unit vectors gives the spectral bounds of `X` and `Y`. -/
theorem cell_bounds (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) (U : Ch02.Domain d) {θ : ℝ} (hθ : 0 ≤ θ)
    (h : ∀ e : Homogenization.Vec d, e ⬝ᵥ e = 1 → frozenJ M L U e e ω ≤ θ)
    (ξ : Homogenization.Vec d) :
    (ahom M L)⁻¹ * Coarse.qf (Coarse.XU U (cutA M L ω U)) ξ ≤ Coarse.xfun θ * (ξ ⬝ᵥ ξ) ∧
      ahom M L * Coarse.qf (Coarse.YU U (cutA M L ω U)) ξ ≤ Coarse.xfun θ * (ξ ⬝ᵥ ξ) := by
  have hs := ahom_pos' M L
  have ha := cutA_symm M L ω U
  set X := Coarse.XU U (cutA M L ω U) with hX
  set Y := Coarse.YU U (cutA M L ω U) with hY
  -- unit case
  have unit : ∀ e : Homogenization.Vec d, e ⬝ᵥ e = 1 →
      (ahom M L)⁻¹ * Coarse.qf X e ≤ Coarse.xfun θ ∧ ahom M L * Coarse.qf Y e ≤ Coarse.xfun θ := by
    intro e he
    have he0 : e ≠ 0 := by rintro rfl; simp at he
    have hXpos := Coarse.posDef_qf_pos (Coarse.XU_posDef ha) he0
    have hYpos := Coarse.posDef_qf_pos (Coarse.YU_posDef ha) he0
    have hsq := Coarse.sq_dot_le_XU ha e
    rw [he] at hsq
    have hJ := frozenJ_unit_eq M L ω U e he
    have hJle := h e he
    have hα : 0 < (ahom M L)⁻¹ * Coarse.qf X e := mul_pos (inv_pos.mpr hs) hXpos
    have hβ : 0 < ahom M L * Coarse.qf Y e := mul_pos hs hYpos
    have hprod : (1 : ℝ) ^ 2 ≤ ((ahom M L)⁻¹ * Coarse.qf X e) * (ahom M L * Coarse.qf Y e) := by
      have : ((ahom M L)⁻¹ * Coarse.qf X e) * (ahom M L * Coarse.qf Y e) =
          Coarse.qf X e * Coarse.qf Y e := by field_simp
      rw [this]; nlinarith
    have hsum : ((ahom M L)⁻¹ * Coarse.qf X e) + (ahom M L * Coarse.qf Y e) ≤
        (2 + 2 * θ) * 1 := by linarith
    have h1 := Coarse.bounds_of_sum_le hθ one_pos hα hβ.le hprod hsum
    have h2 := Coarse.bounds_of_sum_le hθ one_pos hβ hα.le (by rw [mul_comm]; exact hprod)
      (by linarith)
    exact ⟨by simpa using h1.2, by simpa using h2.2⟩
  by_cases hξ : ξ ⬝ᵥ ξ = 0
  · have hξ0 : ξ = 0 := Homogenization.vecNormSq_eq_zero hξ
    subst hξ0
    simp [Coarse.qf]
  · have hpos : 0 < ξ ⬝ᵥ ξ := lt_of_le_of_ne (Homogenization.vecNormSq_nonneg ξ) (Ne.symm hξ)
    set r := Real.sqrt (ξ ⬝ᵥ ξ) with hr
    have hr0 : 0 < r := Real.sqrt_pos.mpr hpos
    have hr2 : r ^ 2 = ξ ⬝ᵥ ξ := Real.sq_sqrt hpos.le
    set e := r⁻¹ • ξ with he
    have hee : e ⬝ᵥ e = 1 := by
      rw [he, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← hr2]
      field_simp
    have hξe : ξ = r • e := by rw [he, smul_smul, mul_inv_cancel₀ hr0.ne', one_smul]
    obtain ⟨u1, u2⟩ := unit e hee
    have eq1 : Coarse.qf X ξ = r ^ 2 * Coarse.qf X e := by
      rw [hξe, Coarse.posDef_qf_smul]
    have eq2 : Coarse.qf Y ξ = r ^ 2 * Coarse.qf Y e := by
      rw [hξe, Coarse.posDef_qf_smul]
    rw [eq1, eq2, ← hr2]
    constructor
    · calc (ahom M L)⁻¹ * (r ^ 2 * Coarse.qf X e) = r ^ 2 * ((ahom M L)⁻¹ * Coarse.qf X e) := by ring
        _ ≤ r ^ 2 * Coarse.xfun θ := mul_le_mul_of_nonneg_left u1 (sq_nonneg r)
        _ = _ := by ring
    · calc ahom M L * (r ^ 2 * Coarse.qf Y e) = r ^ 2 * (ahom M L * Coarse.qf Y e) := by ring
        _ ≤ r ^ 2 * Coarse.xfun θ := mul_le_mul_of_nonneg_left u2 (sq_nonneg r)
        _ = _ := by ring

/-- **C5 (gradient)**: `ā |(∇w)_U|² ≤ 𝗑(θ) ⨍ a_L|∇w|²` for a solution `w` on `U`. -/
theorem c5_grad (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) (U : Ch02.Domain d) {θ : ℝ} (hθ : 0 ≤ θ)
    (h : ∀ e : Homogenization.Vec d, e ⬝ᵥ e = 1 → frozenJ M L U e e ω ≤ θ)
    (w : Ch02.Solution U (cutA M L ω U)) :
    ahom M L * vecNormSq (Ch02.averageGradient U (cutA M L ω U) w) ≤
      Coarse.xfun θ * Ch02.variationEnergyValue U (cutA M L ω U) w := by
  have hs := ahom_pos' M L
  have ha := cutA_symm M L ω U
  set g := Ch02.averageGradient U (cutA M L ω U) w with hg
  have hest := ((Ch02.responseCoarseGrainingEstimatesTheory U (cutA M L ω U)).average_gradient_energy w)
  have hstar : Ch02.aStarCoarse U (cutA M L ω U) = Ch02.sigmaStarCoarse U (cutA M L ω U) :=
    Coarse.aStar_eq_sigmaStar ha
  have hE : Coarse.qf (Ch02.aStarCoarse U (cutA M L ω U)) g ≤
      Ch02.variationEnergyValue U (cutA M L ω U) w := by
    rw [hstar]
    have : vecDot g (matVecMul (Ch02.sigmaStarCoarse U (cutA M L ω U)) g) =
        Coarse.qf (Ch02.sigmaStarCoarse U (cutA M L ω U)) g := rfl
    linarith
  have hYinv : (Coarse.YU U (cutA M L ω U))⁻¹ = Ch02.aStarCoarse U (cutA M L ω U) :=
    Coarse.YU_inv ha
  have hsq := Coarse.posDef_sq_dot_le (Coarse.YU_posDef ha) g
  rw [hYinv] at hsq
  have hb := (cell_bounds M L ω U hθ h g).2
  have hxpos := Coarse.xfun_pos hθ
  have hnn : 0 ≤ Coarse.qf (Ch02.aStarCoarse U (cutA M L ω U)) g :=
    Coarse.posDef_qf_nonneg (Coarse.aStar_posDef ha) g
  have hgg : 0 ≤ g ⬝ᵥ g := Homogenization.vecNormSq_nonneg g
  change ahom M L * (g ⬝ᵥ g) ≤ _
  rcases hgg.lt_or_eq with hpos | hz
  · -- (g.g)^2 <= qf Y g * qf aStar g <= (x/a) (g.g) qf aStar g
    have h1 : (g ⬝ᵥ g) ^ 2 ≤ (Coarse.xfun θ * (g ⬝ᵥ g) / ahom M L) *
        Coarse.qf (Ch02.aStarCoarse U (cutA M L ω U)) g := by
      refine hsq.trans (mul_le_mul_of_nonneg_right ?_ hnn)
      rw [le_div_iff₀ hs]
      linarith [mul_comm (Coarse.qf (Coarse.YU U (cutA M L ω U)) g) (ahom M L)]
    have h2 : ahom M L * (g ⬝ᵥ g) ≤ Coarse.xfun θ *
        Coarse.qf (Ch02.aStarCoarse U (cutA M L ω U)) g := by
      have h3 : ahom M L * (g ⬝ᵥ g) * (g ⬝ᵥ g) ≤
          Coarse.xfun θ * Coarse.qf (Ch02.aStarCoarse U (cutA M L ω U)) g * (g ⬝ᵥ g) := by
        have : (Coarse.xfun θ * (g ⬝ᵥ g) / ahom M L) *
            Coarse.qf (Ch02.aStarCoarse U (cutA M L ω U)) g * ahom M L =
            Coarse.xfun θ * Coarse.qf (Ch02.aStarCoarse U (cutA M L ω U)) g * (g ⬝ᵥ g) := by
          field_simp
        nlinarith [h1, hs]
      exact le_of_mul_le_mul_right h3 hpos
    exact h2.trans (mul_le_mul_of_nonneg_left hE hxpos.le)
  · rw [← hz]
    simp only [mul_zero]
    exact mul_nonneg hxpos.le (hnn.trans hE)

end GMCExplicitDelta.Localization.GradPieces
