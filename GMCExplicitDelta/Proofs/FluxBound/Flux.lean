module

public import GMCExplicitDelta.Proofs.FluxBound.Cell

/-! # G1(c): C5 flux bounds and restriction of solutions to descendant cells. -/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta.Localization.FluxBound

open Assembly Contract

variable {d : ℕ}

theorem bCoarse_eq_XU (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) (U : Ch02.Domain d) :
    Ch02.bCoarse U (cutA M L ω U) = Coarse.XU U (cutA M L ω U) := by
  have hk := Coarse.kappa_eq_zero (cutA_symm M L ω U)
  rw [Coarse.XU_eq_sigma (cutA_symm M L ω U)]
  simp [Ch02.bCoarse, Ch02.coarseMatrices, Ch02.CoarseMatrices.b, hk, matTranspose]

/-- **C5 (flux)**: `ā⁻¹ |(a_L∇w)_U|² ≤ 𝗑(θ) ⨍ a_L|∇w|²` for a solution `w` on `U`. -/
theorem c5_flux (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) (U : Ch02.Domain d) {θ : ℝ} (hθ : 0 ≤ θ)
    (h : ∀ e : Homogenization.Vec d, e ⬝ᵥ e = 1 → frozenJ M L U e e ω ≤ θ)
    (w : Ch02.Solution U (cutA M L ω U)) :
    (ahom M L)⁻¹ * vecNormSq (Ch02.averageFlux U (cutA M L ω U) w) ≤
      Coarse.xfun θ * Ch02.variationEnergyValue U (cutA M L ω U) w := by
  have hs := ahom_pos' M L
  have ha := cutA_symm M L ω U
  set F := Ch02.averageFlux U (cutA M L ω U) w with hF
  have hest := ((Ch02.responseCoarseGrainingEstimatesTheory U (cutA M L ω U)).average_flux_energy w)
  have hE : Coarse.qf (Coarse.XU U (cutA M L ω U))⁻¹ F ≤
      Ch02.variationEnergyValue U (cutA M L ω U) w := by
    rw [bCoarse_eq_XU] at hest
    have : vecDot F (matVecMul ((Coarse.XU U (cutA M L ω U))⁻¹) F) =
        Coarse.qf (Coarse.XU U (cutA M L ω U))⁻¹ F := rfl
    linarith
  have hsq := Coarse.posDef_sq_dot_le (Coarse.XU_posDef ha) F
  have hb := (cell_bounds M L ω U hθ h F).1
  have hxpos := Coarse.xfun_pos hθ
  have hnn : 0 ≤ Coarse.qf (Coarse.XU U (cutA M L ω U))⁻¹ F :=
    Coarse.posDef_qf_nonneg (Coarse.XU_posDef ha).inv F
  have hgg : 0 ≤ F ⬝ᵥ F := Homogenization.vecNormSq_nonneg F
  change (ahom M L)⁻¹ * (F ⬝ᵥ F) ≤ _
  rcases hgg.lt_or_eq with hpos | hz
  · have hqX : Coarse.qf (Coarse.XU U (cutA M L ω U)) F ≤ ahom M L * Coarse.xfun θ * (F ⬝ᵥ F) := by
      have := mul_le_mul_of_nonneg_left hb hs.le
      rw [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul] at this
      linarith
    have h1 : (F ⬝ᵥ F) ^ 2 ≤ (ahom M L * Coarse.xfun θ * (F ⬝ᵥ F)) *
        Coarse.qf (Coarse.XU U (cutA M L ω U))⁻¹ F :=
      hsq.trans (mul_le_mul_of_nonneg_right hqX hnn)
    have h2 : (F ⬝ᵥ F) ≤ ahom M L * Coarse.xfun θ *
        Coarse.qf (Coarse.XU U (cutA M L ω U))⁻¹ F := by
      have h3 : (F ⬝ᵥ F) * (F ⬝ᵥ F) ≤ (ahom M L * Coarse.xfun θ *
          Coarse.qf (Coarse.XU U (cutA M L ω U))⁻¹ F) * (F ⬝ᵥ F) := by nlinarith [h1]
      exact le_of_mul_le_mul_right h3 hpos
    calc (ahom M L)⁻¹ * (F ⬝ᵥ F) ≤ (ahom M L)⁻¹ * (ahom M L * Coarse.xfun θ *
          Coarse.qf (Coarse.XU U (cutA M L ω U))⁻¹ F) :=
          mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hs.le)
      _ = Coarse.xfun θ * Coarse.qf (Coarse.XU U (cutA M L ω U))⁻¹ F := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hE hxpos.le
  · rw [← hz]
    simp only [mul_zero]
    exact mul_nonneg hxpos.le (hnn.trans hE)

/-! ### Restriction of solutions to subdomains and differences of solutions -/

theorem cellCarrier_eq (R : Homogenization.TriadicCube d) :
    ((cellAt 0 R : Ch02.Domain d) : Set (Homogenization.Vec d)) = openCubeSet R := by
  show translateSet 0 (openCubeSet R) = openCubeSet R
  simp

theorem cell_subset {Q R : Homogenization.TriadicCube d} {k : ℕ}
    (hR : R ∈ descendantsAtDepth Q k) :
    ((cellAt 0 R : Ch02.Domain d) : Set (Homogenization.Vec d)) ⊆
      ((cellAt 0 Q : Ch02.Domain d) : Set (Homogenization.Vec d)) := by
  rw [cellCarrier_eq, cellCarrier_eq]
  exact openCubeSet_subset_of_mem_descendantsAtDepth hR

/-- Restriction of a solution of the cutoff equation to a subdomain. -/
noncomputable def restrictSol (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) {U V : Ch02.Domain d}
    (hVU : (V : Set (Homogenization.Vec d)) ⊆ (U : Set (Homogenization.Vec d)))
    (u : Ch02.Solution U (cutA M L ω U)) : Ch02.Solution V (cutA M L ω V) :=
  u.restrictOfMemVectorL2 U.isOpen V.isOpen hVU (by
    have hf := Ch02.Solution.flux_memVectorL2 u
    have hle : volumeMeasureOn (V : Set (Homogenization.Vec d)) ≤
        volumeMeasureOn (U : Set (Homogenization.Vec d)) := by
      simpa [volumeMeasureOn] using MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hVU
    exact hf.mono_measure hle)

end GMCExplicitDelta.Localization.FluxBound
