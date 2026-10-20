module

public import GMCExplicitDelta.Coarse.Order
public import GMCExplicitDelta.Coarse.Average
public import SubdiffusiveProcess.Assumptions.CoefficientPackaging

/-!
# C4: the affine trial for a scalar coefficient

For a scalar coefficient `a` with ellipticity data on `U` and a unit vector `e`:
`e·X_U e ≤ avg_U a`, `e·Y_U e ≤ avg_U a⁻¹`, hence
`J(U,e,e;a) ≤ avg_U (cosh (log a) - 1)`.

Reused from CoarseGraining: `responseSymmetricDirichletNeumannTheory`
(`dirichlet_neumann_bracketing`: `(avg symm(a)⁻¹)⁻¹ ≤ A_* ≤ A ≤ avg a`).
-/

@[expose] public section

open Homogenization.Book.Ch02
open Homogenization (Vec Mat vecDot vecNormSq matVecMul matTranspose symmPart MatLoewnerLE
  scalarMatrix volumeMeasureOn MemVectorL2 GradMemL2On H1Function restrictCoeffField
  vecNormSq_nonneg vecNormSq_eq_zero)
open Matrix
open MeasureTheory hiding average
open SubdiffusiveProcess.CoarseGrainingVocab (ScalarCoeffOnData scalarCoeffField)

namespace GMCExplicitDelta.Coarse

variable {d : ℕ} {U : Domain d} {a : Vec d → ℝ}

theorem scalarCoeffOn_isSymmetric (h : ScalarCoeffOnData U a) :
    CoeffOn.IsSymmetric h.toCoeffOn :=
  Filter.Eventually.of_forall fun x => Homogenization.scalarMatrix_isSymm (a x)

theorem averageMat_scalar (f : Vec d → ℝ) :
    averageMat U (fun x => Homogenization.scalarMatrix (f x)) =
      average U f • (1 : Mat d) := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp [averageMat, Homogenization.scalarMatrix]
  · simp [averageMat, Homogenization.scalarMatrix, hij, average]

theorem a_pos_ae (h : ScalarCoeffOnData U a) :
    ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)), 0 < a x :=
  h.aeBounds.mono fun x hx => lt_of_lt_of_le h.lam_pos hx.1

theorem integrable_scalar (h : ScalarCoeffOnData U a) (i : Fin d) :
    Integrable a (volumeMeasureOn (U : Set (Vec d))) := by
  have hm := h.aeStronglyMeasurable i i
  have hae : (fun x : Vec d =>
      restrictCoeffField (U : Set (Vec d)) (scalarCoeffField a) x i i) =ᵐ[
        volumeMeasureOn (U : Set (Vec d))] a := by
    have : ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)), x ∈ (U : Set (Vec d)) := by
      simpa [volumeMeasureOn] using ae_restrict_mem U.measurableSet
    filter_upwards [this] with x hx
    simp [Homogenization.restrictCoeffField_apply_of_mem hx, scalarCoeffField, Homogenization.scalarMatrix]
  have hm' : AEStronglyMeasurable a (volumeMeasureOn (U : Set (Vec d))) :=
    hm.congr hae
  refine Integrable.of_bound hm' h.Lam ?_
  filter_upwards [h.aeBounds] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (le_trans h.lam_pos.le hx.1)]
  exact hx.2

theorem integrable_scalar_inv (h : ScalarCoeffOnData U a) (i : Fin d) :
    Integrable (fun x => (a x)⁻¹) (volumeMeasureOn (U : Set (Vec d))) := by
  have hm := (integrable_scalar h i).aestronglyMeasurable
  have hm' : AEStronglyMeasurable (fun x => (a x)⁻¹) (volumeMeasureOn (U : Set (Vec d))) :=
    (aestronglyMeasurable_iff_aemeasurable.mp hm).inv.aestronglyMeasurable
  refine Integrable.of_bound hm' (h.lam)⁻¹ ?_
  filter_upwards [h.aeBounds] with x hx
  have hax : 0 < a x := lt_of_lt_of_le h.lam_pos hx.1
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hax)]
  exact inv_anti₀ h.lam_pos hx.1

theorem average_inv_ge (h : ScalarCoeffOnData U a) (i : Fin d) :
    (h.Lam)⁻¹ ≤ average U (fun x => (a x)⁻¹) := by
  have hv := volume_toReal_pos' U
  unfold average
  have hint := integrable_scalar_inv h i
  have hle : ∫ x in (U : Set (Vec d)), (h.Lam)⁻¹ ∂volume ≤
      ∫ x in (U : Set (Vec d)), (a x)⁻¹ ∂volume := by
    refine integral_mono_ae (integrable_const _) hint ?_
    filter_upwards [h.aeBounds] with x hx
    have hax : 0 < a x := lt_of_lt_of_le h.lam_pos hx.1
    exact inv_anti₀ hax hx.2
  rw [setIntegral_const] at hle
  simp only [Measure.real, smul_eq_mul] at hle
  rw [le_inv_mul_iff₀ hv]
  linarith

theorem posDef_scalar {c : ℝ} (hc : 0 < c) :
    (c • (1 : Mat d)).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · ext i j
    simp [Matrix.conjTranspose_apply, Matrix.one_apply, eq_comm]
  · intro x hx
    have : 0 < x ⬝ᵥ x := by
      rcases (vecNormSq_nonneg x).lt_or_eq with h' | h'
      · exact h'
      · exact absurd (vecNormSq_eq_zero h'.symm) hx
    simpa [Matrix.smul_mulVec, dotProduct_smul] using mul_pos hc this

theorem symmPart_scalar (s : ℝ) :
    symmPart (Homogenization.scalarMatrix (d := d) s) = Homogenization.scalarMatrix s := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp [symmPart, Homogenization.scalarMatrix]
  · have : j ≠ i := fun h => hij h.symm
    simp [symmPart, Homogenization.scalarMatrix, hij, this]

theorem inv_scalar {s : ℝ} (hs : s ≠ 0) :
    (Homogenization.scalarMatrix (d := d) s)⁻¹ = Homogenization.scalarMatrix s⁻¹ := by
  apply Matrix.inv_eq_right_inv
  simp [Homogenization.scalarMatrix, smul_smul, inv_mul_cancel₀ hs]

theorem qf_XU_le_average (h : ScalarCoeffOnData U a) (e : Vec d) :
    qf (XU U h.toCoeffOn) e ≤ average U a * (e ⬝ᵥ e) := by
  have hsym := scalarCoeffOn_isSymmetric h
  have hb := (responseSymmetricDirichletNeumannTheory U h.toCoeffOn hsym
    ).dirichlet_neumann_bracketing.2.2
  rw [matLoewnerLE_iff_qf] at hb
  have e1 : averageMat U h.toCoeffOn.toCoeffField = average U a • (1 : Mat d) :=
    averageMat_scalar a
  have := hb e
  rw [e1, qf_smul_one, ← XU_eq_sigma hsym] at this
  exact this

theorem qf_YU_le_average (h : ScalarCoeffOnData U a) (i : Fin d) (e : Vec d) :
    qf (YU U h.toCoeffOn) e ≤ average U (fun x => (a x)⁻¹) * (e ⬝ᵥ e) := by
  have hsym := scalarCoeffOn_isSymmetric h
  have hb := (responseSymmetricDirichletNeumannTheory U h.toCoeffOn hsym
    ).dirichlet_neumann_bracketing.1
  rw [matLoewnerLE_iff_qf] at hb
  set c := average U (fun x => (a x)⁻¹) with hc
  have hcpos : 0 < c := lt_of_lt_of_le (inv_pos.mpr (lt_of_lt_of_le h.lam_pos h.lam_le_Lam))
    (average_inv_ge h i)
  have hH : averagedSymmPartInv U h.toCoeffOn = c • (1 : Mat d) := by
    unfold averagedSymmPartInv
    have hae : (fun x => (symmPart (h.toCoeffOn.toCoeffField x))⁻¹) =ᵐ[
        volumeMeasureOn (U : Set (Vec d))]
        (fun x => Homogenization.scalarMatrix (d := d) (a x)⁻¹) := by
      filter_upwards [a_pos_ae h] with x hx
      show (symmPart (Homogenization.scalarMatrix (a x)))⁻¹ = _
      rw [symmPart_scalar, inv_scalar hx.ne']
    have : averageMat U (fun x => (symmPart (h.toCoeffOn.toCoeffField x))⁻¹) =
        averageMat U (fun x => Homogenization.scalarMatrix (d := d) (a x)⁻¹) := by
      ext i j
      unfold averageMat
      exact average_congr_ae (hae.mono fun x hx => congrFun (congrFun hx i) j)
    rw [this, averageMat_scalar]
  have hHpos : (c • (1 : Mat d)).PosDef := posDef_scalar hcpos
  rw [hH] at hb
  have hS : ((c • (1 : Mat d))⁻¹).PosDef := hHpos.inv
  have hanti := posDef_inv_antitone hS (sigmaStarCoarse_posDef U h.toCoeffOn) hb e
  have hinv : ((c • (1 : Mat d))⁻¹)⁻¹ = c • (1 : Mat d) :=
    Matrix.nonsing_inv_nonsing_inv _ (by
      simpa [Matrix.isUnit_iff_isUnit_det] using hHpos.isUnit)
  rw [hinv, qf_smul_one] at hanti
  show qf (aStarCoarse U h.toCoeffOn)⁻¹ e ≤ _
  rw [aStar_eq_sigmaStar hsym]
  exact hanti

/-- C4, affine trial: for a unit vector `e`, `J(U,e,e;a) ≤ avg_U (cosh (log a) - 1)`. -/
theorem responseJ_self_le_average_cosh_log (h : ScalarCoeffOnData U a) {e : Vec d}
    (he : e ⬝ᵥ e = 1) :
    responseJ U h.toCoeffOn e e ≤ average U (fun x => Real.cosh (Real.log (a x)) - 1) := by
  have hsym := scalarCoeffOn_isSymmetric h
  have i : Fin d := ⟨0, by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · subst h0; exact absurd he (by simp [dotProduct])
    · exact h0⟩
  have hX := qf_XU_le_average h e
  have hY := qf_YU_le_average h i e
  have hcosh : (fun x => Real.cosh (Real.log (a x)) - 1) =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      (fun x => (a x + (a x)⁻¹) / 2 - 1) := by
    filter_upwards [a_pos_ae h] with x hx
    rw [Real.cosh_log hx]
  rw [average_congr_ae hcosh, average_add_sub (integrable_scalar h i) (integrable_scalar_inv h i),
    responseJ_eq_XY hsym, he]
  rw [he] at hX hY
  linarith

/-- C4, supremum form: if `Jmax` bounds `J(U,e,e;a)` over unit vectors `e`, then so does the
affine trial. -/
theorem responseJ_le_average_cosh_log_forall (h : ScalarCoeffOnData U a) :
    ∀ e : Vec d, e ⬝ᵥ e = 1 →
      responseJ U h.toCoeffOn e e ≤ average U (fun x => Real.cosh (Real.log (a x)) - 1) :=
  fun _ he => responseJ_self_le_average_cosh_log h he

end GMCExplicitDelta.Coarse
