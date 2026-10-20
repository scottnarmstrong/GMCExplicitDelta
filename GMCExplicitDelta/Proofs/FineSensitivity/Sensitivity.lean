module

public import GMCExplicitDelta.Proofs.FineSensitivity.Scaled
public import GMCExplicitDelta.Proofs.FineSensitivity.Young

/-! # Deterministic weighted response sensitivity -/

@[expose] public section

open MeasureTheory Homogenization Homogenization.Book.Ch02
open SubdiffusiveProcess.CoarseGrainingVocab

namespace GMCExplicitDelta.Assembly

variable {d : ℕ}

/-- The two nonnegative, spatially weighted G3 remainder densities. -/
noncomputable def fineRemainderDensity (a ρ : Homogenization.Vec d → ℝ) (η : ℝ)
    (v u : Homogenization.Vec d → Homogenization.Vec d) (x : Homogenization.Vec d) : ℝ :=
  a x * ((ρ x - 1) ^ 2 / (8 * η) * vecNormSq (v x - u x) +
    (ρ x + (ρ x)⁻¹ - 2) / 2 * vecNormSq (u x))

/-- The remainder is pointwise nonnegative for positive coefficient and ratio. -/
theorem fineRemainderDensity_nonneg {a ρ : Homogenization.Vec d → ℝ} {η : ℝ}
    (hη : 0 < η) (v u : Homogenization.Vec d → Homogenization.Vec d)
    (x : Homogenization.Vec d) (ha : 0 ≤ a x) (hρ : 0 < ρ x) :
    0 ≤ fineRemainderDensity a ρ η v u x := by
  unfold fineRemainderDensity
  rw [fine_ratio_weight_eq hρ]
  exact mul_nonneg ha (add_nonneg
    (mul_nonneg (div_nonneg (sq_nonneg _) (by positivity)) (vecNormSq_nonneg _))
    (mul_nonneg (div_nonneg (mul_nonneg (inv_nonneg.mpr hρ.le) (sq_nonneg _))
      (by norm_num)) (vecNormSq_nonneg _)))

/-- C12 and Young, retaining the spatial integral of the remainder. Integrability
is explicit here; the model application supplies it from cutoff ellipticity. -/
theorem responseJ_le_fineRemainder {U : Domain d} {a a' ρ : Homogenization.Vec d → ℝ}
    (h : ScalarCoeffOnData U a) (h' : ScalarCoeffOnData U a')
    {η : ℝ} (hη : 0 < η) {e : Homogenization.Vec d} (he : e ⬝ᵥ e = 1)
    {v u : Solution U h.toCoeffOn}
    (hv : IsResponseMaximizer U h.toCoeffOn e 0 v)
    (hu : IsResponseMaximizer U h.toCoeffOn 0 e u)
    (hρ : ∀ᵐ x ∂volumeMeasureOn (U : Set (Homogenization.Vec d)),
      0 < ρ x ∧ a' x = a x * ρ x)
    (hR : Integrable (fineRemainderDensity a ρ η v.toH1.grad u.toH1.grad)
      (volumeMeasureOn (U : Set (Homogenization.Vec d)))) :
    responseJ U h'.toCoeffOn e e ≤ (1 + η) * responseJ U h.toCoeffOn e e +
      average U (fineRemainderDensity a ρ η v.toH1.grad u.toH1.grad) := by
  obtain ⟨i⟩ := Coarse.nonempty_fin_of_dot_one he
  let V := v.toH1.grad
  let W := u.toH1.grad
  have hV : Integrable (fun x => a x * vecNormSq (V x))
      (volumeMeasureOn (U : Set (Homogenization.Vec d))) :=
    Coarse.integrable_energy h i v.toH1.gradMemL2
  have hW : Integrable (fun x => a x * vecNormSq (W x))
      (volumeMeasureOn (U : Set (Homogenization.Vec d))) :=
    Coarse.integrable_energy h i u.toH1.gradMemL2
  have hD : GradMemL2On (U : Set (Homogenization.Vec d)) (fun x => V x + W x) :=
    fun j => (v.toH1.gradMemL2 j).add (u.toH1.gradMemL2 j)
  have hDI : Integrable (fun x => a x * vecNormSq (V x + W x))
      (volumeMeasureOn (U : Set (Homogenization.Vec d))) :=
    Coarse.integrable_energy h i hD
  have hsum : Integrable (fun x => (a x * vecNormSq (V x) + a x * vecNormSq (W x)) / 2)
      (volumeMeasureOn (U : Set (Homogenization.Vec d))) := (hV.add hW).div_const 2
  have hright := (hsum.add (hDI.const_mul (η / 2))).add hR
  have hleft := ((Coarse.integrable_energy h' i v.toH1.gradMemL2).add
    (Coarse.integrable_ainv_a_sq h h' i u.toH1.gradMemL2)).div_const 2
  have hbound := Coarse.average_mono' hleft hright (by
    filter_upwards [hρ, Coarse.a_pos_ae h] with x hx hax
    have hy := mul_le_mul_of_nonneg_left
      (fine_competitor_vector_density_le hη (ρ x) (V x) (W x)) hax.le
    dsimp only [Pi.add_apply]
    rw [hx.2]
    convert hy using 1
    all_goals
      dsimp [fineRemainderDensity, V, W, vecNormSq]
      field_simp [hax.ne', hx.1.ne']
      all_goals ring)
  have hcomp := Coarse.responseJ_le_competitor h h' he hv hu
  have hbase : average U (fun x => (a x * vecNormSq (V x) + a x * vecNormSq (W x)) / 2) =
      responseJ U h.toCoeffOn e e + 1 := by
    have hfun : (fun x => (a x * vecNormSq (V x) + a x * vecNormSq (W x)) / 2) =
        (fun x => (1 / 2 : ℝ) * (a x * vecNormSq (V x) + a x * vecNormSq (W x))) := by
      funext x; ring
    rw [hfun, Coarse.average_const_mul']
    have hXY := Coarse.responseJ_eq_XY (Coarse.scalarCoeffOn_isSymmetric h)
    have hE1 := Coarse.average_energy_v (Coarse.scalarCoeffOn_isSymmetric h) hv
    have hE2 := Coarse.average_energy_u (Coarse.scalarCoeffOn_isSymmetric h) hu
    simp_rw [Coarse.vecDot_scalar_coeff h] at hE1 hE2
    rw [Coarse.average_add' hV hW]
    rw [hXY, he]
    change (1 / 2 : ℝ) * _ = _
    dsimp only [V, W, vecNormSq]
    rw [hE1, hE2]
    ring
  have hdefect : (1 / 2 : ℝ) * average U
      (fun x => a x * vecNormSq (V x + W x)) = responseJ U h.toCoeffOn e e := by
    convert Coarse.half_average_energy_sum (Coarse.scalarCoeffOn_isSymmetric h) hv hu using 1
    congr 2
    funext x
    exact (Coarse.vecDot_scalar_coeff h x _).symm
  change average U (fun x => (a' x * vecNormSq (V x) +
      (a' x)⁻¹ * (a x ^ 2 * vecNormSq (W x))) / 2) ≤
    average U (fun x => ((a x * vecNormSq (V x) + a x * vecNormSq (W x)) / 2 +
      η / 2 * (a x * vecNormSq (V x + W x))) +
        fineRemainderDensity a ρ η V W x) at hbound
  have hav := Coarse.average_add' (hsum.add (hDI.const_mul (η / 2))) hR
  change average U (fun x =>
      (a x * vecNormSq (V x) + a x * vecNormSq (W x)) / 2 +
        η / 2 * (a x * vecNormSq (V x + W x)) + fineRemainderDensity a ρ η V W x) =
    average U (fun x => (a x * vecNormSq (V x) + a x * vecNormSq (W x)) / 2 +
      η / 2 * (a x * vecNormSq (V x + W x))) +
      average U (fineRemainderDensity a ρ η V W) at hav
  rw [hav, Coarse.average_add' hsum (hDI.const_mul (η / 2)), hbase,
    Coarse.average_const_mul'] at hbound
  have hscale : η / 2 * average U (fun x => a x * vecNormSq (V x + W x)) =
      η * responseJ U h.toCoeffOn e e := by rw [← hdefect]; ring
  rw [hscale] at hbound
  rw [← Coarse.average_const_mul' (1 / 2 : ℝ)] at hcomp
  have hhalf : (fun x => (1 / 2 : ℝ) *
      (a' x * vecDot (v.toH1.grad x) (v.toH1.grad x) +
        (a' x)⁻¹ * (a x ^ 2 * vecDot (u.toH1.grad x) (u.toH1.grad x)))) =
      (fun x => (a' x * vecDot (v.toH1.grad x) (v.toH1.grad x) +
        (a' x)⁻¹ * (a x ^ 2 * vecDot (u.toH1.grad x) (u.toH1.grad x))) / 2) := by
    funext x; ring
  rw [hhalf] at hcomp
  dsimp only [V, W, vecNormSq] at hbound ⊢
  linarith only [hcomp, hbound]

end GMCExplicitDelta.Assembly
