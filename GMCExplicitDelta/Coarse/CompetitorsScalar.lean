module

public import GMCExplicitDelta.Coarse.Competitors
public import GMCExplicitDelta.Coarse.Affine

/-!
# C12: the competitor inequality for scalar coefficients

For scalar coefficients `a, a'` on `U` (with ellipticity data), a unit vector `e`, `v` a response
maximizer for `(e,0)` and `u` a response maximizer for `(0,e)` (both for `a`):
`e·X_U(a') e ≤ avg a' |∇v|²`, `e·Y_U(a') e ≤ avg a'⁻¹ a² |∇u|²`, hence
`J(U,e,e;a') ≤ ½ avg (a' |∇v|² + a'⁻¹ a² |∇u|²) - 1`.

The proof uses CoarseGraining's symmetric Dirichlet-Neumann package
(`responseSymmetricDirichletNeumannTheory`: `response_maximizer_split`, `dirichlet_value_by_sigma`,
`neumann_value_by_sigmaStarInv`, existence of the Dirichlet minimizer and the Neumann maximizer).
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

theorem vecDot_scalar_coeff (h : ScalarCoeffOnData U a) (x : Vec d) (ξ : Vec d) :
    vecDot ξ (matVecMul (h.toCoeffOn.toCoeffField x) ξ) = a x * vecDot ξ ξ := by
  show vecDot ξ (matVecMul (Homogenization.scalarMatrix (a x)) ξ) = _
  rw [Homogenization.matVecMul_scalarMatrix]
  unfold vecDot
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem matVecMul_scalar_coeff (h : ScalarCoeffOnData U a) (x : Vec d) (ξ : Vec d) :
    matVecMul (h.toCoeffOn.toCoeffField x) ξ = a x • ξ :=
  Homogenization.matVecMul_scalarMatrix (a x) ξ

theorem nonempty_fin_of_dot_one {e : Vec d} (he : e ⬝ᵥ e = 1) : Nonempty (Fin d) := by
  rcases Nat.eq_zero_or_pos d with h0 | h0
  · subst h0; exact absurd he (by simp [dotProduct])
  · exact ⟨⟨0, h0⟩⟩

theorem integrable_a_mul (h : ScalarCoeffOnData U a) (i : Fin d) {f : Vec d → ℝ}
    (hf : Integrable f (volumeMeasureOn (U : Set (Vec d)))) :
    Integrable (fun x => a x * f x) (volumeMeasureOn (U : Set (Vec d))) := by
  refine hf.bdd_mul (c := h.Lam) (integrable_scalar h i).aestronglyMeasurable ?_
  filter_upwards [h.aeBounds] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (le_trans h.lam_pos.le hx.1)]
  exact hx.2

theorem integrable_ainv_mul (h : ScalarCoeffOnData U a) (i : Fin d) {f : Vec d → ℝ}
    (hf : Integrable f (volumeMeasureOn (U : Set (Vec d)))) :
    Integrable (fun x => (a x)⁻¹ * f x) (volumeMeasureOn (U : Set (Vec d))) := by
  refine hf.bdd_mul (c := (h.lam)⁻¹) (integrable_scalar_inv h i).aestronglyMeasurable ?_
  filter_upwards [h.aeBounds] with x hx
  have hax : 0 < a x := lt_of_lt_of_le h.lam_pos hx.1
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hax)]
  exact inv_anti₀ h.lam_pos hx.1

theorem integrable_energy (h : ScalarCoeffOnData U a) (i : Fin d) {g : Vec d → Vec d}
    (hg : GradMemL2On (U : Set (Vec d)) g) :
    Integrable (fun x => a x * vecDot (g x) (g x)) (volumeMeasureOn (U : Set (Vec d))) :=
  integrable_a_mul h i (integrable_dot_grad hg hg)

theorem energy_nonneg_ae (h : ScalarCoeffOnData U a) (g : Vec d → Vec d) :
    0 ≤ᵐ[volumeMeasureOn (U : Set (Vec d))] fun x => a x * vecDot (g x) (g x) := by
  filter_upwards [a_pos_ae h] with x hx
  exact mul_nonneg hx.le (vecNormSq_nonneg (g x))

/-- A field with zero `a`-energy vanishes almost everywhere. -/
theorem grad_ae_zero_of_energy_zero (h : ScalarCoeffOnData U a) (i : Fin d) {g : Vec d → Vec d}
    (hg : GradMemL2On (U : Set (Vec d)) g)
    (h0 : average U (fun x => a x * vecDot (g x) (g x)) = 0) :
    ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)), g x = 0 := by
  have hv := (volume_toReal_pos' U).ne'
  unfold average at h0
  have hI : ∫ x in (U : Set (Vec d)), a x * vecDot (g x) (g x) ∂volume = 0 := by
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd (inv_eq_zero.mp h1) hv
    · exact h1
  have hz := (integral_eq_zero_iff_of_nonneg_ae (energy_nonneg_ae h g)
    (integrable_energy h i hg)).mp hI
  filter_upwards [hz, a_pos_ae h] with x hx hax
  have : vecDot (g x) (g x) = 0 := by
    have hx' : a x * vecDot (g x) (g x) = 0 := hx
    rcases mul_eq_zero.mp hx' with h1 | h1
    · exact absurd h1 hax.ne'
    · exact h1
  exact vecNormSq_eq_zero this

theorem neumann_energy_eq (h : ScalarCoeffOnData U a) (q : Vec d) (w : H1Function (U : Set (Vec d))) :
    symmetricNeumannEnergyValue U h.toCoeffOn q w =
      average U (fun x => vecDot q (w.grad x) - (1 / 2) * (a x * vecDot (w.grad x) (w.grad x))) := by
  unfold symmetricNeumannEnergyValue
  congr 1
  funext x
  rw [vecDot_scalar_coeff h x]

theorem dirichlet_energy_eq (h : ScalarCoeffOnData U a) (w : H1Function (U : Set (Vec d))) :
    symmetricDirichletEnergyValue U h.toCoeffOn w =
      (1 / 2) * average U (fun x => a x * vecDot (w.grad x) (w.grad x)) := by
  unfold symmetricDirichletEnergyValue
  rw [← average_const_mul']
  congr 1
  funext x
  rw [vecDot_scalar_coeff h x]

/-- The Neumann maximizer for `q = 0` has zero gradient. -/
theorem neumann_zero_grad (h : ScalarCoeffOnData U a) (i : Fin d)
    {uN : H1Function (U : Set (Vec d))} (hN : IsSymmetricNeumannMaximizer U h.toCoeffOn 0 uN) :
    ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)), uN.grad x = 0 := by
  have hT := responseSymmetricDirichletNeumannTheory U h.toCoeffOn (scalarCoeffOn_isSymmetric h)
  have hnu := hT.neumann_value_by_sigmaStarInv 0
  have hgr : IsGreatest (symmetricNeumannValueSet U h.toCoeffOn 0)
      (symmetricNeumannEnergyValue U h.toCoeffOn 0 uN) :=
    ⟨⟨uN, rfl⟩, by rintro E ⟨w, rfl⟩; exact hN w⟩
  have h1 : symmetricNeumannEnergyValue U h.toCoeffOn 0 uN = 0 := by
    have := hgr.csSup_eq
    unfold symmetricNeumannNu at hnu
    rw [this] at hnu
    rw [hnu]; simp [vecDot, matVecMul]
  rw [neumann_energy_eq h] at h1
  have e1 : (fun x => vecDot (0 : Vec d) (uN.grad x) -
      (1 / 2) * (a x * vecDot (uN.grad x) (uN.grad x))) =
      fun x => -((1 / 2) * (a x * vecDot (uN.grad x) (uN.grad x))) := by
    funext x; simp [vecDot]
  rw [e1, average_neg', average_const_mul'] at h1
  refine grad_ae_zero_of_energy_zero h i uN.gradMemL2 ?_
  linarith

/-- The Dirichlet minimizer for `p = 0` has zero gradient. -/
theorem dirichlet_zero_grad (h : ScalarCoeffOnData U a) (i : Fin d)
    {uD : H1Function (U : Set (Vec d))} (hD : IsSymmetricDirichletMinimizer U h.toCoeffOn 0 uD) :
    ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)), uD.grad x = 0 := by
  have hT := responseSymmetricDirichletNeumannTheory U h.toCoeffOn (scalarCoeffOn_isSymmetric h)
  have hnu := hT.dirichlet_value_by_sigma 0
  have hl : IsLeast (symmetricDirichletValueSet U h.toCoeffOn 0)
      (symmetricDirichletEnergyValue U h.toCoeffOn uD) :=
    ⟨⟨uD, hD.1, rfl⟩, by rintro E ⟨w, hw, rfl⟩; exact hD.2 w hw⟩
  have h1 : symmetricDirichletEnergyValue U h.toCoeffOn uD = 0 := by
    have := hl.csInf_eq
    unfold symmetricDirichletNu at hnu
    rw [this] at hnu
    rw [hnu]; simp [vecDot, matVecMul]
  rw [dirichlet_energy_eq h] at h1
  refine grad_ae_zero_of_energy_zero h i uD.gradMemL2 ?_
  linarith

end GMCExplicitDelta.Coarse
