module

public import GMCExplicitDelta.Coarse.CompetitorsScalar

/-!
# C12: the competitor inequality

`responseJ_le_competitor`: for scalar coefficients `a, a'` on `U`, a unit vector `e`, `v` a
response maximizer for `(e,0)` and `u` one for `(0,e)` (for `a`),
`J(U,e,e;a') ≤ ½ avg_U (a' |∇v|² + a'⁻¹ a² |∇u|²) - 1`.

The Dirichlet competitor is `-v` (the Dirichlet minimizer up to sign), the dual competitor is the
flux `a ∇u`, which is solenoidal with zero normal flux because `u` is the Neumann maximizer.
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

variable {d : ℕ} {U : Domain d} {a a' : Vec d → ℝ}

theorem eq_zero_of_forall_le {L Q : ℝ} (hQ : 0 ≤ Q)
    (h : ∀ t : ℝ, t * L - (t ^ 2 / 2) * Q ≤ 0) : L = 0 := by
  by_contra hL
  have h1 := h (L / (Q + 1))
  have hQ1 : 0 < Q + 1 := by linarith
  have e : (L / (Q + 1)) * L - ((L / (Q + 1)) ^ 2 / 2) * Q =
      L ^ 2 * (Q + 2) / (2 * (Q + 1) ^ 2) := by
    field_simp
    ring
  have : 0 < L ^ 2 * (Q + 2) / (2 * (Q + 1) ^ 2) := by
    have : 0 < L ^ 2 := by positivity
    positivity
  linarith

/-- Euler-Lagrange equation of the Neumann maximizer (scalar coefficient). -/
theorem neumann_euler_lagrange (h : ScalarCoeffOnData U a) (i : Fin d) (q : Vec d)
    {uN : H1Function (U : Set (Vec d))} (hN : IsSymmetricNeumannMaximizer U h.toCoeffOn q uN)
    (φ : H1Function (U : Set (Vec d))) :
    average U (fun x => vecDot q (φ.grad x)) =
      average U (fun x => a x * vecDot (φ.grad x) (uN.grad x)) := by
  have hg : GradMemL2On (U : Set (Vec d)) uN.grad := uN.gradMemL2
  have hγ : GradMemL2On (U : Set (Vec d)) φ.grad := φ.gradMemL2
  have iF : Integrable (fun x => vecDot q (uN.grad x)) (volumeMeasureOn (U : Set (Vec d))) :=
    integrable_vecDot_const q (integrable_grad_comp hg)
  have iG : Integrable (fun x => a x * vecDot (uN.grad x) (uN.grad x))
      (volumeMeasureOn (U : Set (Vec d))) := integrable_energy h i hg
  have iH : Integrable (fun x => vecDot q (φ.grad x)) (volumeMeasureOn (U : Set (Vec d))) :=
    integrable_vecDot_const q (integrable_grad_comp hγ)
  have iK : Integrable (fun x => a x * vecDot (φ.grad x) (uN.grad x))
      (volumeMeasureOn (U : Set (Vec d))) :=
    integrable_a_mul h i (integrable_dot_grad hγ hg)
  have iQ : Integrable (fun x => a x * vecDot (φ.grad x) (φ.grad x))
      (volumeMeasureOn (U : Set (Vec d))) := integrable_energy h i hγ
  have key : ∀ t : ℝ,
      t * (average U (fun x => vecDot q (φ.grad x)) -
          average U (fun x => a x * vecDot (φ.grad x) (uN.grad x))) -
        (t ^ 2 / 2) * average U (fun x => a x * vecDot (φ.grad x) (φ.grad x)) ≤ 0 := by
    intro t
    have hmax := hN (uN + t • φ)
    rw [neumann_energy_eq h, neumann_energy_eq h] at hmax
    have hmax' : average U (fun x => vecDot q (uN.grad x + t • φ.grad x) -
        (1 / 2) * (a x * vecDot (uN.grad x + t • φ.grad x) (uN.grad x + t • φ.grad x))) ≤
        average U (fun x => vecDot q (uN.grad x) -
          (1 / 2) * (a x * vecDot (uN.grad x) (uN.grad x))) := hmax
    have e1 : (fun x => vecDot q (uN.grad x + t • φ.grad x) -
        (1 / 2) * (a x * vecDot (uN.grad x + t • φ.grad x) (uN.grad x + t • φ.grad x))) =
        fun x => (vecDot q (uN.grad x) - (1 / 2) * (a x * vecDot (uN.grad x) (uN.grad x))) +
          (t * (vecDot q (φ.grad x) - a x * vecDot (φ.grad x) (uN.grad x)) -
            (t ^ 2 / 2) * (a x * vecDot (φ.grad x) (φ.grad x))) := by
      funext x
      have hc : uN.grad x ⬝ᵥ φ.grad x = φ.grad x ⬝ᵥ uN.grad x := dotProduct_comm _ _
      simp only [vecDot_eq_dotProduct, dotProduct_add, add_dotProduct, dotProduct_smul,
        smul_dotProduct, smul_eq_mul, hc]
      ring
    have iP0 : Integrable (fun x => vecDot q (uN.grad x) -
        (1 / 2) * (a x * vecDot (uN.grad x) (uN.grad x)))
        (volumeMeasureOn (U : Set (Vec d))) := iF.sub (iG.const_mul _)
    have iHK : Integrable (fun x => vecDot q (φ.grad x) - a x * vecDot (φ.grad x) (uN.grad x))
        (volumeMeasureOn (U : Set (Vec d))) := iH.sub iK
    have iT : Integrable (fun x => t * (vecDot q (φ.grad x) -
        a x * vecDot (φ.grad x) (uN.grad x))) (volumeMeasureOn (U : Set (Vec d))) :=
      iHK.const_mul t
    have iQ' : Integrable (fun x => (t ^ 2 / 2) * (a x * vecDot (φ.grad x) (φ.grad x)))
        (volumeMeasureOn (U : Set (Vec d))) := iQ.const_mul _
    have iR : Integrable (fun x => t * (vecDot q (φ.grad x) -
        a x * vecDot (φ.grad x) (uN.grad x)) -
        (t ^ 2 / 2) * (a x * vecDot (φ.grad x) (φ.grad x)))
        (volumeMeasureOn (U : Set (Vec d))) := iT.sub iQ'
    rw [e1, average_add' iP0 iR, average_sub' iT iQ', average_const_mul', average_const_mul',
      average_sub' iH iK] at hmax'
    linarith
  have hL := eq_zero_of_forall_le (average_nonneg' (energy_nonneg_ae h φ.grad)) key
  linarith

theorem integrable_ainv_a_sq (h : ScalarCoeffOnData U a) (h' : ScalarCoeffOnData U a')
    (i : Fin d) {g : Vec d → Vec d} (hg : GradMemL2On (U : Set (Vec d)) g) :
    Integrable (fun x => (a' x)⁻¹ * (a x ^ 2 * vecDot (g x) (g x)))
      (volumeMeasureOn (U : Set (Vec d))) := by
  have := integrable_ainv_mul h' i (integrable_a_mul h i (integrable_energy h i hg))
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  show (a' x)⁻¹ * (a x * (a x * vecDot (g x) (g x))) = (a' x)⁻¹ * (a x ^ 2 * vecDot (g x) (g x))
  ring

/-- The Dirichlet competitor: `e·X_U(a') e ≤ avg a' |∇v|²`. -/
theorem qf_XU_le_average_energy (h : ScalarCoeffOnData U a) (h' : ScalarCoeffOnData U a')
    (i : Fin d) {e : Vec d} {v : Solution U h.toCoeffOn}
    (hv : IsResponseMaximizer U h.toCoeffOn e 0 v) :
    qf (XU U h'.toCoeffOn) e ≤
      average U (fun x => a' x * vecDot (v.toH1.grad x) (v.toH1.grad x)) := by
  have hT := responseSymmetricDirichletNeumannTheory U h.toCoeffOn (scalarCoeffOn_isSymmetric h)
  have hT' := responseSymmetricDirichletNeumannTheory U h'.toCoeffOn
    (scalarCoeffOn_isSymmetric h')
  obtain ⟨uD, hD⟩ := hT.dirichlet_minimizer_exists e
  obtain ⟨uN, -, hN⟩ := hT.neumann_meanZero_maximizer_exists 0
  have hsplit := hT.response_maximizer_split e 0 v hv uD uN hD hN
  have hz := neumann_zero_grad h i hN
  have hgv : ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)), v.toH1.grad x = -uD.grad x := by
    filter_upwards [hsplit, hz] with x hx hz'
    rw [hx, hz', zero_sub]
  have hnu := hT'.dirichlet_value_by_sigma e
  have hle : symmetricDirichletNu U h'.toCoeffOn e ≤
      symmetricDirichletEnergyValue U h'.toCoeffOn uD := by
    unfold symmetricDirichletNu
    refine csInf_le ⟨0, ?_⟩ ⟨uD, hD.1, rfl⟩
    rintro E ⟨w, -, rfl⟩
    rw [dirichlet_energy_eq h']
    exact mul_nonneg (by norm_num) (average_nonneg' (energy_nonneg_ae h' _))
  rw [dirichlet_energy_eq h', hnu] at hle
  have hcongr : average U (fun x => a' x * vecDot (v.toH1.grad x) (v.toH1.grad x)) =
      average U (fun x => a' x * vecDot (uD.grad x) (uD.grad x)) := by
    refine average_congr_ae (hgv.mono fun x hx => ?_)
    simp only [hx, vecDot_eq_dotProduct, neg_dotProduct, dotProduct_neg, neg_neg]
  rw [hcongr, XU_eq_sigma (scalarCoeffOn_isSymmetric h')]
  have : vecDot e (matVecMul (sigmaCoarse U h'.toCoeffOn) e) =
      qf (sigmaCoarse U h'.toCoeffOn) e := rfl
  linarith

/-- The dual competitor: `e·Y_U(a') e ≤ avg a'⁻¹ a² |∇u|²`. -/
theorem qf_YU_le_average_energy (h : ScalarCoeffOnData U a) (h' : ScalarCoeffOnData U a')
    (i : Fin d) {e : Vec d} {u : Solution U h.toCoeffOn}
    (hu : IsResponseMaximizer U h.toCoeffOn 0 e u) :
    qf (YU U h'.toCoeffOn) e ≤
      average U (fun x => (a' x)⁻¹ * (a x ^ 2 * vecDot (u.toH1.grad x) (u.toH1.grad x))) := by
  have hT := responseSymmetricDirichletNeumannTheory U h.toCoeffOn (scalarCoeffOn_isSymmetric h)
  have hT' := responseSymmetricDirichletNeumannTheory U h'.toCoeffOn
    (scalarCoeffOn_isSymmetric h')
  obtain ⟨uD, hD⟩ := hT.dirichlet_minimizer_exists 0
  obtain ⟨uN, -, hN⟩ := hT.neumann_meanZero_maximizer_exists e
  have hsplit := hT.response_maximizer_split 0 e u hu uD uN hD hN
  have hz := dirichlet_zero_grad h i hD
  have hgu : ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)), u.toH1.grad x = uN.grad x := by
    filter_upwards [hsplit, hz] with x hx hz'
    rw [hx, hz', sub_zero]
  have EL := neumann_euler_lagrange h i e hN
  have hnu := hT'.neumann_value_by_sigmaStarInv e
  have hY : sigmaStarInvCoarse U h'.toCoeffOn = YU U h'.toCoeffOn :=
    (YU_eq_sigmaStarInv (scalarCoeffOn_isSymmetric h')).symm
  have hcongr : average U (fun x => (a' x)⁻¹ * (a x ^ 2 * vecDot (u.toH1.grad x) (u.toH1.grad x))) =
      average U (fun x => (a' x)⁻¹ * (a x ^ 2 * vecDot (uN.grad x) (uN.grad x))) := by
    refine average_congr_ae (hgu.mono fun x hx => ?_)
    simp only [hx]
  have iM := integrable_ainv_a_sq h h' i uN.gradMemL2
  have hbound : symmetricNeumannNu U h'.toCoeffOn e ≤
      (1 / 2) * average U (fun x => (a' x)⁻¹ * (a x ^ 2 * vecDot (uN.grad x) (uN.grad x))) := by
    unfold symmetricNeumannNu
    refine csSup_le ⟨_, ⟨0, rfl⟩⟩ ?_
    rintro E ⟨w, rfl⟩
    rw [neumann_energy_eq h']
    have iw1 : Integrable (fun x => vecDot e (w.grad x)) (volumeMeasureOn (U : Set (Vec d))) :=
      integrable_vecDot_const e (integrable_grad_comp w.gradMemL2)
    have iw2 : Integrable (fun x => (1 / 2) * (a' x * vecDot (w.grad x) (w.grad x)))
        (volumeMeasureOn (U : Set (Vec d))) :=
      (integrable_energy h' i w.gradMemL2).const_mul _
    have iK : Integrable (fun x => a x * vecDot (w.grad x) (uN.grad x))
        (volumeMeasureOn (U : Set (Vec d))) :=
      integrable_a_mul h i (integrable_dot_grad w.gradMemL2 uN.gradMemL2)
    have iKd : Integrable (fun x => a x * vecDot (w.grad x) (uN.grad x) -
        (1 / 2) * (a' x * vecDot (w.grad x) (w.grad x)))
        (volumeMeasureOn (U : Set (Vec d))) := iK.sub iw2
    have iMh : Integrable (fun x => (1 / 2) * ((a' x)⁻¹ *
        (a x ^ 2 * vecDot (uN.grad x) (uN.grad x)))) (volumeMeasureOn (U : Set (Vec d))) :=
      iM.const_mul _
    rw [average_sub' iw1 iw2, EL w, ← average_sub' iK iw2, ← average_const_mul']
    refine average_mono' iKd iMh ?_
    filter_upwards [a_pos_ae h'] with x hP
    set P := a' x with hPdef
    set g := uN.grad x
    set γ := w.grad x
    have hP0 : P ≠ 0 := hP.ne'
    have hsq := vecNormSq_nonneg (a x • g - P • γ)
    have hc : g ⬝ᵥ γ = γ ⬝ᵥ g := dotProduct_comm _ _
    have hsq' : 0 ≤ a x ^ 2 * (g ⬝ᵥ g) - 2 * a x * P * (γ ⬝ᵥ g) + P ^ 2 * (γ ⬝ᵥ γ) := by
      have : vecNormSq (a x • g - P • γ) =
          a x ^ 2 * (g ⬝ᵥ g) - 2 * a x * P * (γ ⬝ᵥ g) + P ^ 2 * (γ ⬝ᵥ γ) := by
        simp only [vecNormSq, vecDot_eq_dotProduct, sub_dotProduct, dotProduct_sub,
          smul_dotProduct, dotProduct_smul, smul_eq_mul, hc]
        ring
      linarith
    have key : (1 / 2) * (P⁻¹ * (a x ^ 2 * vecDot g g)) -
        (a x * vecDot γ g - (1 / 2) * (P * vecDot γ γ)) =
        (1 / 2) * P⁻¹ * (a x ^ 2 * (g ⬝ᵥ g) - 2 * a x * P * (γ ⬝ᵥ g) + P ^ 2 * (γ ⬝ᵥ γ)) := by
      simp only [vecDot_eq_dotProduct]
      field_simp
      ring
    have : 0 ≤ (1 / 2) * P⁻¹ *
        (a x ^ 2 * (g ⬝ᵥ g) - 2 * a x * P * (γ ⬝ᵥ g) + P ^ 2 * (γ ⬝ᵥ γ)) :=
      mul_nonneg (by positivity) hsq'
    show a x * vecDot γ g - (1 / 2) * (P * vecDot γ γ) ≤ (1 / 2) * (P⁻¹ * (a x ^ 2 * vecDot g g))
    linarith
  rw [hnu, hY] at hbound
  rw [hcongr]
  have : vecDot e (matVecMul (YU U h'.toCoeffOn) e) = qf (YU U h'.toCoeffOn) e := rfl
  linarith

/-- C12: the competitor inequality
`J(U,e,e;a') ≤ ½ avg (a' |∇v|² + a'⁻¹ a² |∇u|²) - 1`. -/
theorem responseJ_le_competitor (h : ScalarCoeffOnData U a) (h' : ScalarCoeffOnData U a')
    {e : Vec d} (he : e ⬝ᵥ e = 1) {v u : Solution U h.toCoeffOn}
    (hv : IsResponseMaximizer U h.toCoeffOn e 0 v)
    (hu : IsResponseMaximizer U h.toCoeffOn 0 e u) :
    responseJ U h'.toCoeffOn e e ≤
      (1 / 2) * average U (fun x => a' x * vecDot (v.toH1.grad x) (v.toH1.grad x) +
        (a' x)⁻¹ * (a x ^ 2 * vecDot (u.toH1.grad x) (u.toH1.grad x))) - 1 := by
  obtain ⟨i⟩ := nonempty_fin_of_dot_one he
  rw [responseJ_eq_XY (scalarCoeffOn_isSymmetric h'), he]
  have h1 := qf_XU_le_average_energy h h' i hv
  have h2 := qf_YU_le_average_energy h h' i hu
  rw [average_add' (integrable_energy h' i v.toH1.gradMemL2)
    (integrable_ainv_a_sq h h' i u.toH1.gradMemL2)]
  linarith

end GMCExplicitDelta.Coarse
