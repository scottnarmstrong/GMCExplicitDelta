module

public import GMCExplicitDelta.Proofs.FineSensitivity.Sensitivity

/-! # The old-competitor energy budgets in G3 -/

@[expose] public section

open MeasureTheory Homogenization.Book.Ch02
open Homogenization (vecNormSq vecDot matVecMul volumeMeasureOn GradMemL2On)
open SubdiffusiveProcess.CoarseGrainingVocab

namespace GMCExplicitDelta.Assembly

/-- The difference-gradient energy is the sum-gradient energy plus the cross correction. -/
theorem fine_vecNormSq_sub {d : ℕ} (v u : Homogenization.Vec d) :
    vecNormSq (v - u) = vecNormSq (v + u) - 4 * vecDot u v := by
  unfold vecNormSq vecDot
  simp only [Pi.sub_apply, Pi.add_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The old competitors supply the precise spatial energy budgets for G3. -/
theorem fine_old_energy_budgets {d : ℕ} {U : Domain d} {a : Homogenization.Vec d → ℝ}
    (h : ScalarCoeffOnData U a) {e : Homogenization.Vec d} (he : e ⬝ᵥ e = 1)
    {v u : Solution U h.toCoeffOn}
    (hv : IsResponseMaximizer U h.toCoeffOn e 0 v)
    (hu : IsResponseMaximizer U h.toCoeffOn 0 e u) :
    average U (fun x => a x * vecNormSq (v.toH1.grad x - u.toH1.grad x)) =
        2 * responseJ U h.toCoeffOn e e + 4 ∧
      (1 / 2 : ℝ) * average U (fun x => a x * vecNormSq (u.toH1.grad x)) ≤
        responseJ U h.toCoeffOn e e + 1 := by
  obtain ⟨i⟩ := Coarse.nonempty_fin_of_dot_one he
  have hSym := Coarse.scalarCoeffOn_isSymmetric h
  have hsum := Coarse.half_average_energy_sum hSym hv hu
  have hcross := Coarse.average_cross hSym he hv hu
  have hE := Coarse.average_energy_u hSym hu
  simp_rw [Coarse.vecDot_scalar_coeff h] at hsum hE
  simp_rw [Coarse.matVecMul_scalar_coeff h, Homogenization.vecDot_smul_right] at hcross
  have hC := Coarse.integrable_a_mul h i
    (Coarse.integrable_dot_grad u.toH1.gradMemL2 v.toH1.gradMemL2)
  have hD : GradMemL2On (U : Set (Homogenization.Vec d))
      (fun x => v.toH1.grad x + u.toH1.grad x) :=
    fun j => (v.toH1.gradMemL2 j).add (u.toH1.gradMemL2 j)
  have hDI := Coarse.integrable_energy h i hD
  constructor
  · have heq : (fun x => a x * vecNormSq (v.toH1.grad x - u.toH1.grad x)) =
        (fun x => a x * vecNormSq (v.toH1.grad x + u.toH1.grad x) -
          4 * (a x * vecDot (u.toH1.grad x) (v.toH1.grad x))) := by
      funext x
      rw [fine_vecNormSq_sub]
      ring
    rw [heq]
    dsimp only [vecNormSq]
    rw [Coarse.average_sub' hDI (hC.const_mul 4), Coarse.average_const_mul', hcross]
    linarith only [hsum]
  · dsimp only [vecNormSq]
    rw [hE, Coarse.responseJ_eq_XY hSym, he]
    have hX : 0 ≤ Coarse.qf (Coarse.XU U h.toCoeffOn) e :=
      (Coarse.XU_posDef hSym).posSemidef.dotProduct_mulVec_nonneg e
    linarith only [hX]

end GMCExplicitDelta.Assembly
