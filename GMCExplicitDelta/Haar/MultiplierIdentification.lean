module

public import GMCExplicitDelta.Haar.MultiplierSobolev
public import GMCExplicitDelta.Haar.MultiplierEnergy

/-! Identification of the component tensor factors with the gradient and Hessian. -/
@[expose] public section

open Homogenization
open scoped BigOperators

namespace GMCExplicitDelta.Haar

variable {d : ℕ}

theorem tensorMultiplier_component (F : Fin d → ℝ → ℝ) (f t : Fin d → ℝ)
    (x : Vec d) (i : Fin d) (K : ℝ)
    (hF : ∀ j, F j (x j) = if j = i then K * t j else f j) :
    tensorMultiplier F x = K * productGradient f t i := by
  classical
  have hp : (∏ j ∈ Finset.univ.erase i, F j (x j)) = ∏ j ∈ Finset.univ.erase i, f j := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [hF, ite_eq_right (Finset.mem_erase.mp hj).1]
  unfold tensorMultiplier productGradient
  rw [← Finset.mul_prod_erase Finset.univ (fun j => F j (x j)) (Finset.mem_univ i),
    hF, ite_eq_left rfl, hp]
  ring

theorem tensorDerivative_component (F DF : Fin d → ℝ → ℝ) (f t a : Fin d → ℝ)
    (x : Vec d) (i j : Fin d) (K : ℝ)
    (hF : ∀ k, F k (x k) = if k = i then K * t k else f k)
    (hDF : ∀ k, DF k (x k) = if k = i then K ^ 2 * a k else K * t k) :
    tensorDerivative F DF x j = K ^ 2 * productHessian f t a i j := by
  classical
  unfold tensorDerivative productHessian
  by_cases hij : i = j
  · subst j
    rw [hDF, ite_eq_left rfl, ite_eq_left rfl]
    have hp : (∏ k ∈ Finset.univ.erase i, F k (x k)) = ∏ k ∈ Finset.univ.erase i, f k := by
      apply Finset.prod_congr rfl
      intro k hk
      rw [hF, ite_eq_right (Finset.mem_erase.mp hk).1]
    rw [hp]
    ring
  · have hji : j ≠ i := fun h => hij h.symm
    have hi : i ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩
    rw [hDF, ite_eq_right hji, ite_eq_right hij,
      ← Finset.mul_prod_erase _ (fun k => F k (x k)) hi, hF, ite_eq_left rfl]
    have hp : (∏ k ∈ (Finset.univ.erase j).erase i, F k (x k)) =
        ∏ k ∈ (Finset.univ.erase j).erase i, f k := by
      apply Finset.prod_congr rfl
      intro k hk
      rw [hF, ite_eq_right (Finset.mem_erase.mp hk).1]
    rw [hp, Finset.erase_right_comm]
    ring

theorem cutoffComponent_product_ids {ω S : ℝ} (hω0 : 0 < ω) (hS : S ≠ 0)
    (x : Vec d) (i : Fin d) :
    let κ := Real.pi / (2 * ω)
    let f := fun k => cutoffProfile ω (x k / S)
    let t := fun k => cutoffSlope ω (x k / S) / κ
    let a := fun k => cutoffCurvature ω (x k / S) / κ ^ 2
    tensorMultiplier (cutoffComponentFactors ω S i) x = (κ / S) * productGradient f t i ∧
      ∀ j, tensorDerivative (cutoffComponentFactors ω S i)
        (cutoffComponentFactorDerivs ω S i) x j = (κ / S) ^ 2 * productHessian f t a i j := by
  classical
  dsimp only
  let κ := Real.pi / (2 * ω)
  have hk : κ ≠ 0 := ne_of_gt (div_pos Real.pi_pos (mul_pos (by norm_num) hω0))
  have hF (k : Fin d) : cutoffComponentFactors ω S i k (x k) =
      if k = i then (κ / S) * (cutoffSlope ω (x k / S) / κ) else cutoffProfile ω (x k / S) := by
    simp only [cutoffComponentFactors, multiplierFactor, decide_eq_true_eq]
    split_ifs
    · field_simp [hk]
    · rfl
  have hDF (k : Fin d) : cutoffComponentFactorDerivs ω S i k (x k) =
      if k = i then (κ / S) ^ 2 * (cutoffCurvature ω (x k / S) / κ ^ 2)
      else (κ / S) * (cutoffSlope ω (x k / S) / κ) := by
    simp only [cutoffComponentFactorDerivs, multiplierFactorDeriv, decide_eq_true_eq]
    split_ifs <;> field_simp [hk, hS]
  exact ⟨tensorMultiplier_component _ _ _ x i (κ / S) hF,
    fun j => tensorDerivative_component _ _ _ _ _ x i j (κ / S) hF hDF⟩

/-- The sharp H7 bound holds pointwise wherever the coordinates lie in the cube. -/
theorem cutoffComponent_gradient_sq_le {ω S : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1 / 2)
    (hS : S ≠ 0) (x : Vec d) (hx : ∀ k, |x k / S| ≤ 1 / 2) (u : ℝ) (v : Vec d) :
    (∑ i, ∑ j, (tensorMultiplier (cutoffComponentFactors ω S i) x * v j +
      u * tensorDerivative (cutoffComponentFactors ω S i) (cutoffComponentFactorDerivs ω S i) x j) ^ 2) ≤
      (Real.pi / (2 * ω)) ^ 2 / S ^ 2 * (∑ j, v j ^ 2) +
        (d : ℝ) * (Real.pi / (2 * ω)) ^ 4 / S ^ 4 * u ^ 2 := by
  let κ := Real.pi / (2 * ω)
  let f := fun k => cutoffProfile ω (x k / S)
  let t := fun k => cutoffSlope ω (x k / S) / κ
  let a := fun k => cutoffCurvature ω (x k / S) / κ ^ 2
  have hf0 (k : Fin d) : 0 ≤ f k := (cutoffProfile_bounds hω0 hω1 (hx k)).1
  have hf1 (k : Fin d) : f k ≤ 1 := (cutoffProfile_bounds hω0 hω1 (hx k)).2
  have hr (k : Fin d) := cutoff_oscillator_relations hω0 (x k / S)
  have ht (k : Fin d) : t k ^ 2 = 1 - f k ^ 2 := by
    have hk : f k ^ 2 + t k ^ 2 = 1 := (hr k).1
    linarith only [hk]
  have hb := product_gradient_sq_sum_le f t a hf0 hf1 ht
    (fun k => (hr k).2.1) (fun k => (hr k).2.2) ((κ / S) ^ 2 * u) (fun j => (κ / S) * v j)
  have heq : (∑ i, ∑ j, (tensorMultiplier (cutoffComponentFactors ω S i) x * v j +
      u * tensorDerivative (cutoffComponentFactors ω S i) (cutoffComponentFactorDerivs ω S i) x j) ^ 2) =
      ∑ i, ∑ j, (((κ / S) * v j) * productGradient f t i +
        ((κ / S) ^ 2 * u) * productHessian f t a i j) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [(cutoffComponent_product_ids hω0 hS x i).1, (cutoffComponent_product_ids hω0 hS x i).2 j]
    ring
  rw [heq]
  refine hb.trans_eq ?_
  simp_rw [mul_pow]
  rw [← Finset.mul_sum]
  dsimp only [κ]
  ring

end GMCExplicitDelta.Haar
