module

public import GMCExplicitDelta.Haar.CutoffProduct

/-! A pointwise tensor contraction giving the sharp H7 multiplier inequality. -/
@[expose] public section

open scoped BigOperators

namespace GMCExplicitDelta.Haar

/-- The two combinations in a column of the product rule form a contraction.
On a cosine layer they are an orthogonal rotation; on the plateau its slope
and curvature both vanish. -/
theorem oscillator_pair_le {f t a u v : ℝ}
    (hft : f ^ 2 + t ^ 2 ≤ 1) (hat : a ^ 2 + t ^ 2 ≤ 1)
    (hcross : t * (a + f) = 0) :
    (t * v + a * u) ^ 2 + (f * v + t * u) ^ 2 ≤ v ^ 2 + u ^ 2 := by
  have hv := mul_le_mul_of_nonneg_right hft (sq_nonneg v)
  have hu := mul_le_mul_of_nonneg_right hat (sq_nonneg u)
  have hc : 2 * u * v * (t * (a + f)) = 0 := by rw [hcross, mul_zero]
  nlinarith only [hv, hu, hc]

/-- Tensor factors outside the selected coordinate contribute at most one to
each of the two squared oscillator combinations. -/
theorem tensor_column_le {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f t : ι → ℝ) (hf0 : ∀ i ∈ s, 0 ≤ f i) (hf1 : ∀ i ∈ s, f i ≤ 1)
    (ht : ∀ i ∈ s, t i ^ 2 = 1 - f i ^ 2)
    {fj tj aj u v : ℝ} (hft : fj ^ 2 + tj ^ 2 ≤ 1)
    (hat : aj ^ 2 + tj ^ 2 ≤ 1) (hcross : tj * (aj + fj) = 0) :
    ((∏ i ∈ s, f i) * (tj * v + aj * u)) ^ 2 +
      (∑ i ∈ s, (t i * ∏ k ∈ s.erase i, f k) ^ 2) * (fj * v + tj * u) ^ 2 ≤
      v ^ 2 + u ^ 2 := by
  have hp : (∏ i ∈ s, f i) ^ 2 ≤ 1 := by
    have h0 := Finset.prod_nonneg hf0
    have h1 := Finset.prod_le_one₀ hf0 hf1
    exact pow_le_one₀ h0 h1
  have hb : (∑ i ∈ s, (t i * ∏ k ∈ s.erase i, f k) ^ 2) ≤ 1 := by
    simp_rw [mul_pow, ← Finset.prod_pow]
    have he : (∑ i ∈ s, t i ^ 2 * ∏ k ∈ s.erase i, f k ^ 2) =
        ∑ i ∈ s, (1 - f i ^ 2) * ∏ k ∈ s.erase i, f k ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [ht i hi]
    rw [he]
    exact one_failure_le_one s (fun i => f i ^ 2) (fun _ _ => sq_nonneg _)
      (fun i hi => pow_le_one₀ (hf0 i hi) (hf1 i hi))
  calc
    _ ≤ (tj * v + aj * u) ^ 2 + (fj * v + tj * u) ^ 2 := by
      rw [mul_pow]
      exact add_le_add
        ((mul_le_mul_of_nonneg_right hp (sq_nonneg _)).trans_eq (one_mul _))
        ((mul_le_mul_of_nonneg_right hb (sq_nonneg _)).trans_eq (one_mul _))
    _ ≤ _ := oscillator_pair_le hft hat hcross

noncomputable def productGradient {d : ℕ} (f t : Fin d → ℝ) (i : Fin d) : ℝ :=
  t i * ∏ k ∈ Finset.univ.erase i, f k

noncomputable def productHessian {d : ℕ} (f t a : Fin d → ℝ) (i j : Fin d) : ℝ :=
  if i = j then a i * ∏ k ∈ Finset.univ.erase i, f k
  else t i * t j * ∏ k ∈ (Finset.univ.erase i).erase j, f k

/-- The product-rule column is a contraction, with no integration by parts. -/
theorem product_column_le {d : ℕ} (f t a : Fin d → ℝ)
    (hf0 : ∀ i, 0 ≤ f i) (hf1 : ∀ i, f i ≤ 1)
    (ht : ∀ i, t i ^ 2 = 1 - f i ^ 2)
    (ha : ∀ i, a i ^ 2 + t i ^ 2 ≤ 1)
    (hc : ∀ i, t i * (a i + f i) = 0) (j : Fin d) (u v : ℝ) :
    (∑ i, (v * productGradient f t i + u * productHessian f t a i j) ^ 2) ≤ v ^ 2 + u ^ 2 := by
  classical
  have hoff (i : Fin d) (hi : i ∈ Finset.univ.erase j) :
      v * productGradient f t i + u * productHessian f t a i j =
        (t i * ∏ k ∈ (Finset.univ.erase j).erase i, f k) * (f j * v + t j * u) := by
    have hij : i ≠ j := (Finset.mem_erase.mp hi).1
    have hji : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
    unfold productGradient productHessian
    rw [ite_eq_right hij, ← Finset.mul_prod_erase _ f hji, Finset.erase_right_comm]
    ring
  have heq : (∑ i, (v * productGradient f t i + u * productHessian f t a i j) ^ 2) =
      ((∏ k ∈ Finset.univ.erase j, f k) * (t j * v + a j * u)) ^ 2 +
        (∑ i ∈ Finset.univ.erase j, (t i * ∏ k ∈ (Finset.univ.erase j).erase i, f k) ^ 2) *
          (f j * v + t j * u) ^ 2 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    congr 1
    · unfold productGradient productHessian
      rw [ite_eq_left rfl]
      ring
    · rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hoff i hi, mul_pow]
  rw [heq]
  apply tensor_column_le _ f t (fun i _ => hf0 i) (fun i _ => hf1 i) (fun i _ => ht i)
  · rw [ht j]
    exact le_of_eq (by ring)
  · exact ha j
  · exact hc j

/-- Sharp pointwise H7 bound for a tensor of oscillators. -/
theorem product_gradient_sq_sum_le {d : ℕ} (f t a : Fin d → ℝ)
    (hf0 : ∀ i, 0 ≤ f i) (hf1 : ∀ i, f i ≤ 1)
    (ht : ∀ i, t i ^ 2 = 1 - f i ^ 2)
    (ha : ∀ i, a i ^ 2 + t i ^ 2 ≤ 1)
    (hc : ∀ i, t i * (a i + f i) = 0) (u : ℝ) (v : Fin d → ℝ) :
    (∑ i, ∑ j, (v j * productGradient f t i + u * productHessian f t a i j) ^ 2) ≤
      (∑ j, v j ^ 2) + (d : ℝ) * u ^ 2 := by
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ j, (v j ^ 2 + u ^ 2) :=
      Finset.sum_le_sum (fun j _ => product_column_le f t a hf0 hf1 ht ha hc j u (v j))
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end GMCExplicitDelta.Haar
