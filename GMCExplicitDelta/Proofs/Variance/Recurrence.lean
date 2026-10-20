module

public import GMCExplicitDelta.Proofs.Variance.CenteredTrace
public import GMCExplicitDelta.Proofs.Variance.Family
public import GMCExplicitDelta.Proofs.Variance.DecrementAlgebra

/-! # Abstract two-channel centered decrement recurrence -/

@[expose] public section

open MeasureTheory Matrix Homogenization Homogenization.Book

namespace GMCExplicitDelta.Assembly

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem frozenVar_frobSq_neg (A : Homogenization.Mat d) : frobSq (-A) = frobSq A := by
  simp only [frobSq, Matrix.neg_apply, neg_sq]

/-- The two-channel L2 recurrence, before the common dimension normalization. -/
theorem frozenVar_two_channel_recurrence (X B : Fin 2 → Ω → Homogenization.Mat d)
    (a b : Fin 2 → ℝ) (Z : Ω → Homogenization.Mat d) (f g C t : ℝ)
    (hX : ∀ r i j, MemLp (fun ω => X r ω i j) 2 μ)
    (hB : ∀ r i j, MemLp (fun ω => B r ω i j) 2 μ)
    (hZ : ∀ i j, MemLp (fun ω => Z ω i j) 2 μ)
    (hTD : ∀ r, Integrable (fun ω => Matrix.trace (B r ω - X r ω)) μ)
    (hTZ : Integrable (fun ω => Matrix.trace (Z ω)) μ)
    (hmeanD : ∀ r, (∫ ω, Matrix.trace (B r ω - X r ω) ∂μ) = (d : ℝ) * (b r - a r))
    (hmeanZ : (∫ ω, Matrix.trace (Z ω) ∂μ) = 0)
    (hcenters : (∑ r, (b r - a r)) = 2 * (g - f))
    (hp : ∀ r ω, frobSq (B r ω - X r ω) ≤
      2 * frozenVar_matrixPair (B r ω - X r ω) (Z ω + g • 1))
    (hcapB : (∑ r, ∫ ω, frobSq (B r ω - b r • 1) ∂μ) ≤ C)
    (hcapZ : 2 * (∫ ω, frobSq (Z ω) ∂μ) ≤ C)
    (hC : 0 ≤ C) (hgap : 0 ≤ g ^ 2 - f ^ 2) (ht : 0 < t) :
    (∑ r, ∫ ω, frobSq (X r ω - a r • 1) ∂μ) ≤
      (5 + 2 * (t + t⁻¹)) * C + (1 + 2 / t) * ((2 * (d : ℝ)) * (g ^ 2 - f ^ 2)) := by
  let Dc : Fin 2 → Ω → Homogenization.Mat d :=
    fun r ω => (B r ω - X r ω) - (b r - a r) • 1
  let Bc : Fin 2 → Ω → Homogenization.Mat d := fun r ω => B r ω - b r • 1
  let Q : ℝ := ∑ r, ∫ ω, frobSq (Dc r ω) ∂μ
  let V : ℝ := ∑ r, ∫ ω, frobSq (X r ω - a r • 1) ∂μ
  have hDc (r : Fin 2) (i j : Fin d) : MemLp (fun ω => Dc r ω i j) 2 μ :=
    ((hB r i j).sub (hX r i j)).sub (memLp_const _)
  have hBc (r : Fin 2) (i j : Fin d) : MemLp (fun ω => Bc r ω i j) 2 μ :=
    (hB r i j).sub (memLp_const _)
  have hQ : 0 ≤ Q := Finset.sum_nonneg fun r _ => integral_nonneg fun ω => frobSq_nonneg _
  have hV : 0 ≤ V := Finset.sum_nonneg fun r _ => integral_nonneg fun ω => frobSq_nonneg _
  have hsingle (r : Fin 2) := frozenVar_centered_trace_decrement (D := fun ω => B r ω - X r ω) (Z := Z)
    (fun i j => (hB r i j).sub (hX r i j)) hZ (hTD r) hTZ (b r - a r) g
    (hmeanD r) hmeanZ (hp r)
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 2))) (fun r _ => hsingle r)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hdelta : 2 * (g - f) ^ 2 ≤ ∑ r, (b r - a r) ^ 2 := by
    rw [Fin.sum_univ_two] at hcenters ⊢
    have heq := congrArg (fun x : ℝ => x ^ 2) hcenters
    nlinarith only [heq, sq_nonneg ((b 0 - a 0) - (b 1 - a 1))]
  have hcross := frozenVar_family_pair_le (A := Dc) (B := fun _ => Z) hDc (fun _ i j => hZ i j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hcross
  have hcross' : (∑ r, ∫ ω, frozenVar_matrixPair (Dc r ω) (Z ω) ∂μ) ≤ Real.sqrt Q * Real.sqrt C := by
    exact hcross.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcapZ) (Real.sqrt_nonneg Q))
  have hQbound : Q ≤ (2 * (d : ℝ)) * (g ^ 2 - f ^ 2) + 2 * Real.sqrt Q * Real.sqrt C := by
    have hdim : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hmeansq := mul_le_mul_of_nonneg_left hdelta hdim
    change Q + (d : ℝ) * (∑ r, (b r - a r) ^ 2) ≤
      2 * g * ((d : ℝ) * ∑ r, (b r - a r)) +
        2 * ∑ r, ∫ ω, frozenVar_matrixPair (Dc r ω) (Z ω) ∂μ at hsum
    rw [hcenters] at hsum
    nlinarith only [hsum, hmeansq, hcross']
  have htri := frozenVar_family_triangle (A := Bc) (B := fun r ω => -(Dc r ω)) hBc (fun r i j => (hDc r i j).neg)
  have hident (r : Fin 2) (ω : Ω) : Bc r ω + -(Dc r ω) = X r ω - a r • 1 := by
    dsimp only [Bc, Dc]
    module
  simp only [hident, frozenVar_frobSq_neg] at htri
  have htri' : Real.sqrt V ≤ Real.sqrt C + Real.sqrt Q := by
    exact htri.trans (add_le_add (Real.sqrt_le_sqrt hcapB) (le_refl _))
  have hscalar := frozenVar_centered_decrement_algebra hC (mul_nonneg (by positivity) hgap) hV ht
    (show (Real.sqrt Q) ^ 2 ≤ (2 * (d : ℝ)) * (g ^ 2 - f ^ 2) + 2 * Real.sqrt Q * Real.sqrt C by
      rw [Real.sq_sqrt hQ]; exact hQbound) htri'
  exact hscalar

end GMCExplicitDelta.Assembly
