module

public import GMCExplicitDelta.Proofs.PlanarBlock.Spectral

/-! Summation of a Neumann spectral estimate with finitely many exceptional modes. -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization

namespace GMCExplicitDelta.Localization

variable {d : ℕ}

/-- A uniform spectral cutoff plus finitely many low-mode corrections. -/
theorem planarBlock_neumann_finite_correction (Q : TriadicCube d) {G : Vec d → Vec d}
    (hG : ∀ j, MemLp (fun x => G x j) 2 (normalizedCubeMeasure Q))
    {w : H1Function (openCubeSet Q)} (hw : IsNeumannPrimitive Q G w)
    (E : Finset (Fin d → ℤ)) (e : (Fin d → ℤ) → ℝ) {a : ℝ}
    (ha : 0 ≤ a) (he : ∀ p ∈ E, 0 ≤ e p)
    (hgap : ∀ p : Fin d → ℤ, p ≠ 0 →
      1 ≤ (a + if p ∈ E then e p else 0) * Haar.cubeEig Q p) :
    Haar.energy Q w.toFun ≤ a * vecEnergy Q G +
      ∑ p ∈ E, e p * ∑ j,
        (∫ x, Haar.cubeSin Q j p x * G x j ∂normalizedCubeMeasure Q) ^ 2 := by
  classical
  let c := fun p => ∫ x, Haar.cubeCos Q p x * w.toFun x ∂normalizedCubeMeasure Q
  let s := fun j p => ∫ x, Haar.cubeSin Q j p x * G x j ∂normalizedCubeMeasure Q
  let S := fun p => ∑ j, s j p ^ 2
  have hSi : ∀ j, Summable (fun p => s j p ^ 2) := by
    intro j
    have h := Haar.Torus.summable_sq_boxCoeff (Haar.cubeCorner Q)
      (Haar.cubeScaleFactor_pos' Q) {j}
      (show MemLp (fun x => G x j) 2
        (Haar.Torus.boxMeasure (Haar.cubeCorner Q) (cubeScaleFactor Q)) from by
        rw [Haar.boxMeasure_eq_normalizedCubeMeasure]
        exact hG j)
    rw [Haar.boxMeasure_eq_normalizedCubeMeasure] at h
    exact h
  have hS : HasSum S (∑ j, ∑' p, s j p ^ 2) :=
    hasSum_sum fun j _ => (hSi j).hasSum
  have hE : HasSum (fun p => if p ∈ E then e p * S p else 0)
      (∑ p ∈ E, e p * S p) := by
    have h : HasSum (fun p => if p ∈ E then e p * S p else 0)
        (∑ p ∈ E, if p ∈ E then e p * S p else 0) :=
      hasSum_sum_of_ne_finset_zero (s := E)
      (f := fun p => if p ∈ E then e p * S p else 0)
      (fun p hp => ite_eq_right hp)
    have heq : (∑ p ∈ E, if p ∈ E then e p * S p else 0) =
        ∑ p ∈ E, e p * S p :=
      Finset.sum_congr rfl fun p hp => ite_eq_left hp
    rw [heq] at h
    exact h
  have hterm : ∀ p, c p ^ 2 ≤ a * S p + (if p ∈ E then e p * S p else 0) := by
    intro p
    by_cases hp : p = 0
    · subst p
      have hc : c 0 = 0 := planarBlock_neumann_zero_coeff Q hw
      rw [hc, zero_pow (by decide : 2 ≠ 0)]
      apply add_nonneg (mul_nonneg ha (Finset.sum_nonneg fun j _ => sq_nonneg _))
      split_ifs with hm
      · exact mul_nonneg (he 0 hm) (Finset.sum_nonneg fun j _ => sq_nonneg _)
      · exact le_rfl
    · have he' : 0 ≤ a + if p ∈ E then e p else 0 := by
        apply add_nonneg ha
        split_ifs with hm
        · exact he p hm
        · exact le_rfl
      calc
        c p ^ 2 ≤ ((a + if p ∈ E then e p else 0) * Haar.cubeEig Q p) * c p ^ 2 :=
          le_mul_of_one_le_left (sq_nonneg _) (hgap p hp)
        _ = (a + if p ∈ E then e p else 0) * (Haar.cubeEig Q p * c p ^ 2) := by ring
        _ ≤ (a + if p ∈ E then e p else 0) * S p :=
          mul_le_mul_of_nonneg_left (planarBlock_neumann_coeff_sq Q hG hw p) he'
        _ = _ := by split_ifs <;> ring
  have hsum := hasSum_le hterm (planarBlock_cos_parseval Q w) ((hS.mul_left a).add hE)
  refine hsum.trans (add_le_add ?_ le_rfl)
  apply mul_le_mul_of_nonneg_left _ ha
  exact Finset.sum_le_sum fun j _ => planarBlock_sin_bessel Q hG j

end GMCExplicitDelta.Localization
