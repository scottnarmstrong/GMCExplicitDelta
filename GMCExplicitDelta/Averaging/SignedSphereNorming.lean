module

public import GMCExplicitDelta.Averaging.SignedSphereSpectral

/-! # Deterministic signed symmetric-matrix norming by Gaussian averages -/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Matrix Set
open scoped BigOperators RealInnerProductSpace
open GMCExplicitDelta.Insertion

namespace GMCExplicitDelta.Averaging

theorem signedMean_mem {n : ℕ} [NeZero n] (a : Fin n → ℝ) (ha : ∀ i, |a i| ≤ 1) :
    signedMean a ∈ Set.Icc (-1) 1 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  unfold signedMean
  constructor
  · apply (le_div_iff₀ hn).2
    have h := sum_le_sum (s := (univ : Finset (Fin n))) (fun i _ => (abs_le.mp (ha i)).1)
    simpa only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_neg_one, neg_mul, one_mul] using h
  · apply (div_le_iff₀ hn).2
    have h := sum_le_sum (s := (univ : Finset (Fin n))) (fun i _ => (abs_le.mp (ha i)).2)
    simpa only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, one_mul] using h

theorem signedDiagonalMoment_lower {n : ℕ} [NeZero n] (a : Fin n → ℝ) (ha : ∀ i, |a i| ≤ 1) :
    radialMoment ((n + 1 : ℕ) : ℝ) 32 * (Contract.sphereLower (n + 1) : ℝ) ≤
      signedDiagonalMoment a := by
  calc
    _ ≤ radialMoment ((n + 1 : ℕ) : ℝ) 32 * spherePolyReal (n + 1) (signedMean a) :=
      mul_le_mul_of_nonneg_left (sphereLower_le_spherePolyReal n (signedMean_mem a ha))
        (radialMoment_pos (by positivity) 32).le
    _ = signedSplitMoment n (signedMean a) := (signedSplitMoment_eq_spherePoly n _).symm
    _ ≤ _ := signedSplitMoment_mean_le a

/-- Deterministic A4 before replacing the radial moment by its Gaussian integral. -/
theorem signed_sphere_radial_lower {n : ℕ} [NeZero n]
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hH : H.IsHermitian) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) H‖ ^ 32 * (Contract.sphereLower (n + 1) : ℝ) *
        radialMoment ((n + 1 : ℕ) : ℝ) 32 ≤
      ∫ g, sphereQuadratic H g ^ 32 ∂stdGaussian (EuclideanSpace ℝ (Fin (n + 1))) := by
  let T := Matrix.toEuclideanCLM (𝕜 := ℝ) H
  by_cases hz : ‖T‖ = 0
  · change ‖T‖ ^ 32 * _ * _ ≤ _
    rw [hz, zero_pow (by decide : 32 ≠ 0), zero_mul, zero_mul]
    exact integral_nonneg fun _ => by positivity
  · have hsym : T.toLinearMap.IsSymmetric := by
      rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
      exact Matrix.isSymmetric_toEuclideanLin_iff.mpr hH
    obtain ⟨i, hi⟩ := exists_norm_eigenvalue T hsym hH.eigenvectorBasis hH.eigenvalues
      (matrix_eigenbasis_apply hH)
    let e : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 i
    let b := hH.eigenvectorBasis.reindex e
    let ell : Fin (n + 1) → ℝ := fun j => hH.eigenvalues (e.symm j)
    have he : ∀ j, T (b j) = ell j • b j := by
      intro j
      simpa only [b, ell, OrthonormalBasis.reindex_apply] using matrix_eigenbasis_apply hH (e.symm j)
    let c := ell 0
    have hcabs : |c| = ‖T‖ := by simpa [c, ell, e] using hi
    have hc : c ≠ 0 := by
      intro h
      rw [h, abs_zero] at hcabs
      exact hz hcabs.symm
    have htpos : 0 < ‖T‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    let a : Fin n → ℝ := fun j => ell j.succ / c
    have ha : ∀ j, |a j| ≤ 1 := by
      intro j
      change |ell j.succ / c| ≤ 1
      rw [abs_div, hcabs]
      exact (div_le_one htpos).2 (eigenvalue_abs_le_opNorm T b ell he j.succ)
    have hcpow : c ^ 32 = ‖T‖ ^ 32 := by
      rw [← (by decide : Even 32).pow_abs c, hcabs]
    rw [integral_quadratic_eigenbasis H b ell he, integral_diagonal_normalize ell hc rfl, hcpow]
    calc
      _ = ‖T‖ ^ 32 * (radialMoment ((n + 1 : ℕ) : ℝ) 32 * (Contract.sphereLower (n + 1) : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (signedDiagonalMoment_lower a ha) (pow_nonneg (norm_nonneg _) _)

/-- A4 for every real symmetric matrix in dimension at least two, in Gaussian form. -/
theorem signed_sphere_gaussian_lower {d : ℕ} (hd : 2 ≤ d)
    {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.IsHermitian) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) H‖ ^ 32 * (Contract.sphereLower d : ℝ) *
        (∫ g : EuclideanSpace ℝ (Fin d), ‖g‖ ^ 64 ∂stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
      ∫ g, |sphereQuadratic H g| ^ 32 ∂stdGaussian (EuclideanSpace ℝ (Fin d)) := by
  cases d with
  | zero => omega
  | succ n =>
    have : NeZero n := ⟨by omega⟩
    simp_rw [(by decide : Even 32).pow_abs]
    rw [integral_norm_pow_stdGaussian_even (n + 1) 32]
    exact signed_sphere_radial_lower hH

end GMCExplicitDelta.Averaging
