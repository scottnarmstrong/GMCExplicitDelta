module

public import GMCExplicitDelta.Proofs.HaarMode.Affine

/-! # Fubini identities for the multivariate affine-cutoff field -/

@[expose] public section

open MeasureTheory Homogenization Set
open scoped ENNReal

namespace GMCExplicitDelta.Localization

variable {d : ℕ}

/-- The diagonal affine-quadratic moment of a tensor of squared factors. -/
noncomputable def haarMode_quad (row : Contract.Row d) (a : Homogenization.Vec d)
    (b : Fin d → Fin 3) : ℝ :=
  ∑ m, a m ^ 2 * haarMode_m2 row (b m) * ∏ k ∈ Finset.univ.erase m, haarMode_m0 row (b k)

/-- The affine first moment of two tensor factors. -/
noncomputable def haarMode_cross (row : Contract.Row d) (a : Homogenization.Vec d)
    (b c : Fin d → Fin 3) : ℝ :=
  ∑ m, a m * haarMode_mix1 row (b m) (c m) *
    ∏ k ∈ Finset.univ.erase m, haarMode_mix0 row (b k) (c k)

/-- Squared tensor factors have the exact product integral. -/
theorem haarMode_tensor_sq (row : Contract.Row d) (h0 : 0 < row.omegaEff)
    (h1 : row.omegaEff ≤ 1 / 2) (n : ℕ) (b : Fin d → Fin 3) :
    cubeAverage (originCube d (n : ℤ)) (fun x =>
      (∏ k, haarMode_atom row.omegaEff (b k) (x k / (3 : ℝ) ^ n)) ^ 2) =
      ∏ k, haarMode_m0 row (b k) := by
  simp only [← Finset.prod_pow]
  rw [haarMode_cubeAverage_scaled_prod (f := fun k t => haarMode_atom row.omegaEff (b k) t ^ 2)]
  simp_rw [haarMode_atom_sq_integral row h0 h1]

/-- Affine-weighted squared tensors reduce to the diagonal moment table. -/
theorem haarMode_tensor_quad (row : Contract.Row d) (h0 : 0 < row.omegaEff)
    (h1 : row.omegaEff ≤ 1 / 2) (n : ℕ) (a : Homogenization.Vec d) (b : Fin d → Fin 3) :
    cubeAverage (originCube d (n : ℤ)) (fun x =>
      vecDot a (fun k => x k / (3 : ℝ) ^ n) ^ 2 *
        (∏ k, haarMode_atom row.omegaEff (b k) (x k / (3 : ℝ) ^ n)) ^ 2) = haarMode_quad row a b := by
  simp only [← Finset.prod_pow]
  rw [haarMode_affine_quadratic (f := fun k t => haarMode_atom row.omegaEff (b k) t ^ 2)]
  · simp_rw [haarMode_atom_sq_integral row h0 h1, haarMode_atom_sq_moment row h0 h1]
    rfl
  · intro k r _
    simpa only [pow_two] using haarMode_atom_pair_integrable h1 (b k) (b k) r
  · intro k
    exact haarMode_atom_sq_first h1 (b k)

/-- Affine-weighted mixed tensors reduce to the first-moment table. -/
theorem haarMode_tensor_cross (row : Contract.Row d) (h0 : 0 < row.omegaEff)
    (h1 : row.omegaEff ≤ 1 / 2) (n : ℕ) (a : Homogenization.Vec d)
    (b c : Fin d → Fin 3) :
    cubeAverage (originCube d (n : ℤ)) (fun x =>
      vecDot a (fun k => x k / (3 : ℝ) ^ n) *
        ((∏ k, haarMode_atom row.omegaEff (b k) (x k / (3 : ℝ) ^ n)) *
         (∏ k, haarMode_atom row.omegaEff (c k) (x k / (3 : ℝ) ^ n)))) = haarMode_cross row a b c := by
  simp only [← Finset.prod_mul_distrib]
  rw [haarMode_affine_linear (f := fun k t => haarMode_atom row.omegaEff (b k) t * haarMode_atom row.omegaEff (c k) t)]
  · simp_rw [haarMode_atom_pair_integral row h0 h1, haarMode_atom_pair_moment row h0 h1]
    rfl
  · intro k
    simpa using haarMode_atom_pair_integrable h1 (b k) (c k) 0
  · intro k
    simpa using haarMode_atom_pair_integrable h1 (b k) (c k) 1

/-- The exact energy of one affine-cutoff component. -/
theorem haarMode_field_energy (row : Contract.Row d) (h0 : 0 < row.omegaEff)
    (h1 : row.omegaEff ≤ 1 / 2) (n : ℕ) (a : Homogenization.Vec d) (i : Fin d) :
    Haar.energy (originCube d (n : ℤ)) (fun x =>
      vecDot a (fun k => x k / (3 : ℝ) ^ n) *
        haarMode_rawG row.omegaEff (fun k => x k / (3 : ℝ) ^ n) i) =
      haarMode_quad row a (haarMode_gtype i) := by
  simp only [Haar.energy, Haar.pairing, ← sq, mul_pow, haarMode_rawG]
  exact haarMode_tensor_quad row h0 h1 n a _

/-- The exact energy of one unscaled product-rule derivative. -/
theorem haarMode_field_derivative_energy (row : Contract.Row d) (h0 : 0 < row.omegaEff)
    (h1 : row.omegaEff ≤ 1 / 2) (n : ℕ) (a : Homogenization.Vec d) (i j : Fin d) :
    Haar.energy (originCube d (n : ℤ)) (fun x =>
      a j * haarMode_rawG row.omegaEff (fun k => x k / (3 : ℝ) ^ n) i +
        vecDot a (fun k => x k / (3 : ℝ) ^ n) *
          haarMode_rawH row.omegaEff (fun k => x k / (3 : ℝ) ^ n) i j) =
      a j ^ 2 * (∏ k, haarMode_m0 row (haarMode_gtype i k)) +
      2 * a j * haarMode_cross row a (haarMode_gtype i) (haarMode_htype i j) +
      haarMode_quad row a (haarMode_htype i j) := by
  let G := fun x : Homogenization.Vec d => haarMode_rawG row.omegaEff (fun k => x k / (3 : ℝ) ^ n) i
  let H := fun x : Homogenization.Vec d => haarMode_rawH row.omegaEff (fun k => x k / (3 : ℝ) ^ n) i j
  let L := fun x : Homogenization.Vec d => vecDot a (fun k => x k / (3 : ℝ) ^ n)
  have hg : Integrable (fun x => G x ^ 2) (normalizedCubeMeasure (originCube d (n : ℤ))) := by
    simpa only [G, haarMode_rawG, pow_two, Finset.prod_mul_distrib] using
      haarMode_integrable_scaled_prod n
        (fun k t => haarMode_atom row.omegaEff (haarMode_gtype i k) t * haarMode_atom row.omegaEff (haarMode_gtype i k) t)
        (fun k => by simpa using haarMode_atom_pair_integrable h1 (haarMode_gtype i k) (haarMode_gtype i k) 0)
  have hh : Integrable (fun x => L x ^ 2 * H x ^ 2) (normalizedCubeMeasure (originCube d (n : ℤ))) := by
    simpa only [L, H, haarMode_rawH, pow_two, Finset.prod_mul_distrib] using
      haarMode_integrable_affine_sq n a
        (fun k t => haarMode_atom row.omegaEff (haarMode_htype i j k) t * haarMode_atom row.omegaEff (haarMode_htype i j k) t)
        (fun k r _ => haarMode_atom_pair_integrable h1 _ _ r)
  have hc : Integrable (fun x => L x * (G x * H x)) (normalizedCubeMeasure (originCube d (n : ℤ))) := by
    simpa only [L, G, H, haarMode_rawG, haarMode_rawH, ← Finset.prod_mul_distrib] using
      haarMode_integrable_affine n a
        (fun k t => haarMode_atom row.omegaEff (haarMode_gtype i k) t * haarMode_atom row.omegaEff (haarMode_htype i j k) t)
        (fun k r _ => haarMode_atom_pair_integrable h1 _ _ r)
  have heq : (fun x => (a j * G x + L x * H x) ^ 2) =
      (fun x => (a j ^ 2 * G x ^ 2 + (2 * a j) * (L x * (G x * H x))) + L x ^ 2 * H x ^ 2) := by
    funext x; ring
  unfold Haar.energy Haar.pairing
  simp only [← sq]
  change cubeAverage _ (fun x => (a j * G x + L x * H x) ^ 2) = _
  rw [heq]
  simp only [cubeAverage_eq_integral_normalizedCubeMeasure]
  have hsum := integral_add ((hg.const_mul (a j ^ 2)).add (hc.const_mul (2 * a j))) hh
  have hsum2 := integral_add (hg.const_mul (a j ^ 2)) (hc.const_mul (2 * a j))
  simp only [Pi.add_apply] at hsum hsum2
  rw [hsum, hsum2, integral_const_mul, integral_const_mul]
  simp only [← cubeAverage_eq_integral_normalizedCubeMeasure]
  dsimp only [G, H, L, haarMode_rawG, haarMode_rawH]
  rw [haarMode_tensor_sq row h0 h1, haarMode_tensor_cross row h0 h1, haarMode_tensor_quad row h0 h1]

end GMCExplicitDelta.Localization
