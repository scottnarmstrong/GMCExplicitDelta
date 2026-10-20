module

public import GMCExplicitDelta.Proofs.HaarMode.Coefficients
public import GMCExplicitDelta.Proofs.HaarMode.Means
public import GMCExplicitDelta.Proofs.HaarMode.Abel

/-! # Total energy and sharp projection residual bounds for the constant mode -/

@[expose] public section

open Homogenization MeasureTheory Set
open scoped ENNReal

namespace GMCExplicitDelta.Localization

variable {d : ℕ}

/-- The normalized affine-cutoff vector field. -/
noncomputable def haarMode_field (row : Contract.Row d) (n : ℕ) (a : Homogenization.Vec d)
    (x : Homogenization.Vec d) (i : Fin d) : ℝ :=
  vecDot a (fun k => x k / (3 : ℝ) ^ n) *
    haarMode_rawG row.omegaEff (fun k => x k / (3 : ℝ) ^ n) i

/-- Weak almost-everywhere identities on the open cube hold for normalized cube measure. -/
theorem haarMode_ae_normalized (Q : TriadicCube d) {p : Homogenization.Vec d → Prop}
    (hp : ∀ᵐ x ∂volume.restrict (openCubeSet Q), p x) : ∀ᵐ x ∂normalizedCubeMeasure Q, p x := by
  unfold normalizedCubeMeasure cubeMeasure
  rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
  exact Measure.ae_smul_measure hp _

/-- Energy is unchanged by almost-everywhere equality. -/
theorem haarMode_energy_congr (Q : TriadicCube d) {f g : Homogenization.Vec d → ℝ}
    (h : f =ᵐ[normalizedCubeMeasure Q] g) : Haar.energy Q f = Haar.energy Q g := by
  simp only [Haar.energy, Haar.pairing, cubeAverage_eq_integral_normalizedCubeMeasure]
  exact integral_congr_ae (h.mono fun x hx => congrArg (fun t : ℝ => t * t) hx)

/-- A deterministic scalar factor is squared in the energy. -/
theorem haarMode_energy_mul (Q : TriadicCube d) (c : ℝ) (f : Homogenization.Vec d → ℝ) :
    Haar.energy Q (fun x => c * f x) = c ^ 2 * Haar.energy Q f := by
  simp only [Haar.energy, Haar.pairing]
  rw [show (fun x => c * f x * (c * f x)) = (fun x => c ^ 2 * (f x * f x)) by funext x; ring,
    haarMode_average_const_mul]

/-- The exact total energy Lcirc |a|². -/
theorem haarMode_total_energy (row : Contract.Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ))
    (h0 : 0 < row.omegaEff) (h1 : row.omegaEff ≤ 1 / 2) (n : ℕ) (a : Homogenization.Vec d) :
    vecEnergy (originCube d (n : ℤ)) (haarMode_field row n a) = row.Lcirc * vecNormSq a := by
  unfold vecEnergy haarMode_field
  simp_rw [haarMode_field_energy row h0 h1]
  exact haarMode_coeff_energy row hd a

/-- The exact squared vector mean. -/
theorem haarMode_total_mean_sq (row : Contract.Row d) (h0 : 0 < row.omegaEff)
    (h1 : row.omegaEff ≤ 1 / 2) (n : ℕ) (a : Homogenization.Vec d) :
    (∑ i, (cubeAverage (originCube d (n : ℤ)) (fun x => haarMode_field row n a x i)) ^ 2) =
      row.cosMean ^ (2 * d) * vecNormSq a := by
  unfold haarMode_field
  simp_rw [haarMode_field_mean row h0 h1, mul_pow, neg_sq]
  simp only [vecNormSq, vecDot, ← sq, ← pow_mul, Nat.mul_comm d 2]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- The exact total weak-gradient energy π² Hcirc |a|² / ℓ². -/
theorem haarMode_total_gradient (row : Contract.Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ))
    (h0 : 0 < row.omegaEff) (h1 : row.omegaEff ≤ 1 / 2) (n : ℕ) (a : Homogenization.Vec d)
    (u : Fin d → H1Function (openCubeSet (originCube d (n : ℤ)) ))
    (hg : ∀ i, ∀ᵐ x ∂volume.restrict (openCubeSet (originCube d (n : ℤ))),
      (u i).grad x = fun j => ((3 : ℝ) ^ n)⁻¹ *
        (a j * haarMode_rawG row.omegaEff (fun k => x k / (3 : ℝ) ^ n) i +
          vecDot a (fun k => x k / (3 : ℝ) ^ n) *
            haarMode_rawH row.omegaEff (fun k => x k / (3 : ℝ) ^ n) i j)) :
    (∑ i, vecEnergy (originCube d (n : ℤ)) (u i).grad) =
      ((3 : ℝ) ^ n)⁻¹ ^ 2 * (Real.pi ^ 2 * row.Hcirc * vecNormSq a) := by
  unfold vecEnergy
  have he (i j : Fin d) : Haar.energy (originCube d (n : ℤ)) (fun x => (u i).grad x j) =
      ((3 : ℝ) ^ n)⁻¹ ^ 2 *
        (a j ^ 2 * (∏ k, haarMode_m0 row (haarMode_gtype i k)) +
          2 * a j * haarMode_cross row a (haarMode_gtype i) (haarMode_htype i j) +
          haarMode_quad row a (haarMode_htype i j)) := by
    rw [haarMode_energy_congr _ ((haarMode_ae_normalized _ (hg i)).mono fun x hx => congrFun hx j),
      haarMode_energy_mul, haarMode_field_derivative_energy row h0 h1]
  simp_rw [he]
  simp only [← Finset.mul_sum]
  rw [haarMode_coeff_gradient row hd h0]

/-- Every residual is bounded by Rcirc |a|². -/
theorem haarMode_residual_R (row : Contract.Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ))
    (h0 : 0 < row.omegaEff) (h1 : row.omegaEff ≤ 1 / 2) (n : ℕ) (a : Homogenization.Vec d) (j : ℕ) :
    LocWeights.residualEnergy (originCube d (n : ℤ)) j (haarMode_field row n a) ≤ row.Rcirc * vecNormSq a := by
  classical
  have hm (i : Fin d) : MemLp (fun x => haarMode_field row n a x i) 2
      (normalizedCubeMeasure (originCube d (n : ℤ))) := by
    obtain ⟨u, hf, _⟩ := haarMode_affine_cutoff_h1 h1 n a i
    simpa only [hf, haarMode_field] using u.memL2_normalizedCubeMeasure
  have hh := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) =>
    Haar.energy_residual_le_fluctuation (originCube d (n : ℤ)) j (hm i)
  change LocWeights.residualEnergy _ _ _ ≤ _ at hh
  rw [Finset.sum_sub_distrib, haarMode_total_mean_sq row h0 h1] at hh
  change LocWeights.residualEnergy _ _ _ ≤ vecEnergy _ _ - _ at hh
  rw [haarMode_total_energy row hd h0 h1] at hh
  simpa only [Contract.Row.Rcirc, sub_mul] using hh

/-- Cell Poincaré gives the complementary Hcirc / 9ʲ residual bound. -/
theorem haarMode_residual_H
    (hP : ∀ (Q : Homogenization.TriadicCube d) (j : ℕ) (h : H1Function (openCubeSet Q)),
      Haar.energy Q (fun x => h.toFun x - cubeProjection Q j h.toFun x) ≤
        cubeScaleFactor Q ^ 2 / (9 ^ j * Real.pi ^ 2) * vecEnergy Q h.grad)
    (row : Contract.Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ))
    (h0 : 0 < row.omegaEff) (h1 : row.omegaEff ≤ 1 / 2) (n : ℕ) (a : Homogenization.Vec d) (j : ℕ) :
    LocWeights.residualEnergy (originCube d (n : ℤ)) j (haarMode_field row n a) ≤
      row.Hcirc / 9 ^ j * vecNormSq a := by
  classical
  choose u hf hg using fun i => haarMode_affine_cutoff_h1 h1 n a i
  have hh := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) =>
    hP (originCube d (n : ℤ)) j (u i)
  simp only [hf] at hh
  rw [← Finset.mul_sum, haarMode_total_gradient row hd h0 h1 n a u hg] at hh
  change LocWeights.residualEnergy _ _ _ ≤ _ at hh
  convert! hh using 1
  simp only [cubeScaleFactor, originCube, zpow_natCast]
  field_simp

end GMCExplicitDelta.Localization
