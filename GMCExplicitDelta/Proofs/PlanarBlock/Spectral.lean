module

public import GMCExplicitDelta.Haar.NeumannSpectral

/-! Spectral coefficient estimates for the planar first Haar block. -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization

namespace GMCExplicitDelta.Localization

variable {d : ℕ}

/-- The squared cosine coefficients sum to the normalized energy. -/
theorem planarBlock_cos_parseval (Q : TriadicCube d) (w : H1Function (openCubeSet Q)) :
    HasSum (fun p : Fin d → ℤ =>
      (∫ x, Haar.cubeCos Q p x * w.toFun x ∂normalizedCubeMeasure Q) ^ 2)
      (Haar.energy Q w.toFun) := by
  have h := Haar.Torus.hasSum_sq_boxCoeff_cos (Haar.cubeCorner Q)
    (Haar.cubeScaleFactor_pos' Q)
    (show MemLp w.toFun 2
      (Haar.Torus.boxMeasure (Haar.cubeCorner Q) (cubeScaleFactor Q)) from by
      rw [Haar.boxMeasure_eq_normalizedCubeMeasure]
      exact Haar.memLp_normalized_of_memL2On w.memL2)
  rw [Haar.boxMeasure_eq_normalizedCubeMeasure] at h
  rw [Haar.energy_eq_integral_sq]
  exact h

/-- The zero cosine coefficient of a Neumann primitive vanishes. -/
theorem planarBlock_neumann_zero_coeff (Q : TriadicCube d) {G : Vec d → Vec d}
    {w : H1Function (openCubeSet Q)} (hw : IsNeumannPrimitive Q G w) :
    (∫ x, Haar.cubeCos Q 0 x * w.toFun x ∂normalizedCubeMeasure Q) = 0 := by
  simpa only [Haar.cubeCos, Haar.Torus.boxMode, Pi.zero_apply, Int.cast_zero,
    mul_zero, zero_mul, zero_div, Real.cos_zero, Finset.notMem_empty, ite_false,
    Finset.prod_const_one, one_mul, ← cubeAverage_eq_integral_normalizedCubeMeasure] using hw.1

/-- Mixed sine coefficients satisfy Bessel's inequality. -/
theorem planarBlock_sin_bessel (Q : TriadicCube d) {G : Vec d → Vec d}
    (hG : ∀ j, MemLp (fun x => G x j) 2 (normalizedCubeMeasure Q)) (j : Fin d) :
    ∑' p : Fin d → ℤ,
      (∫ x, Haar.cubeSin Q j p x * G x j ∂normalizedCubeMeasure Q) ^ 2 ≤
      Haar.energy Q (fun x => G x j) := by
  have h := Haar.Torus.tsum_sq_boxCoeff_le (Haar.cubeCorner Q)
    (Haar.cubeScaleFactor_pos' Q) {j}
    (show MemLp (fun x => G x j) 2
      (Haar.Torus.boxMeasure (Haar.cubeCorner Q) (cubeScaleFactor Q)) from by
      rw [Haar.boxMeasure_eq_normalizedCubeMeasure]
      exact hG j)
  rw [Haar.boxMeasure_eq_normalizedCubeMeasure] at h
  rw [Haar.energy_eq_integral_sq]
  exact h

/-- Cauchy--Schwarz converts the Neumann identity into a coefficient energy bound. -/
theorem planarBlock_neumann_coeff_sq (Q : TriadicCube d) {G : Vec d → Vec d}
    (hG : ∀ j, MemLp (fun x => G x j) 2 (normalizedCubeMeasure Q))
    {w : H1Function (openCubeSet Q)} (hw : IsNeumannPrimitive Q G w)
    (p : Fin d → ℤ) :
    Haar.cubeEig Q p *
      (∫ x, Haar.cubeCos Q p x * w.toFun x ∂normalizedCubeMeasure Q) ^ 2 ≤
      ∑ j, (∫ x, Haar.cubeSin Q j p x * G x j ∂normalizedCubeMeasure Q) ^ 2 := by
  let c := ∫ x, Haar.cubeCos Q p x * w.toFun x ∂normalizedCubeMeasure Q
  let s := fun j => ∫ x, Haar.cubeSin Q j p x * G x j ∂normalizedCubeMeasure Q
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d))
    (Haar.cubeFreq Q p) s
  have hid : Haar.cubeEig Q p * c = -∑ j, Haar.cubeFreq Q p j * s j :=
    Haar.neumann_coeff_identity Q hG hw p
  have hnonneg : 0 ≤ Haar.cubeEig Q p := Finset.sum_nonneg fun j _ => sq_nonneg _
  change Haar.cubeEig Q p * c ^ 2 ≤ ∑ j, s j ^ 2
  by_cases hz : Haar.cubeEig Q p = 0
  · rw [hz, zero_mul]
    exact Finset.sum_nonneg fun j _ => sq_nonneg _
  · have hpos : 0 < Haar.cubeEig Q p := lt_of_le_of_ne hnonneg (Ne.symm hz)
    have hsquare : (Haar.cubeEig Q p * c) ^ 2 =
        (∑ j, Haar.cubeFreq Q p j * s j) ^ 2 := by rw [hid, neg_sq]
    have hbound : Haar.cubeEig Q p * (Haar.cubeEig Q p * c ^ 2) ≤
        Haar.cubeEig Q p * ∑ j, s j ^ 2 := by
      calc
        _ = (Haar.cubeEig Q p * c) ^ 2 := by ring
        _ = (∑ j, Haar.cubeFreq Q p j * s j) ^ 2 := hsquare
        _ ≤ _ := h
    exact (mul_le_mul_iff_right₀ hpos).mp hbound

/-- A positive eigenvalue lower bound controls an individual cosine coefficient. -/
theorem planarBlock_coeff_of_gap (Q : TriadicCube d) {G : Vec d → Vec d}
    (hG : ∀ j, MemLp (fun x => G x j) 2 (normalizedCubeMeasure Q))
    {w : H1Function (openCubeSet Q)} (hw : IsNeumannPrimitive Q G w)
    (p : Fin d → ℤ) {a : ℝ} (ha : 0 < a) (hgap : a ≤ Haar.cubeEig Q p) :
    (∫ x, Haar.cubeCos Q p x * w.toFun x ∂normalizedCubeMeasure Q) ^ 2 ≤
      (∑ j, (∫ x, Haar.cubeSin Q j p x * G x j ∂normalizedCubeMeasure Q) ^ 2) / a := by
  apply (le_div_iff₀ ha).mpr
  calc
    _ = a * (∫ x, Haar.cubeCos Q p x * w.toFun x ∂normalizedCubeMeasure Q) ^ 2 := mul_comm _ _
    _ ≤ Haar.cubeEig Q p *
        (∫ x, Haar.cubeCos Q p x * w.toFun x ∂normalizedCubeMeasure Q) ^ 2 :=
      mul_le_mul_of_nonneg_right hgap (sq_nonneg _)
    _ ≤ _ := planarBlock_neumann_coeff_sq Q hG hw p

/-- Away from the four lowest mixed frequencies the planar integer gap is five. -/
theorem planarBlock_mixed_integer_gap (p : Fin 2 → ℤ)
    (h0 : p 0 ≠ 0) (h1 : p 1 ≠ 0)
    (hexc : ¬ (p 0 ^ 2 = 1 ∧ p 1 ^ 2 = 1)) :
    (5 : ℝ) ≤ (p 0 : ℝ) ^ 2 + (p 1 : ℝ) ^ 2 := by
  have ha : (1 : ℤ) ≤ p 0 ^ 2 := by
    have := Int.one_le_abs h0
    nlinarith [sq_abs (p 0)]
  have hb : (1 : ℤ) ≤ p 1 ^ 2 := by
    have := Int.one_le_abs h1
    nlinarith [sq_abs (p 1)]
  have hgap : (5 : ℤ) ≤ p 0 ^ 2 + p 1 ^ 2 := by
    by_cases h : p 0 ^ 2 = 1
    · have h' : p 1 ^ 2 ≠ 1 := fun h' => hexc ⟨h, h'⟩
      have hm : p 1 ≠ -1 := by intro e; simp [e] at h'
      have hp : p 1 ≠ 1 := by intro e; simp [e] at h'
      have : p 1 ≤ -2 ∨ 2 ≤ p 1 := by omega
      rcases this with hn | hp <;> nlinarith
    · have hm : p 0 ≠ -1 := by intro e; simp [e] at h
      have hp : p 0 ≠ 1 := by intro e; simp [e] at h
      have : p 0 ≤ -2 ∨ 2 ≤ p 0 := by omega
      rcases this with hn | hp <;> nlinarith
  exact_mod_cast hgap

/-- Explicit planar eigenvalue. -/
theorem planarBlock_cubeEig_two (Q : TriadicCube 2) (p : Fin 2 → ℤ) :
    Haar.cubeEig Q p = (Real.pi / cubeScaleFactor Q) ^ 2 *
      ((p 0 : ℝ) ^ 2 + (p 1 : ℝ) ^ 2) := by
  simp only [Haar.cubeEig, Fin.sum_univ_two, Haar.cubeFreq]
  ring

/-- The mixed planar spectrum starts at `2π²/ℓ²`. -/
theorem planarBlock_mixed_eigenvalue (Q : TriadicCube 2) (p : Fin 2 → ℤ)
    (h0 : p 0 ≠ 0) (h1 : p 1 ≠ 0) :
    2 * (Real.pi / cubeScaleFactor Q) ^ 2 ≤ Haar.cubeEig Q p := by
  have ha : (1 : ℤ) ≤ p 0 ^ 2 := by
    have := Int.one_le_abs h0
    nlinarith [sq_abs (p 0)]
  have hb : (1 : ℤ) ≤ p 1 ^ 2 := by
    have := Int.one_le_abs h1
    nlinarith [sq_abs (p 1)]
  have h : (2 : ℝ) ≤ (p 0 : ℝ) ^ 2 + (p 1 : ℝ) ^ 2 := by exact_mod_cast (show (2 : ℤ) ≤ p 0 ^ 2 + p 1 ^ 2 by omega)
  rw [planarBlock_cubeEig_two, mul_comm 2]
  exact mul_le_mul_of_nonneg_left h (sq_nonneg _)

/-- All other mixed frequencies lie above `5π²/ℓ²`. -/
theorem planarBlock_mixed_eigenvalue_gap (Q : TriadicCube 2) (p : Fin 2 → ℤ)
    (h0 : p 0 ≠ 0) (h1 : p 1 ≠ 0)
    (hexc : ¬ (p 0 ^ 2 = 1 ∧ p 1 ^ 2 = 1)) :
    5 * (Real.pi / cubeScaleFactor Q) ^ 2 ≤ Haar.cubeEig Q p := by
  rw [planarBlock_cubeEig_two, mul_comm 5]
  exact mul_le_mul_of_nonneg_left (planarBlock_mixed_integer_gap p h0 h1 hexc) (sq_nonneg _)

end GMCExplicitDelta.Localization
