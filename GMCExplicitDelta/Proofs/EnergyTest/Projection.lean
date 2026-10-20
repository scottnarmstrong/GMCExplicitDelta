module

public import GMCExplicitDelta.Localization.HaarComplete
public import GMCExplicitDelta.Haar.TriadicDualNorms
public import GMCExplicitDelta.Localization.CoreDefs

/-! Projection limits and finite-depth vector duality for the harmonic energy test. -/

@[expose] public section

open Homogenization MeasureTheory Filter
open scoped Topology ENNReal

namespace GMCExplicitDelta.Localization.EnergyTest

variable {d : ℕ}

/-- Haar completeness gives convergence of the actual scalar pairings. -/
theorem pairing_projection_tendsto (Q : TriadicCube d) {f g : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    Tendsto (fun N => Haar.pairing Q (cubeProjection Q N f) (cubeProjection Q N g))
      atTop (𝓝 (Haar.pairing Q f g)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have he := (energy_sub_projection_tendsto_proof Q hg).sqrt.const_mul
    (Real.sqrt (Haar.energy Q f))
  simp only [Real.sqrt_zero, mul_zero] at he
  refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) he
  rw [Haar.pairing_projections Q N N hf hg, min_self, Real.norm_eq_abs, abs_sub_comm,
    ← Haar.pairing_sub_right Q hf hg (Haar.projection_memLp Q N g 2)]
  exact Haar.abs_pairing_le Q hf (hg.sub (Haar.projection_memLp Q N g 2))

/-- Finite-dimensional Cauchy--Schwarz collects the componentwise H1(a) bounds. -/
theorem vector_projection_pairing_le (Q : TriadicCube d) {q : ℝ} (hq : 1 < q) (N : ℕ)
    {F G : Vec d → Vec d}
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q)) :
    |∑ i, Haar.pairing Q (cubeProjection Q N fun x => F x i)
      (cubeProjection Q N fun x => G x i)| ≤
      Real.sqrt (∑ i, Haar.partialEnergy Q q⁻¹ N (fun x => F x i)) *
        Real.sqrt (∑ i, Haar.partialEnergy Q q N (fun x => G x i)) := by
  calc
    _ ≤ ∑ i, |Haar.pairing Q (cubeProjection Q N fun x => F x i)
        (cubeProjection Q N fun x => G x i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, Real.sqrt (Haar.partialEnergy Q q⁻¹ N (fun x => F x i)) *
        Real.sqrt (Haar.partialEnergy Q q N (fun x => G x i)) :=
      Finset.sum_le_sum fun i _ => Haar.abs_pairing_projections_le Q hq N (hF i) (hG i)
    _ ≤ _ := Real.sum_sqrt_mul_sqrt_le _
      (fun i => Finset.sum_nonneg fun k _ =>
        mul_nonneg (pow_nonneg (inv_nonneg.mpr (le_trans zero_le_one hq.le)) k) (Haar.energy_nonneg Q _))
      (fun i => Finset.sum_nonneg fun k _ =>
        mul_nonneg (pow_nonneg (le_trans zero_le_one hq.le) k) (Haar.energy_nonneg Q _))

end GMCExplicitDelta.Localization.EnergyTest
