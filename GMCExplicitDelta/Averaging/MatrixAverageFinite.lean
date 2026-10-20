module

public import GMCExplicitDelta.Averaging.MatrixAverageColors

/-! # A5 for arbitrary finite palettes and equal finite classes -/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix
open GMCExplicitDelta.Insertion
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace GMCExplicitDelta.Averaging

/-- Equal-class centered average, with arbitrary finite index types. -/
noncomputable def finiteMatrixAverage {Ω κ ι : Type*} [MeasurableSpace Ω] [Fintype κ] [Fintype ι]
    {d : ℕ} (μ : Measure Ω) (M : κ → ι → Ω → Matrix (Fin d) (Fin d) ℝ) (ω : Ω) :
    Matrix (Fin d) (Fin d) ℝ :=
  ((Fintype.card κ * Fintype.card ι : ℕ) : ℝ)⁻¹ •
    ∑ c, ∑ i, (M c i ω - ∫ ω', M c i ω' ∂μ)

theorem finiteMatrixAverage_memLp {Ω κ ι : Type*} [MeasurableSpace Ω] [Fintype κ] [Fintype ι]
    {d : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {M : κ → ι → Ω → Matrix (Fin d) (Fin d) ℝ} (hm : ∀ c i, MemLp (M c i) 32 μ) :
    MemLp (finiteMatrixAverage μ M) 32 μ := by
  exact (memLp_finsetSum Finset.univ fun c _ => memLp_finsetSum Finset.univ
    fun i _ => (hm c i).sub (memLp_const _)).const_smul
      (((Fintype.card κ * Fintype.card ι : ℕ) : ℝ)⁻¹)

/-- A5 with a finite palette and one common finite class carrier. -/
theorem finiteMatrixAverage_le {Ω κ ι : Type*} [MeasurableSpace Ω] [Fintype κ] [Fintype ι]
    [Nonempty κ] [Nonempty ι] {μ : Measure Ω} [IsProbabilityMeasure μ] {d : ℕ}
    (hd : 2 ≤ d) (M : κ → ι → Ω → Matrix (Fin d) (Fin d) ℝ)
    {D F : ℝ} (hD : 0 < D) (hF : 0 < F)
    (hM : ∀ c i, Measurable (M c i)) (hm : ∀ c i, MemLp (M c i) 32 μ)
    (hPSD : ∀ c i ω, (M c i ω).PosSemidef) (hind : ∀ c, iIndepFun (M c) μ)
    (hmean : ∀ c i u, ‖u‖ = 1 → ∫ ω, sphereQuadratic (M c i ω) u ∂μ ≤ F)
    (hmoment : ∀ c i, ∫ ω, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (M c i ω)‖ ^ 32 ∂μ ≤ D ^ 32)
    (hL : 0 < Contract.sphereLower d)
    (hcert : 1 < Contract.sigmaNorm d ^ 32 * Contract.sphereLower d) :
    lpNorm (finiteMatrixAverage μ M) 32 μ ≤
      (Contract.sigmaNorm d : ℝ) * D * Contract.Bbar32 (Fintype.card ι) D F := by
  let e := (Fintype.equivFin κ).symm
  let b := (Fintype.equivFin ι).symm
  let N c i := M (e c) (b i)
  have hindN c : iIndepFun (N c) μ := (hind (e c)).precomp b.injective
  have h := lpNorm_coloredMatrixAverage_equal_le hd Fintype.card_pos Fintype.card_pos N
    hD hF (fun c i => hM _ _) (fun c i => hm _ _) (fun c i => hPSD _ _) hindN
    (fun c i => hmean _ _) (fun c i => hmoment _ _) hL hcert
  have heq : coloredMatrixAverage μ (fun _ : Fin (Fintype.card κ) => Fintype.card ι) N =
      finiteMatrixAverage μ M := by
    funext ω
    unfold coloredMatrixAverage finiteMatrixAverage
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
    congr 1
    change (∑ c, ∑ i, (M (e c) (b i) ω - ∫ ω', M (e c) (b i) ω' ∂μ)) = _
    calc
      _ = ∑ c : κ, ∑ i : Fin (Fintype.card ι),
          (M c (b i) ω - ∫ ω', M c (b i) ω' ∂μ) := Equiv.sum_comp e _
      _ = _ := Finset.sum_congr rfl (fun c _ => Equiv.sum_comp b (fun i => M c i ω - ∫ ω', M c i ω' ∂μ))
  rwa [heq] at h

end GMCExplicitDelta.Averaging
