module

public import GMCExplicitDelta.Proofs.Variance.ParityVariance
public import GMCExplicitDelta.Proofs.Variance.CellMoments

/-! # The parity bound lifted from entries to Frobenius variances -/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Homogenization Homogenization.Book SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion

namespace GMCExplicitDelta.Assembly

variable {d : ℕ}

theorem frozenVar_cellAvg_entry (n k : ℕ) (A : Ch02.Domain d → Homogenization.Mat d) (i j : Fin d) :
    cellAvg n k A i j =
      ((descendantsAtScale (originCube d (n : ℤ)) (k : ℤ)).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtScale (originCube d (n : ℤ)) (k : ℤ), A (cellAt 0 R) i j := by
  change _ * (∑ R ∈ descendantsAtScale (originCube d (n : ℤ)) (k : ℤ), A (cellAt 0 R)) i j = _
  rw [Matrix.sum_apply]

theorem frozenVar_integral_frobSq_eq_sum {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {A : Ω → Homogenization.Mat d} (hA : ∀ i j, MemLp (fun ω => A ω i j) 2 μ) :
    (∫ ω, frobSq (A ω) ∂μ) = ∑ i, ∑ j, ∫ ω, A ω i j ^ 2 ∂μ := by
  unfold frobSq
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => (hA i j).integrable_sq))]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_finsetSum Finset.univ (fun j _ => (hA i j).integrable_sq)

theorem frozenVar_parity_matrix (hd : d ∈ ({2, 3, 4} : Finset ℕ))
    (M : SubdiffusiveProcess.Model.GMCModel d) (L k n : ℕ) (hk : L + 1 ≤ k) (hkn : k ≤ n)
    (A : Ch02.Domain d → SubdiffusiveProcess.Model.PotentialSample d → Homogenization.Mat d)
    (C : Homogenization.Mat d)
    (hMem : ∀ U i j, MemLp (fun ω => A U ω i j) 2 M.P.toMeasure)
    (hLocal : ∀ R i j, ∃ Y : SubdiffusiveProcess.Model.PotentialSample d → ℝ,
      @Measurable _ ℝ ((LocalSigmaR
        (Metric.thickening (responseRestrictionBridgeRadius d) (cubeSet R))).comap
        (aCutoffRegCoeffField M L)) _ Y ∧
      (fun ω => A (cellAt 0 R) ω i j) =ᵐ[M.P.toMeasure] Y)
    (hMean : ∀ R, R.scale = (k : ℤ) → ∀ i j,
      (∫ ω, A (cellAt 0 R) ω i j ∂M.P.toMeasure) = C i j)
    (hStat : ∀ R, R.scale = (k : ℤ) → ∀ ω,
      A (cellAt 0 R) ω = A (cubeAt 0 k) (translatePotentialSequence (triadicCubeShift R) ω)) :
    (∫ ω, frobSq (cellAvg n k (fun U => A U ω) - C) ∂M.P.toMeasure) ≤
      (2 : ℝ) ^ d / (3 : ℝ) ^ (d * (n - k)) *
        ∫ ω, frobSq (A (cubeAt 0 k) ω - C) ∂M.P.toMeasure := by
  let s := descendantsAtScale (originCube d (n : ℤ)) (k : ℤ)
  have hc : (s.card : ℝ) ≠ 0 := by
    dsimp only [s]
    rw [frozenVar_cells_card n k hkn]
    positivity
  have hAvg (i j : Fin d) : MemLp (fun ω => (cellAvg n k (fun U => A U ω) - C) i j) 2 M.P.toMeasure :=
    (frozenVar_cellAvg_entry_memLp n k A M hMem i j).sub (memLp_const _)
  have hOrigin (i j : Fin d) : MemLp (fun ω => (A (cubeAt 0 k) ω - C) i j) 2 M.P.toMeasure :=
    (hMem (cubeAt 0 k) i j).sub (memLp_const _)
  have hEntry (i j : Fin d) :
      (∫ ω, ((cellAvg n k (fun U => A U ω) - C) i j) ^ 2 ∂M.P.toMeasure) ≤
        (2 : ℝ) ^ d / (3 : ℝ) ^ (d * (n - k)) *
          ∫ ω, ((A (cubeAt 0 k) ω - C) i j) ^ 2 ∂M.P.toMeasure := by
    let X := fun R ω => A (cellAt 0 R) ω i j - C i j
    have hlocal : ∀ R ∈ s, ∃ Y : SubdiffusiveProcess.Model.PotentialSample d → ℝ,
        @Measurable _ ℝ ((LocalSigmaR
          (Metric.thickening (responseRestrictionBridgeRadius d) (cubeSet R))).comap
          (aCutoffRegCoeffField M L)) _ Y ∧ X R =ᵐ[M.P.toMeasure] Y := by
      intro R _
      obtain ⟨Y, hY, heq⟩ := hLocal R i j
      refine ⟨fun ω => Y ω - C i j, hY.sub measurable_const, ?_⟩
      exact heq.sub (Filter.EventuallyEq.rfl)
    have hLp : ∀ R ∈ s, MemLp (X R) 2 M.P.toMeasure :=
      fun R _ => (hMem (cellAt 0 R) i j).sub (memLp_const _)
    have hmean : ∀ R ∈ s, (∫ ω, X R ω ∂M.P.toMeasure) = 0 := by
      intro R hR
      rw [show X R = fun ω => A (cellAt 0 R) ω i j - C i j from rfl,
        integral_sub ((hMem (cellAt 0 R) i j).integrable (by norm_num)) (integrable_const _),
        hMean R (scale_eq_of_mem_descendantsAtScale hR) i j, integral_const]
      simp only [probReal_univ, one_smul, sub_self]
    have hsecond : ∀ R ∈ s, (∫ ω, X R ω ^ 2 ∂M.P.toMeasure) ≤
        ∫ ω, ((A (cubeAt 0 k) ω - C) i j) ^ 2 ∂M.P.toMeasure := by
      intro R hR
      apply le_of_eq
      dsimp only [X]
      simp_rw [hStat R (scale_eq_of_mem_descendantsAtScale hR)]
      exact integral_comp_eq_of_map_eq (measurable_translatePotentialSequence (triadicCubeShift R))
        (potentialSequenceLaw_stationary M (triadicCubeShift R)) _ (hOrigin i j).integrable_sq.aestronglyMeasurable
    have hv := frozenVar_parity_scalar hd M L k n hk hkn X hlocal hLp hmean _
      (integral_nonneg fun ω => sq_nonneg (((A (cubeAt 0 k) ω - C) i j))) hsecond
    have hAvgEq (ω : SubdiffusiveProcess.Model.PotentialSample d) :
        probabilityFinsetAverage s X ω = (cellAvg n k (fun U => A U ω) - C) i j := by
      change (s.card : ℝ)⁻¹ * (∑ R ∈ s, (A (cellAt 0 R) ω i j - C i j)) =
        cellAvg n k (fun U => A U ω) i j - C i j
      rw [frozenVar_cellAvg_entry, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      change (s.card : ℝ)⁻¹ * ((∑ R ∈ s, A (cellAt 0 R) ω i j) - (s.card : ℝ) * C i j) =
        (s.card : ℝ)⁻¹ * (∑ R ∈ s, A (cellAt 0 R) ω i j) - C i j
      rw [mul_sub, inv_mul_cancel_left₀ hc]
    dsimp only [s] at hAvgEq
    simpa only [hAvgEq] using hv
  rw [frozenVar_integral_frobSq_eq_sum (A := fun ω => cellAvg n k (fun U => A U ω) - C) hAvg,
    frozenVar_integral_frobSq_eq_sum (A := fun ω => A (cubeAt 0 k) ω - C) hOrigin]
  simp only [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hEntry i j

end GMCExplicitDelta.Assembly
