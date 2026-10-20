module

public import GMCExplicitDelta.Proofs.Variance.ParityGeometry
public import GMCExplicitDelta.Proofs.Variance.Cells

/-! # Scalar variance gain from parity classes -/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Homogenization Homogenization.Book SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion

namespace GMCExplicitDelta.Assembly

variable {d : ℕ}

theorem frozenVar_parity_indep (hd : d ∈ ({2, 3, 4} : Finset ℕ))
    (M : SubdiffusiveProcess.Model.GMCModel d) (L k n : ℕ) (hk : L + 1 ≤ k)
    (X : Homogenization.TriadicCube d → SubdiffusiveProcess.Model.PotentialSample d → ℝ)
    (hlocal : ∀ R ∈ descendantsAtScale (originCube d (n : ℤ)) (k : ℤ),
      ∃ Y : SubdiffusiveProcess.Model.PotentialSample d → ℝ,
        @Measurable _ ℝ ((LocalSigmaR
          (Metric.thickening (responseRestrictionBridgeRadius d) (cubeSet R))).comap
          (aCutoffRegCoeffField M L)) _ Y ∧ X R =ᵐ[M.P.toMeasure] Y)
    (c : Fin d → Fin 2) :
    Set.Pairwise ↑((descendantsAtScale (originCube d (n : ℤ)) (k : ℤ)).filter
      (fun R => frozenVar_parityColor R = c)) (fun R S => IndepFun (X R) (X S) M.P.toMeasure) := by
  let : NeZero d := neZero_of_gmcModel M
  intro R hR S hS hne
  have hr := Finset.mem_filter.mp hR
  have hs := Finset.mem_filter.mp hS
  obtain ⟨YR, hYR, heqR⟩ := hlocal R hr.1
  obtain ⟨YS, hYS, heqS⟩ := hlocal S hs.1
  have hsep := fun {x y : Homogenization.Vec d} hx hy => frozenVar_parity_thickened_separation hd hk
    (scale_eq_of_mem_descendantsAtScale hr.1) (scale_eq_of_mem_descendantsAtScale hs.1)
    (hr.2.trans hs.2.symm) hne (x := x) (y := y) hx hy
  have hfield := indep_aCutoffRegCoeffField_local_of_separation M L
    (Metric.thickening (responseRestrictionBridgeRadius d) (cubeSet R))
    (Metric.thickening (responseRestrictionBridgeRadius d) (cubeSet S))
    Metric.isOpen_thickening Metric.isOpen_thickening @hsep
  have hind : IndepFun YR YS M.P.toMeasure := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hfield hYR.comap_le) hYS.comap_le
  exact hind.congr heqR.symm heqS.symm

/-- The parity estimate for a centered scalar observable with stationary second moment. -/
theorem frozenVar_parity_scalar (hd : d ∈ ({2, 3, 4} : Finset ℕ))
    (M : SubdiffusiveProcess.Model.GMCModel d) (L k n : ℕ) (hk : L + 1 ≤ k) (hkn : k ≤ n)
    (X : Homogenization.TriadicCube d → SubdiffusiveProcess.Model.PotentialSample d → ℝ)
    (hlocal : ∀ R ∈ descendantsAtScale (originCube d (n : ℤ)) (k : ℤ),
      ∃ Y : SubdiffusiveProcess.Model.PotentialSample d → ℝ,
        @Measurable _ ℝ ((LocalSigmaR
          (Metric.thickening (responseRestrictionBridgeRadius d) (cubeSet R))).comap
          (aCutoffRegCoeffField M L)) _ Y ∧ X R =ᵐ[M.P.toMeasure] Y)
    (hLp : ∀ R ∈ descendantsAtScale (originCube d (n : ℤ)) (k : ℤ), MemLp (X R) 2 M.P.toMeasure)
    (hmean : ∀ R ∈ descendantsAtScale (originCube d (n : ℤ)) (k : ℤ),
      (∫ ω, X R ω ∂M.P.toMeasure) = 0)
    (σ : ℝ) (hσ : 0 ≤ σ)
    (hsecond : ∀ R ∈ descendantsAtScale (originCube d (n : ℤ)) (k : ℤ),
      (∫ ω, X R ω ^ 2 ∂M.P.toMeasure) ≤ σ) :
    (∫ ω, (probabilityFinsetAverage (descendantsAtScale (originCube d (n : ℤ)) (k : ℤ)) X ω) ^ 2
      ∂M.P.toMeasure) ≤ (2 : ℝ) ^ d / (3 : ℝ) ^ (d * (n - k)) * σ := by
  let s := descendantsAtScale (originCube d (n : ℤ)) (k : ℤ)
  have hs : s.Nonempty := by
    rw [show s = descendantsAtDepth (originCube d (n : ℤ)) (n - k) from frozenVar_cells_eq_depth n k hkn]
    exact descendantsAtDepth_nonempty _ _
  have hindep : ∀ c ∈ s.image frozenVar_parityColor,
      Set.Pairwise ↑(s.filter (fun R => frozenVar_parityColor R = c))
        (fun R S => IndepFun (X R) (X S) M.P.toMeasure) :=
    fun c _ => frozenVar_parity_indep hd M L k n hk X hlocal c
  have hv := variance_probabilityFinsetAverage_le_of_coloring_secondMoment
    s hs frozenVar_parityColor hLp hindep hsecond
  have hAvgLp : MemLp (probabilityFinsetAverage s X) 2 M.P.toMeasure := by
    simpa only [probabilityFinsetAverage, Finset.sum_apply] using!
      (memLp_finsetSum' s (fun R hR => hLp R hR)).const_mul ((s.card : ℝ)⁻¹)
  have hAvgMean : (∫ ω, probabilityFinsetAverage s X ω ∂M.P.toMeasure) = 0 := by
    simp only [probabilityFinsetAverage, integral_const_mul]
    rw [integral_finsetSum s (fun R hR => (hLp R hR).integrable (by norm_num))]
    rw [Finset.sum_eq_zero (fun R hR => hmean R hR), mul_zero]
  rw [variance_eq_sub hAvgLp, hAvgMean, zero_pow two_ne_zero, sub_zero] at hv
  have hc : ((s.image frozenVar_parityColor).card : ℝ) ≤ (2 : ℝ) ^ d := by
    have hc0 := Finset.card_le_univ (s.image frozenVar_parityColor)
    simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] using
      (Nat.cast_le (α := ℝ)).mpr hc0
  have hcard : (s.card : ℝ) = (3 : ℝ) ^ (d * (n - k)) := by
    dsimp only [s]
    rw [frozenVar_cells_card n k hkn]
    norm_cast
  exact hv.trans (by
    rw [hcard, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) hσ)

end GMCExplicitDelta.Assembly
