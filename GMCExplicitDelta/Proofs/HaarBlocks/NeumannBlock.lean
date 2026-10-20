module

public import GMCExplicitDelta.Localization.HaarDefs
public import GMCExplicitDelta.Haar.NeumannBlock
public import GMCExplicitDelta.Steps.LocalizationNeumann

/-!
Proof of the H5/H6 target `neumann_block_bound` (primitive on Haar blocks): H5 by duality
(`Haar.neumann_block_bound_of_projectedPoincare`, consuming H4 = `projected_poincare`), and for
`d = 2`, `k = 1` the planar constant H6 (`planar_first_block`).
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta.Localization

open Assembly Contract

variable {d : ℕ}

theorem projectedPoincare_of_one_le (hd : 1 ≤ d) : Haar.ProjectedPoincare d :=
  fun U _ _ hv hg hder => projected_poincare hd U hv hg hder

theorem neumannBlock_omegaEff_pos (row : Row d) (hO : row.Obligations) : 0 < row.omegaEff := by
  unfold Row.omegaEff
  split_ifs with h2
  · norm_num
  · exact_mod_cast (hO.par2.2.2.2.2.2 h2).2.1

/-- `𝖫_k/κ_ω² = (5/54)9^{1-k}` away from the planar first block. -/
theorem haarL_div_kappaOmega_sq (row : Row d) (hO : row.Obligations) {k : ℕ}
    (hk : ¬(d = 2 ∧ k = 1)) :
    row.haarL k / row.kappaOmega ^ 2 = 5 / 54 * (9 / 9 ^ k) := by
  have hω := (neumannBlock_omegaEff_pos row hO).ne'
  unfold Row.haarL Row.kappaOmega Row.etaOmega
  rw [if_neg hk]
  field_simp
  ring

/-- `𝖫₁/π² = 1/(5π²) + 243/(10π⁶)` for `d = 2`. -/
theorem haarL_one_div_kappaOmega_sq_two (row : Row 2) :
    row.haarL 1 / row.kappaOmega ^ 2 =
      1 / (5 * Real.pi ^ 2) + 243 / (10 * Real.pi ^ 6) := by
  have hπ := Real.pi_ne_zero
  have h1 : row.haarL 1 = 1 / 5 + 243 / (10 * Real.pi ^ 4) := by simp [Row.haarL]
  have h2 : row.kappaOmega = Real.pi := by norm_num [Row.kappaOmega, Row.omegaEff]
  rw [h1, h2]
  field_simp

/-- **H5 + H6 (primitive on Haar blocks).** -/
theorem neumann_block_bound_proof (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ))
    (hO : row.Obligations) (n k : ℕ) (hk : 1 ≤ k)
    (F : Homogenization.Vec d → Homogenization.Vec d)
    (hF : ∀ i, MeasureTheory.MemLp (fun x => F x i) 2 (normalizedCubeMeasure (originCube d (n : ℤ))))
    (w : H1Function (openCubeSet (originCube d (n : ℤ))))
    (hw : IsNeumannPrimitive (originCube d (n : ℤ)) (vecIncrement (originCube d (n : ℤ)) k F) w) :
    Haar.energy (originCube d (n : ℤ)) w.toFun ≤
      row.haarL k / row.kappaOmega ^ 2 * ((3 : ℝ) ^ n) ^ 2 *
        vecEnergy (originCube d (n : ℤ)) (vecIncrement (originCube d (n : ℤ)) k F) := by
  have hd1 : 1 ≤ d := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    omega
  have hside : cubeScaleFactor (originCube d (n : ℤ)) = (3 : ℝ) ^ n := by
    simp [zpow_natCast]
  by_cases h21 : d = 2 ∧ k = 1
  · obtain ⟨rfl, rfl⟩ := h21
    rw [haarL_one_div_kappaOmega_sq_two, ← hside]
    exact planar_first_block _ F hF w hw
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have h := Haar.neumann_block_bound_of_projectedPoincare (projectedPoincare_of_one_le hd1)
      (originCube d (n : ℤ)) m F hF w hw
    rw [hside] at h
    refine h.trans (le_of_eq ?_)
    rw [haarL_div_kappaOmega_sq row hO h21]
    congr 1
    have h9 : ((3 : ℝ) ^ m) ^ 2 = 9 ^ m := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [div_pow, h9, pow_succ]
    field_simp
    ring

end GMCExplicitDelta.Localization
