module

public import GMCExplicitDelta.Proofs.PlanarBlock.SpectralSum

/-! The finite exceptional planar spectrum below the cutoff five. -/

@[expose] public section

noncomputable section

namespace GMCExplicitDelta.Localization

/-- Squared integer frequency. -/
def planarBlock_modeSize (p : Fin 2 → ℤ) : ℤ := p 0 ^ 2 + p 1 ^ 2

/-- A finite square containing all exceptional frequencies. -/
def planarBlock_lowModes : Finset (Fin 2 → ℤ) :=
  (({-2, -1, 0, 1, 2} : Finset ℤ) ×ˢ {-2, -1, 0, 1, 2}).image
    (fun z => ![z.1, z.2])

/-- Extra inverse eigenvalue weight above the uniform cutoff-five weight. -/
def planarBlock_lowWeight (r : ℝ) (p : Fin 2 → ℤ) : ℝ :=
  if planarBlock_modeSize p = 1 then 4 / (5 * r)
  else if planarBlock_modeSize p = 2 then 3 / (10 * r)
  else if planarBlock_modeSize p = 4 then 1 / (20 * r) else 0

theorem planarBlock_mem_lowModes (p : Fin 2 → ℤ) :
    p ∈ planarBlock_lowModes ↔
      p 0 ∈ ({-2, -1, 0, 1, 2} : Finset ℤ) ∧
      p 1 ∈ ({-2, -1, 0, 1, 2} : Finset ℤ) := by
  simp only [planarBlock_lowModes, Finset.mem_image, Finset.mem_product]
  constructor
  · rintro ⟨⟨x, y⟩, h, rfl⟩
    exact h
  · intro h
    refine ⟨(p 0, p 1), h, ?_⟩
    ext i
    fin_cases i <;> rfl

theorem planarBlock_mem_lowModes_of_size (p : Fin 2 → ℤ) (hp : planarBlock_modeSize p ≤ 4) :
    p ∈ planarBlock_lowModes := by
  have hx : -2 ≤ p 0 ∧ p 0 ≤ 2 := by
    dsimp [planarBlock_modeSize] at hp
    constructor <;> nlinarith [sq_nonneg (p 1)]
  have hy : -2 ≤ p 1 ∧ p 1 ≤ 2 := by
    dsimp [planarBlock_modeSize] at hp
    constructor <;> nlinarith [sq_nonneg (p 0)]
  rw [planarBlock_mem_lowModes]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

theorem planarBlock_integer_spectrum (x y : ℤ) (h : x ≠ 0 ∨ y ≠ 0) :
    x ^ 2 + y ^ 2 = 1 ∨ x ^ 2 + y ^ 2 = 2 ∨ x ^ 2 + y ^ 2 = 4 ∨
      5 ≤ x ^ 2 + y ^ 2 := by
  by_cases hg : 5 ≤ x ^ 2 + y ^ 2
  · exact Or.inr (Or.inr (Or.inr hg))
  have hx : -2 ≤ x ∧ x ≤ 2 := by constructor <;> nlinarith [sq_nonneg y]
  have hy : -2 ≤ y ∧ y ≤ 2 := by constructor <;> nlinarith [sq_nonneg x]
  rcases hx with ⟨hxlo, hxhi⟩
  rcases hy with ⟨hylo, hyhi⟩
  interval_cases x <;> interval_cases y <;> norm_num at *

theorem planarBlock_lowWeight_nonneg {r : ℝ} (hr : 0 < r) (p : Fin 2 → ℤ) :
    0 ≤ planarBlock_lowWeight r p := by
  unfold planarBlock_lowWeight
  split_ifs <;> positivity

/-- The finite correction supplies the reciprocal eigenvalue at every nonzero mode. -/
theorem planarBlock_lowWeight_gap {r : ℝ} (hr : 0 < r) (p : Fin 2 → ℤ) (hp : p ≠ 0) :
    1 ≤ (1 / (5 * r) + if p ∈ planarBlock_lowModes then planarBlock_lowWeight r p else 0) *
      (r * (planarBlock_modeSize p : ℝ)) := by
  have hne : p 0 ≠ 0 ∨ p 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hp
    ext i
    fin_cases i <;> simp_all
  rcases planarBlock_integer_spectrum (p 0) (p 1) hne with h1 | h2 | h4 | hhigh
  · have hm := planarBlock_mem_lowModes_of_size p (show planarBlock_modeSize p ≤ 4 by dsimp [planarBlock_modeSize]; omega)
    simp only [ite_eq_left hm, planarBlock_lowWeight, planarBlock_modeSize, h1, Int.cast_one, ite_true]
    field_simp [hr.ne']
    linarith only [hr]
  · have hm := planarBlock_mem_lowModes_of_size p (show planarBlock_modeSize p ≤ 4 by dsimp [planarBlock_modeSize]; omega)
    simp only [ite_eq_left hm, planarBlock_lowWeight, planarBlock_modeSize, h2]
    norm_num
    field_simp [hr.ne']
    linarith only [hr]
  · have hm := planarBlock_mem_lowModes_of_size p (show planarBlock_modeSize p ≤ 4 by dsimp [planarBlock_modeSize]; omega)
    simp only [ite_eq_left hm, planarBlock_lowWeight, planarBlock_modeSize, h4]
    norm_num
    field_simp [hr.ne']
    linarith only [hr]
  · have hN : (5 : ℝ) ≤ (planarBlock_modeSize p : ℝ) := by exact_mod_cast hhigh
    have hweight : 0 ≤ if p ∈ planarBlock_lowModes then planarBlock_lowWeight r p else 0 := by
      split_ifs
      · exact planarBlock_lowWeight_nonneg hr p
      · exact le_rfl
    have hbase : 1 ≤ 1 / (5 * r) * (r * (planarBlock_modeSize p : ℝ)) := by
      have heq : 1 / (5 * r) * (r * (planarBlock_modeSize p : ℝ)) =
          (planarBlock_modeSize p : ℝ) / 5 := by field_simp [hr.ne']
      rw [heq]
      linarith only [hN]
    refine hbase.trans ?_
    apply mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hweight)
    exact mul_nonneg hr.le (le_trans (by norm_num) hN)

end GMCExplicitDelta.Localization
