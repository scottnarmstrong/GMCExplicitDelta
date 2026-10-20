module

public import GMCExplicitDelta.Certificates.Group3TwoBar
public import GMCExplicitDelta.Certificates.Group3ThreeBar
public import GMCExplicitDelta.Certificates.Group3FourBar

/-!
# Numeric obligations, group 3, for the three rows

The structure `Row.Group3 row` lists the fields `geo1, geo2, geo4, bar1, bar2` of
`Row.Obligations` with exactly the same statements; `rowTwo_group3` etc. prove it.
-/

@[expose] public section

open Real

namespace GMCExplicitDelta.Certificates

open GMCExplicitDelta.Contract

/-- The group 3 fields of `Row.Obligations`, verbatim. -/
structure Group3 {d : ℕ} (row : Row d) : Prop where
  geo1 : 0 < row.locBracket ∧ (d ≠ 2 → 0 < row.Lcirc ∧ 0 < row.Rcirc ∧ 0 < row.Hcirc)
  geo2 : (d = 2 → 1 < row.qs ∧ row.qs < 3 ∧ row.us < 3 ∧
      ∀ k : ℕ, 1 ≤ k → row.haarL k ≤ 9 / 9 ^ k ∧ 1 + 2 * row.haarL k ≤ 3) ∧ row.rhoS < 1
  geo4 : 0 < row.tauAbs ∧ row.tauAbs < 1
  bar1 : 0 < row.Z ∧ (row.Z : ℝ) < (row.Mwin : ℝ) ∧ 0 < row.barrier row.D row.F
  bar2 : d = 2 →
    0 ≤ nMatch row.vT0 (row.vT1 row.D row.F) (row.uStar row.F) ∧
    0 ≤ nMatch row.vF0 (row.vF1 row.D row.F) (row.uStar row.F) ∧
    row.t4Loss row.F ≤
      row.t4b * mMatch row.vT0 (row.vT1 row.D row.F) (row.uStar row.F) +
        row.t4c * mMatch row.vF0 (row.vF1 row.D row.F) (row.uStar row.F) ∧
    0 < (1 - row.tauAbs) * √(row.Z : ℝ) - row.t4R row.D row.F 1 -
      (row.Mwin : ℝ) * (row.badBudget : ℝ) / √(row.Z : ℝ)

theorem rowTwo_group3 : Group3 rowTwo :=
  ⟨G3.Two.geo1, G3.Two.geo2, G3.Two.geo4,
    ⟨by norm_num [rowTwo], G3.Two.hZM, G3.Two.bar1_pos⟩, G3.Two.bar2⟩

theorem rowThree_group3 : Group3 rowThree :=
  ⟨G3.Three.geo1, G3.Three.geo2, G3.Three.geo4,
    ⟨by norm_num [rowThree], G3.Three.hZM, G3.Three.bar1_pos⟩,
    fun h => absurd h (by norm_num)⟩

theorem rowFour_group3 : Group3 rowFour :=
  ⟨G3.Four.geo1, G3.Four.geo2, G3.Four.geo4,
    ⟨by norm_num [rowFour], G3.Four.hZM, G3.Four.bar1_pos⟩,
    fun h => absurd h (by norm_num)⟩

end GMCExplicitDelta.Certificates
