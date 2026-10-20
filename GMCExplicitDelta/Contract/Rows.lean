module

public import GMCExplicitDelta.Contract.Row
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum

/-!
# Contract layer: the three certified rows

The literals are the three certified rows (one per dimension). Decimals are kept in their decimal
shape (`.36665 = 36665/100000`).

The lemmas `rowX_deltaStar`, `rowX_C32`, `rowX_Cmean` rewrite the row's threshold and constants to
the literals of the main theorems `explicit_cascade_two/three/four`.
-/

@[expose] public section

namespace GMCExplicitDelta.Contract

/-- The certified row in dimension two (row `d = 2`). `young`, `width`, `epsSub` are recorded but unused in `d = 2`
(the planar route uses `ℓ_v = 3`, `t = 23/2`, the full cosine and `κ_h = 0`). -/
def rowTwo : Row 2 where
  deltaStar := (36665 / 100000 : ℚ)
  h := 261
  g := 55
  nu := 5
  gridN := 71
  D := (5784592876 / 100000000 : ℚ)
  F := (57647749 / 100000000 : ℚ)
  s := (12604 / 100000 : ℚ)
  R := (283478719 / 100000000 : ℚ)
  epsilon := (11492862 / 100000000 : ℚ)
  young := (2203457714 / 100000000 : ℚ)
  width := (40743153 / 100000000 : ℚ)
  badBudget := (24609 / 100000000 : ℚ)
  Z := (344099 / 2000 : ℚ)
  eta := (1 : ℚ)
  epsSub := (1 / 100 : ℚ)
  haarCutoff := 56
  historyCutoff := 12
  bandTerms := 64

theorem rowTwo_deltaStar : (rowTwo.deltaStar : ℝ) = 36665 / 100000 := by norm_num [rowTwo]

theorem rowTwo_C32 : (rowTwo.D : ℝ) / (rowTwo.deltaStar : ℝ) ^ 2 = 23138371504 / 53772889 := by
  norm_num [rowTwo]

theorem rowTwo_Cmean : (rowTwo.F : ℝ) / (rowTwo.deltaStar : ℝ) ^ 2 = 230590996 / 53772889 := by
  norm_num [rowTwo]

/-- The certified row in dimension three (row `d = 3`). -/
def rowThree : Row 3 where
  deltaStar := (18870 / 100000 : ℚ)
  h := 398
  g := 67
  nu := 5
  gridN := 39
  D := (268425375 / 100000000 : ℚ)
  F := (17849411 / 100000000 : ℚ)
  s := (9604 / 100000 : ℚ)
  R := (183997685 / 100000000 : ℚ)
  epsilon := (11946918 / 100000000 : ℚ)
  young := (753845145 / 100000000 : ℚ)
  width := (34324872 / 100000000 : ℚ)
  badBudget := (46252 / 100000000 : ℚ)
  Z := (2686531 / 10000 : ℚ)
  eta := (44565937389194283091677 / 62500000000000000000000 : ℚ)
  epsSub := (1 / 100 : ℚ)
  haarCutoff := 48
  historyCutoff := 12
  bandTerms := 64

theorem rowThree_deltaStar : (rowThree.deltaStar : ℝ) = 18870 / 100000 := by norm_num [rowThree]

theorem rowThree_C32 : (rowThree.D : ℝ) / (rowThree.deltaStar : ℝ) ^ 2 = 89475125 / 1186923 := by
  norm_num [rowThree]

theorem rowThree_Cmean : (rowThree.F : ℝ) / (rowThree.deltaStar : ℝ) ^ 2 = 17849411 / 3560769 := by
  norm_num [rowThree]

/-- The certified row in dimension four (row `d = 4`). -/
def rowFour : Row 4 where
  deltaStar := (15698 / 100000 : ℚ)
  h := 537
  g := 86
  nu := 5
  gridN := 27
  D := (236750704 / 100000000 : ℚ)
  F := (16943872 / 100000000 : ℚ)
  s := (10215 / 100000 : ℚ)
  R := (180694423 / 100000000 : ℚ)
  epsilon := (9841843 / 100000000 : ℚ)
  young := (1777499128 / 100000000 : ℚ)
  width := (26800003 / 100000000 : ℚ)
  badBudget := (41618 / 100000000 : ℚ)
  Z := (460219 / 1250 : ℚ)
  eta := (613127844724193305266181 / 1000000000000000000000000 : ℚ)
  epsSub := (1 / 100 : ℚ)
  haarCutoff := 48
  historyCutoff := 12
  bandTerms := 64

theorem rowFour_deltaStar : (rowFour.deltaStar : ℝ) = 15698 / 100000 := by norm_num [rowFour]

theorem rowFour_C32 : (rowFour.D : ℝ) / (rowFour.deltaStar : ℝ) ^ 2 = 5918767600 / 61606801 := by
  norm_num [rowFour]

theorem rowFour_Cmean : (rowFour.F : ℝ) / (rowFour.deltaStar : ℝ) ^ 2 = 423596800 / 61606801 := by
  norm_num [rowFour]

end GMCExplicitDelta.Contract
