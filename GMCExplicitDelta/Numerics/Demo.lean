module

public import GMCExplicitDelta.Numerics.NatMatrix
public import GMCExplicitDelta.Numerics.DemoData

/-!
# End-to-end demo

The Nat part is discharged by `decide +kernel` (no `native_decide`); the computational
definitions live in `NatMatrix.lean` and the data in `DemoData.lean`, so this also checks that
the kernel unfolds exposed definitions across module boundaries.
-/

@[expose] public section

namespace GMCNumerics.Demo

open Matrix

/-! ### A 3 × 3 example (scale 1000) -/

/-- Fixed-point lower-triangular matrix. -/
def B3 : List (List ℕ) := [[1000, 0, 0], [200, 900, 0], [50, 300, 800]]
/-- Its rounded-up tenth power. -/
def R3 : List (List ℕ) := [[1000, 0, 0], [1305, 350, 0], [1456, 726, 109]]
/-- The all-ones vector. -/
def v3 : List ℕ := [1000, 1000, 1000]

theorem demo3_nat : leM (powUp 1000 3 4 B3 10) R3 = true := by decide +kernel

/-- Every real nonnegative matrix below `B3 / 1000` has tenth power below `R3 / 1000`. -/
theorem demo3_matrix (X : Matrix (Fin 3) (Fin 3) ℝ) (hX : Dom 1000 3 X B3) :
    ∀ i j, (X ^ 10) i j ≤ toReal 1000 3 R3 i j :=
  powUp_le_sound (fuel := 4) (by norm_num) (by norm_num) (by decide +kernel) demo3_nat hX

theorem demo3_check : checkVec 1000 3 4 B3 10 v3 2 2291 = true := by decide +kernel

theorem demo3_vec (X : Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 3 → ℝ)
    (hX : Dom 1000 3 X B3) (hx : DomV 1000 3 x v3) :
    ((X ^ 10) *ᵥ x) 2 ≤ (2291 : ℝ) / 1000 :=
  checkVec_sound (fuel := 4) (i := 2) (by norm_num) (by norm_num) (by norm_num) demo3_check hX hx

/-! ### The d = 4 one-band matrix (33 × 33, scale 10^60, power 537) -/

theorem demo4_nat : leM (powUp S4 33 10 B4 537) R4 = true := by decide +kernel

/-- `(toReal B4)^537` is entrywise below the rounded-up power `R4`. -/
theorem demo4_matrix : ∀ i j, ((toReal S4 33 B4) ^ 537) i j ≤ toReal S4 33 R4 i j :=
  powUp_le_sound (fuel := 10) (by unfold S4; norm_num) (by norm_num) (by decide +kernel)
    demo4_nat (Dom_toReal S4 33 B4)

theorem demo4_check : checkVec S4 33 10 B4 537 v4 32 c4 = true := by decide +kernel

/-- Vector bound for any nonnegative `X ≤ B4/S4` and `x ≤ 1`. -/
theorem demo4_vec (X : Matrix (Fin 33) (Fin 33) ℝ) (x : Fin 33 → ℝ)
    (hX : Dom S4 33 X B4) (hx : DomV S4 33 x v4) :
    ((X ^ 537) *ᵥ x) 32 ≤ (c4 : ℝ) / S4 :=
  checkVec_sound (fuel := 10) (i := 32) (by unfold S4; norm_num) (by norm_num) (by norm_num)
    demo4_check hX hx

end GMCNumerics.Demo
