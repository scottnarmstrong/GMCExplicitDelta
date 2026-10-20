module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic

/-!
# Ceiling and floor division on `ℕ`

`ceilDiv a b = (a + b - 1) / b` and `floorDiv a b = a / b`, with the real-number inequalities
needed to interpret fixed-point Nat computations.
-/

@[expose] public section

namespace GMCNumerics

/-- Ceiling division on naturals. -/
def ceilDiv (a b : ℕ) : ℕ := (a + b - 1) / b

/-- Floor division on naturals. -/
def floorDiv (a b : ℕ) : ℕ := a / b

theorem le_ceilDiv_mul {a b : ℕ} (hb : 0 < b) : a ≤ ceilDiv a b * b := by
  unfold ceilDiv
  have h1 := Nat.div_add_mod (a + b - 1) b
  have h2 := Nat.mod_lt (a + b - 1) hb
  have : b * ((a + b - 1) / b) = (a + b - 1) - (a + b - 1) % b := by omega
  rw [mul_comm] at this
  omega

theorem div_le_ceilDiv {a b : ℕ} (hb : 0 < b) : (a : ℝ) / b ≤ ceilDiv a b := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_le_iff₀ hb']
  exact_mod_cast le_ceilDiv_mul hb

theorem floorDiv_le_div {a b : ℕ} (hb : 0 < b) : (floorDiv a b : ℝ) ≤ a / b := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [le_div_iff₀ hb']
  exact_mod_cast Nat.div_mul_le_self a b

theorem ceilDiv_mono_left {a a' : ℕ} (b : ℕ) (h : a ≤ a') : ceilDiv a b ≤ ceilDiv a' b :=
  Nat.div_le_div_right (by omega)

theorem floorDiv_mono_left {a a' : ℕ} (b : ℕ) (h : a ≤ a') : floorDiv a b ≤ floorDiv a' b :=
  Nat.div_le_div_right h

end GMCNumerics
