module

public import GMCExplicitDelta.Certificates.Group4Moment

/-!
# Group 4: the Nat check of the profile bounds `ρ_r`

`rhoOK S FnN FnD FpN FpD ρ` checks `ρ₀ = S` and, for `1 ≤ r ≤ 32`,
`(ρ_r/S)^{31} ≥ (FnN/FnD)^{32-r} (FpN/FpD)^{32(r-1)}` in exact integer arithmetic.
-/

@[expose] public section

namespace GMCExplicitDelta.Certificates.Group4

/-- Integer check of the profile bounds. -/
def rhoOK (S FnN FnD FpN FpD : ℕ) (ρ : List ℕ) : Bool :=
  ρ.getD 0 0 == S && (List.range 33).all fun r =>
    r == 0 || Nat.ble (S ^ 31 * FnN ^ (32 - r) * FpN ^ (32 * (r - 1)))
      (ρ.getD r 0 ^ 31 * FnD ^ (32 - r) * FpD ^ (32 * (r - 1)))

theorem rhoOK_sound {S FnN FnD FpN FpD : ℕ} {ρ : List ℕ} (hS : 0 < S) (hFnD : 0 < FnD)
    (hFpD : 0 < FpD) (h : rhoOK S FnN FnD FpN FpD ρ = true) :
    ρ.getD 0 0 = S ∧ ∀ r : ℕ, 1 ≤ r → r ≤ 32 →
      ((FnN : ℝ) / FnD) ^ (32 - r) * ((FpN : ℝ) / FpD) ^ (32 * (r - 1)) ≤
        (((ρ.getD r 0 : ℕ) : ℝ) / S) ^ 31 := by
  simp only [rhoOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true] at h
  refine ⟨h.1, fun r hr1 hr => ?_⟩
  have h2 := h.2 r (by omega)
  rcases h2 with h2 | h2
  · omega
  have h3 := Nat.le_of_ble_eq_true h2
  have h4 : ((S : ℝ) ^ 31 * (FnN : ℝ) ^ (32 - r) * (FpN : ℝ) ^ (32 * (r - 1))) ≤
      (ρ.getD r 0 : ℝ) ^ 31 * (FnD : ℝ) ^ (32 - r) * (FpD : ℝ) ^ (32 * (r - 1)) := by
    exact_mod_cast h3
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  have hFnD' : (0 : ℝ) < FnD := by exact_mod_cast hFnD
  have hFpD' : (0 : ℝ) < FpD := by exact_mod_cast hFpD
  rw [div_pow, div_pow, div_pow, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
  calc (FnN : ℝ) ^ (32 - r) * (FpN : ℝ) ^ (32 * (r - 1)) * (S : ℝ) ^ 31
      = (S : ℝ) ^ 31 * (FnN : ℝ) ^ (32 - r) * (FpN : ℝ) ^ (32 * (r - 1)) := by ring
    _ ≤ (ρ.getD r 0 : ℝ) ^ 31 * (FnD : ℝ) ^ (32 - r) * (FpD : ℝ) ^ (32 * (r - 1)) := h4
    _ = (ρ.getD r 0 : ℝ) ^ 31 * ((FnD : ℝ) ^ (32 - r) * (FpD : ℝ) ^ (32 * (r - 1))) := by ring

end GMCExplicitDelta.Certificates.Group4
