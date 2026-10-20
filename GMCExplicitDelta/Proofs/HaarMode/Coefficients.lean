module

public import GMCExplicitDelta.Proofs.HaarMode.Integrals

/-! # Finite-dimensional identities for the affine-cutoff constants -/

@[expose] public section

open Homogenization

namespace GMCExplicitDelta.Localization

variable {d : ℕ}

/-- Rewrite an erased product as a full product for coordinate expansion. -/
theorem haarMode_prod_erase {ι M : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid M]
    (f : ι → M) (i : ι) :
    (∏ k ∈ Finset.univ.erase i, f k) = ∏ k, if k = i then 1 else f k := by
  rw [← Fintype.prod_ite_mem]
  apply Finset.prod_congr rfl
  intro k _
  by_cases h : k = i <;> simp [h]

/-- The slope energy is κ²ω. -/
theorem haarMode_cosB (row : Contract.Row d) (h0 : 0 < row.omegaEff) :
    row.cosB = row.kappaOmega ^ 2 * row.omegaEff := by
  unfold Contract.Row.cosB Contract.Row.kappaOmega
  field_simp [h0.ne', Real.pi_ne_zero]
  ring

/-- The slope's second moment is κ²C* + A. -/
theorem haarMode_cosE (row : Contract.Row d) (h0 : 0 < row.omegaEff) :
    row.cosE = row.kappaOmega ^ 2 * row.cosCstar + row.cosA := by
  unfold Contract.Row.cosE Contract.Row.cosCstar Contract.Row.cosA Contract.Row.kappaOmega
  field_simp [h0.ne', Real.pi_ne_zero]
  ring

/-- The Hessian constant expressed in κ-scaled variables. -/
theorem haarMode_Hcirc (row : Contract.Row d) (h0 : 0 < row.omegaEff) :
    Real.pi ^ 2 * row.Hcirc = row.kappaOmega ^ 2 *
      ((d : ℝ) * row.omegaEff * row.cosA ^ (d - 1) + row.Wcirc) := by
  unfold Contract.Row.Hcirc Contract.Row.kappaOmega
  field_simp [h0.ne', Real.pi_ne_zero]
  ring

/-- The total affine-cutoff energy has exactly the contract coefficient Lcirc. -/
theorem haarMode_coeff_energy (row : Contract.Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ))
    (a : Homogenization.Vec d) :
    (∑ i, haarMode_quad row a (haarMode_gtype i)) = row.Lcirc * vecNormSq a := by
  classical
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl <;>
    simp [haarMode_quad, haarMode_prod_erase, Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_four,
      Fin.prod_univ_two, Fin.prod_univ_three, Fin.prod_univ_four,
      haarMode_gtype, haarMode_m0, haarMode_m2, Contract.Row.Lcirc, vecNormSq, vecDot] <;> ring

/-- The total weak-gradient energy has exactly the contract coefficient π²Hcirc. -/
theorem haarMode_coeff_gradient (row : Contract.Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ))
    (h0 : 0 < row.omegaEff) (a : Homogenization.Vec d) :
    (∑ i, ∑ j,
      (a j ^ 2 * (∏ k, haarMode_m0 row (haarMode_gtype i k)) +
        2 * a j * haarMode_cross row a (haarMode_gtype i) (haarMode_htype i j) +
        haarMode_quad row a (haarMode_htype i j))) = Real.pi ^ 2 * row.Hcirc * vecNormSq a := by
  classical
  rw [haarMode_Hcirc row h0]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl <;>
    simp [haarMode_quad, haarMode_cross, haarMode_prod_erase, Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_four,
      Fin.prod_univ_two, Fin.prod_univ_three, Fin.prod_univ_four,
      haarMode_gtype, haarMode_htype, haarMode_m0, haarMode_m2, haarMode_mix0, haarMode_mix1,
      Contract.Row.Wcirc, Contract.Row.Lcirc, vecNormSq, vecDot,
      haarMode_cosB row h0, haarMode_cosE row h0, Contract.Row.cosA] <;> ring

end GMCExplicitDelta.Localization
