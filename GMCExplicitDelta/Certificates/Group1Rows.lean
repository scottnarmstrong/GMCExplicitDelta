module

public import GMCExplicitDelta.Certificates.Group1Common
public import GMCExplicitDelta.Contract.Rows

/-!
# Numeric obligations, group 1, for the three rows

The structure `Row.Group1 row` lists the fields `src1..src7, avg1, avg2, sph, par1..par3, var1,
fin1, band1` of `Row.Obligations` with exactly the same statements; `rowTwo_group1` etc. prove it.
-/

@[expose] public section

open Real

namespace GMCExplicitDelta.Certificates

open GMCExplicitDelta.Contract

/-- The group 1 fields of `Row.Obligations`, verbatim. -/
structure Group1 {d : ℕ} (row : Row d) : Prop where
  src1 : (3 - 2 * √2) / 16 < (proxyA : ℝ)
  src2 : Real.log 2 / (35 + (13 + 2 * √2) * π ^ 2) < (varU : ℝ)
  src3 : (varU : ℝ) < proxyA ∧ (kappaQ1 : ℝ) < (proxyA : ℝ) / 2 ∧
    (varU : ℝ) / 2 + 4 * (Real.exp ((proxyA : ℝ) / 8) - 1 - (proxyA : ℝ) / 8) < kappaQ1
  src4 : 4 / 3 * (√3 - 1) ≤ (ratioC2 : ℝ)
  src5 : 72 * (√3 - 1) / (5 * (Real.exp 3 - Real.exp 1)) ≤ (ratioC3 : ℝ)
  src6 : 0 < ratioC3 ∧ ratioC3 < ratioC2 ∧ ratioC2 < 1 ∧ 0 ≤ varU ∧ varU ≤ proxyA
  src7 : row.deltaStar ≤ 1 / 2
  avg1 : 0 < sphereLower d ∧ 1 < sigmaNorm d ^ 32 * sphereLower d
  avg2 : ∀ k < 16, assocStirling 32 (k + 1) = assocStirling32Table.getD k 0
  sph : (sphereFactorPow d : ℝ) =
    √π * Real.Gamma (32 + (d : ℝ) / 2) / (Real.Gamma ((d : ℝ) / 2) * Real.Gamma (32 + 1 / 2))
  par1 : 0 < row.D ∧ 0 < row.F ∧ row.F ≤ min row.D 1 ∧ max row.nu 2 ≤ row.g ∧ row.g ≤ row.h ∧
    0 < row.s ∧ row.s < 1 / 2 ∧ (d : ℚ) / 32 < 2 * row.s
  par2 : 1 < row.R ∧ 0 < row.epsilon ∧ row.nu + 1 ≤ row.g ∧ 1 ≤ row.gridN ∧ 0 < row.badBudget ∧
    (d ≠ 2 → 0 < row.young ∧ 0 < row.width ∧ row.width ≤ 1 / 2)
  par3 : 0 < row.eta ∧ row.eta ≤ 1
  var1 : 0 < row.rhoV ∧ row.rhoV < 1
  fin1 : row.Fnext row.F ≤ row.Dnext row.D row.F
  band1 : bandNormBound row.deltaStar < (row.bandTerms : ℝ) + 2

/-- `Bbar32` is nonnegative for nonnegative caps. -/
theorem Bbar32_nonneg (n : ℕ) {D F : ℝ} (hD : 0 ≤ D) (hF : 0 ≤ F) : 0 ≤ Bbar32 n D F := by
  unfold Bbar32
  refine Real.rpow_nonneg (Finset.sum_nonneg fun k _ => ?_) _
  have hT : 0 ≤ Tvarpi D F := by
    unfold Tvarpi varpi
    exact Real.rpow_nonneg (le_min_iff.2 ⟨div_nonneg hF hD, zero_le_one⟩) _
  positivity

/-- Generic form of O.fin.1. -/
theorem fin1_of {d : ℕ} (row : Row d) (hD : 0 < row.D) (hF : 0 < row.F) (hFD : row.F ≤ row.D)
    (hM : (row.Z : ℝ) ≤ (row.Mwin : ℝ)) (hMpos : 0 < row.Mwin)
    (hσ : 0 ≤ sigmaNorm d) : row.Fnext row.F ≤ row.Dnext row.D row.F := by
  have hD' : (0 : ℝ) < row.D := by exact_mod_cast hD
  have hF' : (0 : ℝ) < row.F := by exact_mod_cast hF
  have hFD' : (row.F : ℝ) ≤ row.D := by exact_mod_cast hFD
  have hM' : (0 : ℝ) < row.Mwin := by exact_mod_cast hMpos
  have ht : row.tStar ≤ 1 := by
    unfold Row.tStar; rw [div_le_one hM']; exact hM
  have h1 : row.Fnext row.F ≤ row.F := by
    unfold Row.Fnext; nlinarith
  have hB := Bbar32_nonneg (3 ^ (d * (row.h - 1))) hD'.le hF'.le
  have hσ' : (0 : ℝ) ≤ sigmaNorm d := by exact_mod_cast hσ
  have h2 : (row.F : ℝ) ≤ row.F + (sigmaNorm d : ℝ) * row.D * Bbar32 (3 ^ (d * (row.h - 1))) row.D row.F := by
    have : 0 ≤ (sigmaNorm d : ℝ) * row.D * Bbar32 (3 ^ (d * (row.h - 1))) row.D row.F := by positivity
    linarith
  unfold Row.Dnext nativeCap
  exact h1.trans (le_min hFD' h2)

theorem rowTwo_group1 : Group1 rowTwo := by
  refine ⟨src1_proof, src2_proof, src3_proof, src4_proof, src5_proof, src6_proof, ?_, ?_, avg2_proof,
    sph_two, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [rowTwo]
  · decide +kernel
  · norm_num [rowTwo]
  · norm_num [rowTwo]
  · norm_num [rowTwo]
  · norm_num [Row.rhoV, rowTwo]
  · refine fin1_of rowTwo (by norm_num [rowTwo]) (by norm_num [rowTwo]) (by norm_num [rowTwo])
      (by norm_num [Row.Mwin, rowTwo]) (by norm_num [Row.Mwin, rowTwo]) (by norm_num [sigmaNorm])
  · norm_num [bandNormBound, proxyA, rowTwo]

theorem rowThree_group1 : Group1 rowThree := by
  refine ⟨src1_proof, src2_proof, src3_proof, src4_proof, src5_proof, src6_proof, ?_, ?_, avg2_proof,
    sph_three, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [rowThree]
  · decide +kernel
  · norm_num [rowThree]
  · norm_num [rowThree]
  · norm_num [rowThree]
  · norm_num [Row.rhoV, rowThree]
  · refine fin1_of rowThree (by norm_num [rowThree]) (by norm_num [rowThree]) (by norm_num [rowThree])
      (by norm_num [Row.Mwin, rowThree]) (by norm_num [Row.Mwin, rowThree]) (by norm_num [sigmaNorm])
  · norm_num [bandNormBound, proxyA, rowThree]

theorem rowFour_group1 : Group1 rowFour := by
  refine ⟨src1_proof, src2_proof, src3_proof, src4_proof, src5_proof, src6_proof, ?_, ?_, avg2_proof,
    sph_four, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [rowFour]
  · decide +kernel
  · norm_num [rowFour]
  · norm_num [rowFour]
  · norm_num [rowFour]
  · norm_num [Row.rhoV, rowFour]
  · refine fin1_of rowFour (by norm_num [rowFour]) (by norm_num [rowFour]) (by norm_num [rowFour])
      (by norm_num [Row.Mwin, rowFour]) (by norm_num [Row.Mwin, rowFour]) (by norm_num [sigmaNorm])
  · norm_num [bandNormBound, proxyA, rowFour]

end GMCExplicitDelta.Certificates
