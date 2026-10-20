module

public import GMCExplicitDelta.Proofs.EnergyTest.Energy
public import GMCExplicitDelta.Proofs.EnergyTest.Duality

/-! L1 for the exact localized energy, frozen flux and test field. -/

@[expose] public section

open Homogenization Homogenization.Book MeasureTheory
open scoped ENNReal

namespace GMCExplicitDelta.Localization

open Assembly Contract
variable {d : ℕ}

theorem loc_L1_proof (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) (p q : Homogenization.Vec d) :
    ENNReal.ofReal (locEnergy row M L n p q ω) ^ 2 ≤
      haarDual (originCube d (n : ℤ)) row.qs (frozenFlux M L (cubeAt 0 n) p q ω) *
        haarPrimal (originCube d (n : ℤ)) row.qs
          (locTestField row n (frozenH1 M L (cubeAt 0 n) p q ω).toFun) := by
  let Q := originCube d (n : ℤ)
  have hU : ((cubeAt 0 n : Ch02.Domain d) : Set (Vec d)) = openCubeSet Q := cellAt_zero_coe Q
  have hF (i : Fin d) : MemLp (fun x => frozenFlux M L (cubeAt 0 n) p q ω x i) 2 (normalizedCubeMeasure Q) :=
    memL2On_openCubeSet_normalizedCubeMeasure (by rw [← hU]; exact EnergyTest.frozenFlux_memL2 M L _ p q ω i)
  have hG (i : Fin d) : MemLp (fun x => locTestField row n (frozenH1 M L (cubeAt 0 n) p q ω).toFun x i)
      2 (normalizedCubeMeasure Q) :=
    memL2On_openCubeSet_normalizedCubeMeasure (by rw [← hU]; exact EnergyTest.locTestField_memL2 row hO M L n p q ω i)
  have hs : 0 < (row.s : ℝ) := by exact_mod_cast hO.par1.2.2.2.2.2.1
  have hq : 1 < row.qs := Real.one_lt_rpow (by norm_num) (by linarith only [hs])
  have hh := EnergyTest.ofReal_vector_pairing_sq_le Q hq hF hG
  refine le_trans (pow_le_pow_left' (ENNReal.ofReal_le_ofReal ?_) 2) hh
  rw [EnergyTest.locEnergy_eq_neg_pairing row hO M L n p q ω]
  exact neg_le_abs _

end GMCExplicitDelta.Localization
