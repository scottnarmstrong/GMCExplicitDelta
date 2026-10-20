module

public import GMCExplicitDelta.Proofs.FreshMean.Means
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.DualAnnealedMonotone

/-! # C9: monotonicity of the normalized annealed primal and dual energies -/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge

namespace GMCExplicitDelta.Assembly

variable {d : ℕ}

/-- The normalized primal mean is nonincreasing at every observation scale. -/
theorem annealedMean_alpha_antitone (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) :
    Antitone (alphaMean M L) := by
  intro a b hab
  rw [freshRet_alpha_eq, freshRet_alpha_eq]
  exact div_le_div_of_nonneg_right (antitone_abarScalarReadout M L hab) (driftSeed_ahom_pos M L).le

/-- The normalized dual mean is nonincreasing at every observation scale. -/
theorem annealedMean_beta_antitone (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) :
    Antitone (betaMean M L) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [freshRet_beta_eq, freshRet_beta_eq]
  have htrace := freshRet_trace_le (matLoewnerLE_abarStarInv_originCube_succ M L n)
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left htrace (driftSeed_ahom_pos M L).le) (Nat.cast_nonneg d)

end GMCExplicitDelta.Assembly

namespace GMCExplicitDelta.Localization

open Assembly Contract

variable {d : ℕ}

/-- C9, with the exact localization statement. -/
theorem alphaBeta_ge_one_antitone_proof (M : SubdiffusiveProcess.Model.GMCModel d) {D F : ℝ} (L : ℕ)
    (hP : InductionP M L D F) :
    (∀ n, L ≤ n → 1 ≤ alphaMean M L n ∧ 1 ≤ betaMean M L n) ∧
      ∀ a b, L ≤ a → a ≤ b → alphaMean M L b ≤ alphaMean M L a ∧ betaMean M L b ≤ betaMean M L a := by
  have _hP := hP
  refine ⟨fun n _ => freshRet_alpha_beta_ge_one M L n, ?_⟩
  intro a b _ hab
  exact ⟨annealedMean_alpha_antitone M L hab, annealedMean_beta_antitone M L hab⟩

end GMCExplicitDelta.Localization
