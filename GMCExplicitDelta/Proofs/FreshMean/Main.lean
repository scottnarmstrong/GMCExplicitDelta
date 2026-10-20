module

public import GMCExplicitDelta.Proofs.FreshMean.Return
public import GMCExplicitDelta.Steps.AssemblyFrozen

/-! # I8 target wrapper using the C8 identity

This wrapper imports the intermediate statements of the assembly; it uses the C8 identity
`Assembly.lintegral_frozenJ_eq_fMean` as an input.
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta.Assembly

open Contract

variable {d : ℕ}

/-- I8, with the exact target statement and its C8 dependency. -/
theorem freshMean_return_proof (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (M : SubdiffusiveProcess.Model.GMCModel d) {F : ℝ} (hF : 0 ≤ F) (L : ℕ)
    (hf : fMean M L (L + row.h) ≤ row.Fnext F) :
    ∀ z e : Homogenization.Vec d, vecNormSq e = 1 →
      ∫⁻ ω, ENNReal.ofReal (frozenJ M (L + row.h) (cubeAt z (L + row.h)) e e ω) ∂M.P.toMeasure ≤
        ENNReal.ofReal (row.meanpost M.delta F) := by
  exact freshMean_return_of_lintegral_frozenJ_eq_fMean
    (fun M L n z e he => lintegral_frozenJ_eq_fMean M L n z e he) row hd hO M hF L hf

end GMCExplicitDelta.Assembly
