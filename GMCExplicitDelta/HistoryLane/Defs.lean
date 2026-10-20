module

public import GMCExplicitDelta.HistoryLane.Split
public import GMCExplicitDelta.HistoryLane.Consts

/-!
# History lane: model vocabulary of the fine source history (G3, G4)

* `cutoffRatio M k L ω x = b_L(x)/b_k(x)` with `b_m = a_m/ā_m` (the factor `ρ = e^{Z_{k,L} - c_{k,L}}`
  of G3, N2); it depends on the layers `g_{k+1}, …, g_L` and the deterministic normalizations only.
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta.Assembly

open Contract

variable {d : ℕ}

/-- `ρ(x) = b_L(x)/b_k(x)` for `b_m = a_m/ā_m` (G3). -/
noncomputable def cutoffRatio (M : SubdiffusiveProcess.Model.GMCModel d) (k L : ℕ)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) (x : Homogenization.Vec d) : ℝ :=
  (SubdiffusiveProcess.Model.aCutoff M L ω x / ahom M L) /
    (SubdiffusiveProcess.Model.aCutoff M k ω x / ahom M k)

end GMCExplicitDelta.Assembly
