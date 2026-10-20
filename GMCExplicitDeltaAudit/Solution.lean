module
public import GMCExplicitDeltaAudit.SolutionBridge
public import GMCExplicitDelta.Statements.ExplicitCascadeTwo
public import GMCExplicitDelta.Statements.ExplicitCascadeThree
public import GMCExplicitDelta.Statements.ExplicitCascadeFour

/-!
# Proof of the challenge statement from the library

The challenge theorem, stated over the verbatim challenge vocabulary of
`GMCExplicitDeltaAudit.SolutionBasic`, follows from `GMCExplicitDelta.explicit_cascade_two`,
`GMCExplicitDelta.explicit_cascade_three` and `GMCExplicitDelta.explicit_cascade_four` through
the translation lemmas of `GMCExplicitDeltaAudit.SolutionBridge`.
-/

@[expose] public section
noncomputable section
namespace GMCExplicitDeltaAudit
open _root_.GMCExplicitDeltaAudit.SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal
/-- **The explicit cascade** in dimensions two, three and four, with the thresholds
`δ₀(2) = .36665`, `δ₀(3) = .18870`, `δ₀(4) = .15698` and the explicit constants `C₃₂(d)` and
`C_mean(d)` (library: `GMCExplicitDelta.explicit_cascade_two`, `_three`, `_four`). -/
theorem explicit_cascade :
    ExplicitCascade 2 (36665 / 100000) (23138371504 / 53772889) (230590996 / 53772889) ∧
    ExplicitCascade 3 (18870 / 100000) (89475125 / 1186923) (17849411 / 3560769) ∧
    ExplicitCascade 4 (15698 / 100000) (5918767600 / 61606801) (423596800 / 61606801) :=
  ⟨Conversion.transfer fun M hδ m n hmn z =>
      _root_.GMCExplicitDelta.explicit_cascade_two (Conversion.toModel M) hδ m n hmn z,
    Conversion.transfer fun M hδ m n hmn z =>
      _root_.GMCExplicitDelta.explicit_cascade_three (Conversion.toModel M) hδ m n hmn z,
    Conversion.transfer fun M hδ m n hmn z =>
      _root_.GMCExplicitDelta.explicit_cascade_four (Conversion.toModel M) hδ m n hmn z⟩
end GMCExplicitDeltaAudit
