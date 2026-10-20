module
public import GMCExplicitDelta.Statements.ExplicitCascadeTwo
public import GMCExplicitDelta.Statements.ExplicitCascadeThree
public import GMCExplicitDelta.Statements.ExplicitCascadeFour
public import GMCExplicitDelta.Statements.SourceVariance
public import GMCExplicitDelta.Statements.SourceExpMoment
public import GMCExplicitDelta.Statements.SourceEvenMoment
public import GMCExplicitDeltaAudit.Solution

/-!
# Axiom report

The axioms used by the three main theorems, the six statements of
`GMCExplicitDelta/Statements/` and the comparator solution. Each must be exactly
`propext`, `Classical.choice` and `Quot.sound`.
-/

#print axioms GMCExplicitDelta.explicit_cascade_two
#print axioms GMCExplicitDelta.explicit_cascade_three
#print axioms GMCExplicitDelta.explicit_cascade_four
#print axioms GMCExplicitDelta.source_variance
#print axioms GMCExplicitDelta.source_exp_moment
#print axioms GMCExplicitDelta.source_even_moment
#print axioms GMCExplicitDeltaAudit.explicit_cascade
