module

public import GMCExplicitDelta.Contract.Obligations
public import GMCExplicitDelta.Contract.Rows
public import GMCExplicitDelta.Certificates.Obligations

/-!
# Intermediate statements: the numeric half of the contract

`rowTwo_obligations`, `rowThree_obligations`, `rowFour_obligations`: the numeric obligations of
§18 for the three certified rows (certified values in §18.4–18.6).

Intermediate statements of the proof, each proved in `GMCExplicitDelta/Proofs/`.
-/

@[expose] public section

namespace GMCExplicitDelta.Contract

/-- **Numeric target (§18.2–18.4).** The obligations of the `d = 2` row (`δ_* = .36665`). -/
theorem rowTwo_obligations : rowTwo.Obligations :=
  GMCExplicitDelta.Certificates.rowTwo_obligations_proof

/-- **Numeric target (§18.2–18.3, §18.5).** The obligations of the `d = 3` row (`δ_* = .18870`). -/
theorem rowThree_obligations : rowThree.Obligations :=
  GMCExplicitDelta.Certificates.rowThree_obligations_proof

/-- **Numeric target (§18.2–18.3, §18.6).** The obligations of the `d = 4` row (`δ_* = .15698`). -/
theorem rowFour_obligations : rowFour.Obligations :=
  GMCExplicitDelta.Certificates.rowFour_obligations_proof

end GMCExplicitDelta.Contract
