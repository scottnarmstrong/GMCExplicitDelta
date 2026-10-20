module

public import GMCExplicitDelta.Certificates.Group4RetTwo
public import GMCExplicitDelta.Certificates.Group4RetThree
public import GMCExplicitDelta.Certificates.Group4RetFour

/-!
# Numeric obligations, group 4 (the returns), for the three rows

The structure `Row.Group4 row` lists the fields `ret1..ret4` of `Row.Obligations` with exactly the
same statements; `rowTwo_group4` etc. prove it.
-/

@[expose] public section

namespace GMCExplicitDelta.Certificates

open GMCExplicitDelta.Contract

/-- The group 4 fields of `Row.Obligations`, verbatim. -/
structure Group4 {d : ℕ} (row : Row d) : Prop where
  ret1 : row.post row.deltaStar row.D row.F < row.D
  ret2 : row.meanpost row.deltaStar row.F < row.F
  ret3 : row.seed row.deltaStar < row.D
  ret4 : row.meanseed row.deltaStar < row.F

theorem rowTwo_group4 : Group4 rowTwo :=
  ⟨Group4.rowTwo_rets.1, Group4.rowTwo_rets.2.1, Group4.rowTwo_rets.2.2.1, Group4.rowTwo_rets.2.2.2⟩

theorem rowThree_group4 : Group4 rowThree :=
  ⟨Group4.rowThree_rets.1, Group4.rowThree_rets.2.1, Group4.rowThree_rets.2.2.1,
    Group4.rowThree_rets.2.2.2⟩

theorem rowFour_group4 : Group4 rowFour :=
  ⟨Group4.rowFour_rets.1, Group4.rowFour_rets.2.1, Group4.rowFour_rets.2.2.1, Group4.rowFour_rets.2.2.2⟩

end GMCExplicitDelta.Certificates
