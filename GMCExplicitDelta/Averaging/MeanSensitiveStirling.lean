module

public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.List.Range

/-!
# Associated Stirling numbers of the second kind

`assocStirling p k` counts partitions of a `p`-set into `k` blocks of size at least `2`, defined by
the recurrence `𝒜(0,0) = 1`, `𝒜(p,k) = k 𝒜(p-1,k) + (p-1) 𝒜(p-2,k-1)`.
-/

@[expose] public section

namespace GMCExplicitDelta.Averaging

/-- Associated Stirling numbers of the second kind (partitions into blocks of size `≥ 2`). -/
def assocStirling : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | 1, _ => 0
  | _ + 2, 0 => 0
  | p + 2, k + 1 => (k + 1) * assocStirling (p + 1) (k + 1) + (p + 1) * assocStirling p k

theorem assocStirling_zero_zero : assocStirling 0 0 = 1 := rfl

theorem assocStirling_succ_succ (p k : ℕ) :
    assocStirling (p + 2) (k + 1) =
      (k + 1) * assocStirling (p + 1) (k + 1) + (p + 1) * assocStirling p k := rfl

theorem assocStirling_succ_zero (p : ℕ) : assocStirling (p + 2) 0 = 0 := rfl

theorem assocStirling_one (k : ℕ) : assocStirling 1 k = 0 := rfl

/-- The values `𝒜(32,k)`, `k = 1, …, 16`. -/
theorem assocStirling_thirtyTwo_values :
    (List.range 16).map (fun k => assocStirling 32 (k + 1)) =
      [1, 2147483615, 308800190920486, 765011543314355365, 187128474745367109190,
        9648191836041940120446, 154227582326730813420156, 948856977801169301069205,
        2550133124516049612389850, 3217076814220214136741550, 1967326750353779714399500,
        581105308935958505448750, 79198178493972888850500, 4449180413533177822500,
        79318164037837725000, 191898783962510625] := by
  decide +kernel

/-- `𝒜(32,16) = 31!!`. -/
theorem assocStirling_thirtyTwo_sixteen : assocStirling 32 16 = 191898783962510625 := by
  decide +kernel

end GMCExplicitDelta.Averaging
