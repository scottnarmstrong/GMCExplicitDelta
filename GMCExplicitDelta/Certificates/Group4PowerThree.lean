module

public import GMCExplicitDelta.Certificates.Group4BandThree
public import GMCExplicitDelta.Certificates.Group4Check

/-!
# Group 4, row three: the matrix power and the fresh/seed moment bounds (kernel certificate)

`rhoThree` is the rounded-up profile `ρ_r ≥ (F_next^{32-r} (F + 10^{-30})^{32(r-1)})^{1/31}`
at scale `10^24` (so `μ_r ≤ ρ_r`); `cFreshThree` bounds `∑_r (𝐐^h)_{32,r} ρ_r`, and `cSeedThree` bounds
`∑_r (𝐐^h)_{32,r} (X/S)^r` with `X = 1000000000000000000000`.
-/

@[expose] public section

open GMCNumerics

namespace GMCExplicitDelta.Certificates.Group4

/-- The profile bounds, scale `10^24`. -/
def rhoThree : List ℕ := [1000000000000000000000000, 144436734889280120481928, 25957780716895902021435, 4665062390554368837777, 838392439828241788485, 150673629699864156150, 27078658642941446248, 4866503550498913693, 874594902181091165, 157179838663167779, 28247936982674067, 5076643102345348, 912360616083153, 163966990981713, 29467705705029, 5295856649678, 951757083999, 171047218017, 30740145026, 5524536015, 992854724, 178433175, 32067530, 5763090, 1035727, 186139, 33453, 6012, 1081, 195, 35, 7, 2]

theorem rho_check_three : rhoOK (10 ^ 24) 47952995983241 332000000000000 178494110000000000000000000001 1000000000000000000000000000000 rhoThree = true := by
  decide +kernel

/-- Bound for the fresh moment, scale `10^24`. -/
def cFreshThree : ℕ := 264758002996450785181979592281851049

/-- Bound for the seed sum, scale `10^24`. -/
def cSeedThree : ℕ := 1624373645250543715163189732

set_option maxRecDepth 100000 in
theorem power_check_three :
    (checkVec (10 ^ 24) 33 10 bandThree 398 rhoThree 32 cFreshThree &&
      checkVec (10 ^ 24) 33 10 bandThree 398 (powList (10 ^ 24) 1000000000000000000000) 32 cSeedThree) = true := by
  decide +kernel

end GMCExplicitDelta.Certificates.Group4
