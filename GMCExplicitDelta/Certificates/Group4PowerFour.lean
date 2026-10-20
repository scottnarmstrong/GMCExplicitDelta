module

public import GMCExplicitDelta.Certificates.Group4BandFour
public import GMCExplicitDelta.Certificates.Group4Check

/-!
# Group 4, row four: the matrix power and the fresh/seed moment bounds (kernel certificate)

`rhoFour` is the rounded-up profile `ρ_r ≥ (F_next^{32-r} (F + 10^{-30})^{32(r-1)})^{1/31}`
at scale `10^24` (so `μ_r ≤ ρ_r`); `cFreshFour` bounds `∑_r (𝐐^h)_{32,r} ρ_r`, and `cSeedFour` bounds
`∑_r (𝐐^h)_{32,r} (X/S)^r` with `X = 1000000000000000000000`.
-/

@[expose] public section

open GMCNumerics

namespace GMCExplicitDelta.Certificates.Group4

/-- The profile bounds, scale `10^24`. -/
def rhoFour : List ℕ := [1000000000000000000000000, 138015784565805309734514, 23540468117670281369415, 4015146824998361108857, 684837869226276855820, 116808407654327439646, 19923261711789726064, 3398183103489648961, 579606320084082544, 98859736526977070, 16861871873249304, 2876021452801357, 490544552772699, 83669041488053, 14270892345988, 2434094675028, 415167933677, 70812534501, 12078040320, 2060073955, 351373616, 59931547, 10222140, 1743525, 297382, 50723, 8652, 1476, 252, 43, 8, 2, 1]

theorem rho_check_four : rhoOK (10 ^ 24) 7797891827968 56500000000000 169438720000000000000000000001 1000000000000000000000000000000 rhoFour = true := by
  decide +kernel

/-- Bound for the fresh moment, scale `10^24`. -/
def cFreshFour : ℕ := 896923394113724102334219969429589

/-- Bound for the seed sum, scale `10^24`. -/
def cSeedFour : ℕ := 4672512121507325310292507

set_option maxRecDepth 100000 in
theorem power_check_four :
    (checkVec (10 ^ 24) 33 10 bandFour 537 rhoFour 32 cFreshFour &&
      checkVec (10 ^ 24) 33 10 bandFour 537 (powList (10 ^ 24) 1000000000000000000000) 32 cSeedFour) = true := by
  decide +kernel

end GMCExplicitDelta.Certificates.Group4
