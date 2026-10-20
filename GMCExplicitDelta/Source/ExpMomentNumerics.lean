module

public import GMCExplicitDelta.Numerics.Enclosures
public import GMCExplicitDelta.Contract.Row

/-! # The numerical first-exponential-moment constant (step S7) -/

@[expose] public section

namespace GMCExplicitDelta.Source

open Real

/-- The true one-point variance constant used in S7. -/
noncomputable def sourceVarianceTrue : ℝ := log 2 / (35 + (13 + 2 * sqrt 2) * π ^ 2)

/-- The endpoint-strip all-even-moment proxy. -/
noncomputable def sourceProxyTrue : ℝ := (3 - 2 * sqrt 2) / 16

/-- Rational upper bound on the true variance constant. -/
theorem sourceVarianceTrue_le : sourceVarianceTrue ≤ 0.003624861638 := by
  obtain ⟨hpi, _⟩ := GMCNumerics.pi_enclosure
  obtain ⟨hs, _⟩ := GMCNumerics.sqrt_two_enclosure
  obtain ⟨_, hl⟩ := GMCNumerics.log_two_enclosure
  have hd : 0 < 35 + (13 + 2 * sqrt 2) * π ^ 2 := by positivity
  rw [sourceVarianceTrue, div_le_iff₀ hd]
  have hpi2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3.14159265358979323846) hpi.le 2
  have hprod := mul_le_mul (by linarith only [hs] : (13 + 2 * 1.41421356237309 : ℝ) ≤ 13 + 2 * sqrt 2)
    hpi2 (by norm_num) (by positivity)
  linarith only [hprod, hl]

/-- The endpoint proxy divided by eight, enclosed tightly enough for O.src.3. -/
theorem sourceProxyTrue_div_eight_enclosure :
    (0.0013404130879203125 : ℝ) ≤ sourceProxyTrue / 8 ∧
      sourceProxyTrue / 8 ≤ 0.00134041308792046875 := by
  obtain ⟨hlo, hhi⟩ := GMCNumerics.sqrt_two_enclosure
  unfold sourceProxyTrue
  constructor <;> linarith only [hlo, hhi]

/-- A rational exponential enclosure at the upper endpoint of the proxy interval. -/
theorem exp_proxy_endpoint_le :
    exp (0.00134041308792046875 : ℝ) ≤ 1.001341311843067 := by
  apply GMCNumerics.exp_le_of_poly (n := 8) (by norm_num) (by norm_num)
  norm_num [GMCNumerics.expPoly, GMCNumerics.expErr, Finset.sum_range_succ, Nat.factorial]

/-- The sharp variance and all-even proxy imply the frozen first-MGF constant. -/
theorem source_exp_constant_le_kappa :
    sourceVarianceTrue / 2 + 4 * (exp (sourceProxyTrue / 8) - 1 - sourceProxyTrue / 8) ≤
      (GMCExplicitDelta.Contract.kappaQ1 : ℝ) := by
  have hv := sourceVarianceTrue_le
  obtain ⟨hqlo, hqhi⟩ := sourceProxyTrue_div_eight_enclosure
  have he := (exp_le_exp.mpr hqhi).trans exp_proxy_endpoint_le
  norm_num [GMCExplicitDelta.Contract.kappaQ1]
  linarith only [hv, hqlo, he]

end GMCExplicitDelta.Source
