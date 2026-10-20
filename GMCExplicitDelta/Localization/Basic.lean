module

public import GMCExplicitDelta.Localization.Defs

/-!
# Localization lane: elementary facts

Finite averages over triadic descendants (`descendantsAverage`) and positivity facts about the row
constants (`c_ν, R, ε > 0`, `b_k, y_k, T_g ≥ 0`, and `(1+ε)RT_g/c_ν ≤ τ_abs` from H12).
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta.Localization

open Assembly Contract

variable {d : ℕ}

/-! ### Finite averages over descendants -/

theorem descendantsAverage_eq (Q : Homogenization.TriadicCube d) (k : ℕ)
    (F : Homogenization.TriadicCube d → ℝ) :
    descendantsAverage Q k F =
      ((descendantsAtDepth Q k).card : ℝ)⁻¹ * ∑ R ∈ descendantsAtDepth Q k, F R := rfl

theorem card_descendantsAtDepth_pos (Q : Homogenization.TriadicCube d) (k : ℕ) :
    (0 : ℝ) < ((descendantsAtDepth Q k).card : ℝ) := by
  exact_mod_cast (descendantsAtDepth_nonempty Q k).card_pos

theorem descendantsAverage_const' (Q : Homogenization.TriadicCube d) (k : ℕ) (c : ℝ) :
    descendantsAverage Q k (fun _ => c) = c := by
  have h := card_descendantsAtDepth_pos Q k
  rw [descendantsAverage_eq, Finset.sum_const, nsmul_eq_mul]
  field_simp

theorem descendantsAverage_congr' (Q : Homogenization.TriadicCube d) (k : ℕ)
    {F G : Homogenization.TriadicCube d → ℝ} (h : ∀ R ∈ descendantsAtDepth Q k, F R = G R) :
    descendantsAverage Q k F = descendantsAverage Q k G := by
  rw [descendantsAverage_eq, descendantsAverage_eq, Finset.sum_congr rfl h]

theorem descendantsAverage_mul_const (Q : Homogenization.TriadicCube d) (k : ℕ)
    (w : Homogenization.TriadicCube d → ℝ) (c : ℝ) :
    descendantsAverage Q k (fun R => w R * c) = descendantsAverage Q k w * c := by
  rw [show (fun R => w R * c) = fun R => c * w R from funext fun R => mul_comm _ _,
    descendantsAverage_mul_left, mul_comm]

/-! ### Elementary facts about the row constants -/

theorem cNu_pos (row : Row d) (hO : row.Obligations) : 0 < row.cNu :=
  pow_pos hO.geo1.1 d

theorem R_pos (row : Row d) (hO : row.Obligations) : (0 : ℝ) < (row.R : ℝ) := by
  have h := hO.par2.1
  have : (1 : ℝ) < (row.R : ℝ) := by exact_mod_cast h
  linarith

theorem epsilon_pos (row : Row d) (hO : row.Obligations) : (0 : ℝ) < (row.epsilon : ℝ) := by
  exact_mod_cast hO.par2.2.1

theorem haarB_nonneg' (row : Row d) (k : ℕ) : 0 ≤ row.haarB k := by
  unfold Row.haarB
  split_ifs <;> exact Real.sqrt_nonneg _

theorem thetaR_nonneg (row : Row d) (hO : row.Obligations) : 0 ≤ row.thetaR := by
  have hR := R_pos row hO
  unfold Row.thetaR
  have : 2 ≤ (row.R : ℝ) + (row.R : ℝ)⁻¹ := by
    have h1 : 0 ≤ ((row.R : ℝ) - 1) ^ 2 / (row.R : ℝ) := by positivity
    have h2 : ((row.R : ℝ) - 1) ^ 2 / (row.R : ℝ) = (row.R : ℝ) + (row.R : ℝ)⁻¹ - 2 := by
      field_simp
      ring
    linarith
  linarith

theorem yk_nonneg (row : Row d) (hO : row.Obligations) (k : ℕ) : 0 ≤ row.yk k := by
  have hθ : 0 ≤ row.thetaR * row.qs ^ k :=
    mul_nonneg (thetaR_nonneg row hO) (pow_nonneg (Real.rpow_nonneg (by norm_num) _) _)
  unfold Row.yk ellipX
  positivity

theorem Tg_nonneg (row : Row d) : 0 ≤ row.Tg := by
  unfold Row.Tg
  refine tsum_nonneg fun k => mul_nonneg (haarB_nonneg' row _) (pow_nonneg ?_ _)
  exact Real.rpow_nonneg (by norm_num) _

theorem tau_bound (row : Row d) (hO : row.Obligations)
    (hTg : row.Tg ≤ row.Ks * row.rhoS ^ (row.g + 1) / (1 - row.rhoS)) :
    (1 + (row.epsilon : ℝ)) * (row.R : ℝ) * row.Tg / row.cNu ≤ row.tauAbs := by
  have hc := cNu_pos row hO
  have hR := R_pos row hO
  have he := epsilon_pos row hO
  have h1 : (1 + (row.epsilon : ℝ)) * (row.R : ℝ) * row.Tg ≤
      (1 + (row.epsilon : ℝ)) * (row.R : ℝ) * (row.Ks * row.rhoS ^ (row.g + 1) / (1 - row.rhoS)) :=
    mul_le_mul_of_nonneg_left hTg (by positivity)
  calc (1 + (row.epsilon : ℝ)) * (row.R : ℝ) * row.Tg / row.cNu ≤
      (1 + (row.epsilon : ℝ)) * (row.R : ℝ) * (row.Ks * row.rhoS ^ (row.g + 1) / (1 - row.rhoS)) /
        row.cNu := div_le_div_of_nonneg_right h1 hc.le
    _ = row.tauAbs := by
      unfold Row.tauAbs
      rw [← div_div]
      ring

end GMCExplicitDelta.Localization
