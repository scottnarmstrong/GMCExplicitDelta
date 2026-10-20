module

public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Coefficient bounds for the band majorant (step S9) -/

@[expose] public section

namespace GMCExplicitDelta.Source

open PowerSeries

/-- The S9 majorant, expressed in the variable `q²`. -/
noncomputable def bandEvenMajorant (a u s c₂ c₃ : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk fun n => if n = 0 then 1 else if n = 1 then u * s / 2 else
    if n = 2 then c₂ / 2 * (a * s / 2) ^ 2 else c₃ * (a * s / 2) ^ n / n.factorial

/-- The S9 majorant in the original variable `q`, with vanishing odd coefficients. -/
noncomputable def bandMajorant (a u s c₂ c₃ : ℝ) : PowerSeries ℝ :=
  PowerSeries.expand 2 (by decide) (bandEvenMajorant a u s c₂ c₃)

/-- Nonnegative coefficients are preserved by multiplication. -/
theorem coeff_mul_nonneg {f g : PowerSeries ℝ}
    (hf : ∀ n, 0 ≤ coeff n f) (hg : ∀ n, 0 ≤ coeff n g) (n : ℕ) :
    0 ≤ coeff n (f * g) := by
  rw [coeff_mul]
  exact Finset.sum_nonneg fun p _ => mul_nonneg (hf p.1) (hg p.2)

/-- Nonnegative coefficients are preserved by natural powers. -/
theorem coeff_pow_nonneg {f : PowerSeries ℝ} (hf : ∀ n, 0 ≤ coeff n f) (h n : ℕ) :
    0 ≤ coeff n (f ^ h) := by
  induction h generalizing n with
  | zero => simp only [pow_zero, coeff_one]; split_ifs <;> norm_num
  | succ h ih =>
    rw [pow_succ]
    exact coeff_mul_nonneg (fun n => ih n) hf n

/-- Coefficientwise multiplication is monotone for nonnegative series. -/
theorem coeff_mul_le {f g F G : PowerSeries ℝ}
    (hf : ∀ n, 0 ≤ coeff n f) (hG : ∀ n, 0 ≤ coeff n G)
    (hfF : ∀ n, coeff n f ≤ coeff n F) (hgG : ∀ n, coeff n g ≤ coeff n G) (n : ℕ) :
    coeff n (f * g) ≤ coeff n (F * G) := by
  rw [coeff_mul, coeff_mul]
  exact Finset.sum_le_sum fun p _ =>
    (mul_le_mul_of_nonneg_left (hgG p.2) (hf p.1)).trans
      (mul_le_mul_of_nonneg_right (hfF p.1) (hG p.2))

/-- Coefficientwise powers are monotone for nonnegative series. -/
theorem coeff_pow_le {f F : PowerSeries ℝ} (hf : ∀ n, 0 ≤ coeff n f)
    (hF : ∀ n, 0 ≤ coeff n F) (hle : ∀ n, coeff n f ≤ coeff n F) (h n : ℕ) :
    coeff n (f ^ h) ≤ coeff n (F ^ h) := by
  induction h generalizing n with
  | zero => simp only [pow_zero, le_refl]
  | succ h ih =>
    rw [pow_succ, pow_succ]
    exact coeff_mul_le (coeff_pow_nonneg hf h) hF ih hle n

/-- The majorant has nonnegative coefficients when its scalar inputs are nonnegative. -/
theorem bandEvenMajorant_coeff_nonneg {a u s c₂ c₃ : ℝ} (ha : 0 ≤ a) (hu : 0 ≤ u)
    (hs : 0 ≤ s) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃) (n : ℕ) :
    0 ≤ coeff n (bandEvenMajorant a u s c₂ c₃) := by
  rw [bandEvenMajorant, coeff_mk]
  split_ifs <;> positivity

/-- Each even coefficient is dominated by its Gaussian counterpart. -/
theorem bandEvenMajorant_coeff_le {a u s c₂ c₃ : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s)
    (hua : u ≤ a) (hc₂ : c₂ ≤ 1) (hc₃ : c₃ ≤ 1) (n : ℕ) :
    coeff n (bandEvenMajorant a u s c₂ c₃) ≤ (a * s / 2) ^ n / n.factorial := by
  rw [bandEvenMajorant, coeff_mk]
  split_ifs with hn0 hn1 hn2
  · subst n; norm_num
  · subst n
    norm_num
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hua hs) (by norm_num)
  · subst n
    norm_num
    have h := mul_le_mul_of_nonneg_right hc₂ (sq_nonneg (a * s / 2))
    calc
      _ = c₂ * (a * s / 2) ^ 2 / 2 := by ring
      _ ≤ 1 * (a * s / 2) ^ 2 / 2 :=
        div_le_div_of_nonneg_right h (show (0 : ℝ) ≤ 2 by norm_num)
      _ = _ := by rw [one_mul]
  · calc
      _ ≤ 1 * (a * s / 2) ^ n / n.factorial :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc₃ (by positivity)) (by positivity)
      _ = _ := by rw [one_mul]

/-- Coefficients of a rescaled exponential, in real arithmetic. -/
theorem coeff_rescaled_exp (t : ℝ) (n : ℕ) :
    coeff n (rescale t (PowerSeries.exp ℝ)) = t ^ n / n.factorial := by
  simp only [coeff_rescale, coeff_exp, map_div₀, map_one, map_natCast, mul_one_div]

/-- The Gaussian comparator is stable under powers. -/
theorem rescaled_exp_pow (t : ℝ) (h : ℕ) :
    (rescale t (PowerSeries.exp ℝ)) ^ h = rescale ((h : ℝ) * t) (PowerSeries.exp ℝ) := by
  rw [← map_pow, PowerSeries.exp_pow_eq_rescale_exp, rescale_rescale]

/-- S9: the coefficientwise Gaussian bound for every finite band count. -/
theorem bandEvenMajorant_pow_coeff_le {a u s c₂ c₃ : ℝ} (ha : 0 ≤ a) (hu : 0 ≤ u)
    (hs : 0 ≤ s) (hua : u ≤ a) (hc₂0 : 0 ≤ c₂) (hc₂1 : c₂ ≤ 1)
    (hc₃0 : 0 ≤ c₃) (hc₃1 : c₃ ≤ 1) (h n : ℕ) :
    0 ≤ coeff n (bandEvenMajorant a u s c₂ c₃ ^ h) ∧
      coeff n (bandEvenMajorant a u s c₂ c₃ ^ h) ≤ ((h : ℝ) * a * s / 2) ^ n / n.factorial := by
  have hnonneg := bandEvenMajorant_coeff_nonneg ha hu hs hc₂0 hc₃0
  refine ⟨coeff_pow_nonneg hnonneg h n, ?_⟩
  have hle := coeff_pow_le (F := rescale (a * s / 2) (PowerSeries.exp ℝ)) hnonneg
    (fun n => by rw [coeff_rescaled_exp]; positivity)
    (fun n => by rw [coeff_rescaled_exp]; exact bandEvenMajorant_coeff_le ha hs hua hc₂1 hc₃1 n) h n
  rw [rescaled_exp_pow, coeff_rescaled_exp] at hle
  have heq : (h : ℝ) * a * s / 2 = (h : ℝ) * (a * s / 2) := by ring
  simpa only [heq] using hle

/-- The original majorant has exactly the prescribed even coefficients. -/
theorem bandMajorant_pow_even_coeff (a u s c₂ c₃ : ℝ) (h n : ℕ) :
    coeff (2 * n) (bandMajorant a u s c₂ c₃ ^ h) =
      coeff n (bandEvenMajorant a u s c₂ c₃ ^ h) := by
  rw [bandMajorant, ← map_pow, coeff_expand_mul]

/-- Every odd coefficient vanishes, including after taking powers. -/
theorem bandMajorant_pow_odd_coeff (a u s c₂ c₃ : ℝ) (h n : ℕ) :
    coeff (2 * n + 1) (bandMajorant a u s c₂ c₃ ^ h) = 0 := by
  rw [bandMajorant, ← map_pow]
  exact coeff_expand_of_not_dvd _ _ _ (by omega)

/-- S9: the stated coefficientwise upper bound in the original variable `q`. -/
theorem bandMajorant_pow_even_coeff_le {a u s c₂ c₃ : ℝ} (ha : 0 ≤ a) (hu : 0 ≤ u)
    (hs : 0 ≤ s) (hua : u ≤ a) (hc₂0 : 0 ≤ c₂) (hc₂1 : c₂ ≤ 1)
    (hc₃0 : 0 ≤ c₃) (hc₃1 : c₃ ≤ 1) (h n : ℕ) :
    0 ≤ coeff (2 * n) (bandMajorant a u s c₂ c₃ ^ h) ∧
      coeff (2 * n) (bandMajorant a u s c₂ c₃ ^ h) ≤
        ((h : ℝ) * a * s / 2) ^ n / n.factorial := by
  rw [bandMajorant_pow_even_coeff]
  exact bandEvenMajorant_pow_coeff_le ha hu hs hua hc₂0 hc₂1 hc₃0 hc₃1 h n

/-- S9: every coefficient of the powered majorant is nonnegative. -/
theorem bandMajorant_pow_coeff_nonneg {a u s c₂ c₃ : ℝ} (ha : 0 ≤ a) (hu : 0 ≤ u)
    (hs : 0 ≤ s) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃) (h n : ℕ) :
    0 ≤ coeff n (bandMajorant a u s c₂ c₃ ^ h) := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hn : n = 2 * k := by omega
    rw [hn]
    rw [bandMajorant_pow_even_coeff]
    exact coeff_pow_nonneg (bandEvenMajorant_coeff_nonneg ha hu hs hc₂ hc₃) h k
  · have hn : n = 2 * k + 1 := by omega
    rw [hn]
    rw [bandMajorant_pow_odd_coeff]

end GMCExplicitDelta.Source
