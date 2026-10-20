module

public import GMCExplicitDelta.Proofs.GridMax.Orlicz
public import GMCExplicitDelta.Proofs.FineSensitivity.Holder
public import GMCExplicitDelta.Contract.DerivedHistory

/-! # Paper moment norms for the grid and the Orlicz remainder -/

@[expose] public section

open MeasureTheory ProbabilityTheory Real SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

namespace GMCExplicitDelta.Assembly.GridMax

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Completing the square also proves integrability of every linear exponential. -/
theorem integrable_exp_of_orlicz {Z : Ω → ℝ} {B : ℝ} (hB : B ≠ 0)
    (hZ : AEStronglyMeasurable Z μ)
    (hi : Integrable (fun ω => exp (Z ω ^ 2 / B ^ 2)) μ) (t : ℝ) :
    Integrable (fun ω => exp (t * Z ω)) μ := by
  refine (hi.const_mul (exp (t ^ 2 * B ^ 2 / 4))).mono'
    (continuous_exp.comp_aestronglyMeasurable (hZ.const_mul t))
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), ← exp_add]
  exact exp_le_exp.2 (by simpa only [add_comm] using mul_le_sq_div_add hB t (Z ω))

/-- The source moment factor at p=32 is precisely the contract's P32. -/
theorem momentFactor32 : Source.subgaussianMomentFactor 32 = Contract.P32 := by
  have hgamma : Gamma (65 : ℝ) = (Nat.factorial 64 : ℝ) := by
    simpa only [Nat.cast_ofNat, show (64 : ℝ) + 1 = 65 by norm_num] using Gamma_nat_eq_factorial 64
  norm_num only [Source.subgaussianMomentFactor, Contract.P32, Nat.cast_mul, Nat.cast_ofNat,
    show 2 * (32 : ℕ) + 1 = 65 by decide, show (2 : ℝ) * 32 = 64 by norm_num]
  rw [hgamma]
  norm_num

/-- The exact L128 Orlicz moment bound in the paper norm convention. -/
theorem lnorm128_of_orlicz {Z : Ω → ℝ} {B : ℝ} (hB : 0 < B)
    (hZ : AEStronglyMeasurable Z μ)
    (hi : Integrable (fun ω => exp (Z ω ^ 2 / B ^ 2)) μ)
    (hb : ∫ ω, exp (Z ω ^ 2 / B ^ 2) ∂μ ≤ 2) :
    paperENNRealLpNorm μ 128 (fun ω => ENNReal.ofReal |Z ω|) ≤
      ENNReal.ofReal (B * sqrt Contract.P32) := by
  have hpow : Integrable (fun ω => |Z ω| ^ (128 : ℕ)) μ :=
    integrable_pow_abs_of_integrable_exp_mul (by norm_num : (1 : ℝ) ≠ 0)
      (integrable_exp_of_orlicz hB.ne' hZ hi 1) (integrable_exp_of_orlicz hB.ne' hZ hi (-1)) 128
  have hm := integral_abs_pow_le_of_orlicz hB.ne' 64 hi hb (by simpa using hpow)
  have hgamma : Gamma (65 : ℝ) = (Nat.factorial 64 : ℝ) := by
    simpa only [Nat.cast_ofNat, show (64 : ℝ) + 1 = 65 by norm_num] using Gamma_nat_eq_factorial 64
  norm_num only [Nat.cast_ofNat, show (2 : ℕ) * 64 = 128 by decide,
    show (64 : ℝ) + 1 = 65 by norm_num] at hm
  rw [hgamma] at hm
  have hroot := Source.moment_root_le
    (integral_nonneg fun ω => pow_nonneg (abs_nonneg _) 128) hB.le
    (by positivity : (0 : ℝ) ≤ 2 * (Nat.factorial 64 : ℝ)) (by decide : (128 : ℕ) ≠ 0)
    (hm.trans_eq (by ring))
  rw [fine_lnorm_ofReal_eq μ (by norm_num) (fun _ => abs_nonneg _)
    (by simpa only [Real.rpow_ofNat] using hpow)]
  apply ENNReal.ofReal_le_ofReal
  have hfactor : sqrt Contract.P32 = (2 * (Nat.factorial 64 : ℝ)) ^ (1 / 128 : ℝ) := by
    rw [Contract.P32, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2 * (Nat.factorial 64 : ℝ))]
    congr 1
    norm_num
  rw [hfactor]
  simpa only [Real.rpow_ofNat, Nat.cast_ofNat, one_div] using hroot

/-- An exponential's paper norm is bounded by the corresponding exponential moment. -/
theorem lnorm_exp_of_moment {Z : Ω → ℝ} {p E : ℝ} (hp : 0 < p)
    (hi : Integrable (fun ω => exp (p * Z ω)) μ)
    (hb : ∫ ω, exp (p * Z ω) ∂μ ≤ E) :
    paperENNRealLpNorm μ p (fun ω => ENNReal.ofReal (exp (Z ω))) ≤ ENNReal.ofReal (E ^ p⁻¹) := by
  have heq : (fun ω => exp (Z ω) ^ p) = (fun ω => exp (p * Z ω)) := by
    funext ω
    rw [← exp_mul, mul_comm]
  rw [fine_lnorm_ofReal_eq μ hp (fun ω => (exp_pos _).le) (by rw [heq]; exact hi), heq]
  exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (integral_nonneg fun ω => (exp_pos _).le)
    hb (inv_nonneg.2 hp.le))

/-- Finite maxima acquire exactly card^(1/p) in the moment norm. -/
theorem lnorm_max_le {ι : Type*} [Fintype ι] [Nonempty ι] (Z : ι → Ω → ℝ)
    (hZ : ∀ i, Measurable (Z i)) {p B : ℝ} (hp : 0 < p)
    (hb : ∀ i, paperENNRealLpNorm μ p (fun ω => ENNReal.ofReal |Z i ω|) ≤ ENNReal.ofReal B) :
    paperENNRealLpNorm μ p (fun ω => ENNReal.ofReal
      (Finset.univ.sup' Finset.univ_nonempty (fun i => |Z i ω|))) ≤
      ENNReal.ofReal ((Fintype.card ι : ℝ) ^ (1 / p) * B) := by
  classical
  have heq : (fun ω => ENNReal.ofReal (Finset.univ.sup' Finset.univ_nonempty (fun i => |Z i ω|))) =
      fun ω => Finset.univ.sup (fun i => ENNReal.ofReal |Z i ω|) := by
    funext ω
    apply le_antisymm
    · obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => |Z i ω|)
      rw [he]
      exact Finset.le_sup (f := fun i => ENNReal.ofReal |Z i ω|) hi
    · apply Finset.sup_le
      intro i hi
      exact ENNReal.ofReal_le_ofReal (Finset.le_sup' (fun i => |Z i ω|) hi)
  rw [heq]
  refine (HistoryLane.lnorm_finset_sup_le hp Finset.univ _
    (fun i _ => (hZ i).norm.ennreal_ofReal.aemeasurable) (fun i _ => hb i)).trans_eq ?_
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg (Nat.cast_nonneg _) _),
    ← ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg _) (div_nonneg zero_le_one hp.le)]
  simp

end GMCExplicitDelta.Assembly.GridMax
