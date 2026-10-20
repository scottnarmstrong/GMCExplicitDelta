module

public import GMCExplicitDelta.Proofs.FreshMean.Cutoff
public import GMCExplicitDelta.Proofs.FreshMean.Arithmetic

/-! # Fresh mean return, with only the C8 identity left as an input -/

@[expose] public section

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta.Assembly

open Contract

variable {d : ℕ}

/-- I8 from the exact conclusion of the C8 target
`Assembly.lintegral_frozenJ_eq_fMean`. All fresh-band and normalization estimates are proved. -/
theorem freshMean_return_of_lintegral_frozenJ_eq_fMean
    (hmean : ∀ (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
      (z e : Homogenization.Vec d), vecNormSq e = 1 →
        ∫⁻ ω, ENNReal.ofReal (frozenJ M L (cubeAt z n) e e ω) ∂M.P.toMeasure =
          ENNReal.ofReal (fMean M L n))
    (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (M : SubdiffusiveProcess.Model.GMCModel d) {F : ℝ} (_hF : 0 ≤ F) (L : ℕ)
    (hf : fMean M L (L + row.h) ≤ row.Fnext F) :
    ∀ z e : Homogenization.Vec d, vecNormSq e = 1 →
      ∫⁻ ω, ENNReal.ofReal (frozenJ M (L + row.h) (cubeAt z (L + row.h)) e e ω) ∂M.P.toMeasure ≤
        ENNReal.ofReal (row.meanpost M.delta F) := by
  have htau := (StatementProofs.source_exp_moment (M := M) (x := 0)).2.2.2.2
  have hcast : ((L + row.h : ℕ) : ℝ) - L = (row.h : ℝ) := by push_cast; ring
  have ht : (((L + row.h : ℕ) : ℝ) - L) * SubdiffusiveProcess.Model.tauSq M.P ≤
      row.gammaH M.delta := by
    rw [hcast]
    calc
      _ ≤ (row.h : ℝ) * (1816027 / 1000000000 * M.delta ^ 2) :=
        mul_le_mul_of_nonneg_left htau (Nat.cast_nonneg _)
      _ = _ := by unfold Row.gammaH kappaQ1; push_cast; ring
  have hc : |normShift M (L + row.h) - normShift M L| ≤ row.gammaH M.delta :=
    (normShift_increment_le_tau M L (L + row.h) (Nat.le_add_right L row.h)).trans ht
  have hαβ := freshRet_alpha_beta_ge_one M L (L + row.h)
  have htrial := freshRet_fMean_fresh_le M L (L + row.h) (L + row.h)
    (Nat.le_add_right L row.h) ht
  have hcap : fMean M (L + row.h) (L + row.h) ≤ row.meanpost M.delta F := by
    change (alphaMean M L (L + row.h) + betaMean M L (L + row.h)) / 2 - 1 ≤ row.Fnext F at hf
    by_cases hd2 : d = 2
    · subst d
      have hz : normShift M (L + row.h) - normShift M L = 0 := by
        rw [normShift_planar_eq_zero, normShift_planar_eq_zero, sub_self]
      rw [hz] at htrial
      refine htrial.trans ?_
      change _ ≤ Real.exp (row.gammaH M.delta) * (1 + row.Fnext F) - 1
      exact freshRet_fresh_pair_zero_le hf
    · refine htrial.trans ?_
      rw [Row.meanpost, ite_eq_right hd2]
      exact freshRet_fresh_pair_le hαβ.1 hαβ.2 hc hf
  intro z e he
  rw [hmean M (L + row.h) (L + row.h) z e he]
  exact ENNReal.ofReal_le_ofReal hcap

end GMCExplicitDelta.Assembly
