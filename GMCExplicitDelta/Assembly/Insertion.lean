module

public import GMCExplicitDelta.Steps.AssemblyFrozen
public import GMCExplicitDelta.Steps.AssemblyInsertion
public import GMCExplicitDelta.Assembly.Scaling

/-!
# Assembly: the fresh insertion step (step I9) and extension to larger cubes (R1)

`freshInsertion` (I9): with `m = L + h`, from `f_m(b_L) ≤ F_next`, `‖J^max(z+Q_m;b_L)‖_{32} ≤ D_next`
and `0 < F_next ≤ D_next`, the coefficient `b_m` satisfies `‖J^max_m(z+Q_m)‖_{32} ≤ post` and
`𝔼 J(z+Q_m, e, e; b_m) ≤ meanpost`. Proof: I6 bounds the unshifted coefficient
`b_Le^{Z_{L,m}} = a_m/freshNorm` by `sym`; N2 gives `ā_m = freshNorm · e^c` with
`c = H_m - H_L`, `|c| ≤ κ_h h δ²`; I7 transfers the bound to `b_m` with `Φ_{κ_h hδ²}` (which is the
identity for `d = 2`, where `κ_h = 0`, and `Φ_{γ_h}` for `d ≥ 3`); I8 is the mean return.

`inductionP_of_cubeBounds` (R1): cutoff-scale bounds for all translates give `𝖯(m; D, F)`, with the
measurability conjuncts.
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta.Assembly

open Contract

variable {d : ℕ}

/-- `ā_m = ā_L e^{-(m-L)τ²} · e^{H_m - H_L}` (N2). -/
theorem ahom_eq_freshNorm_mul_exp (M : SubdiffusiveProcess.Model.GMCModel d)
    (hpos : ∀ m, 0 < ahom M m) (L m : ℕ) :
    ahom M m = freshNorm M L m * Real.exp (normShift M m - normShift M L) := by
  unfold freshNorm normShift
  rw [mul_assoc, ← Real.exp_add]
  have e : -(((m : ℝ) - L) * SubdiffusiveProcess.Model.tauSq M.P) +
      (((m : ℝ) + 1) * SubdiffusiveProcess.Model.tauSq M.P + Real.log (ahom M m) -
        (((L : ℝ) + 1) * SubdiffusiveProcess.Model.tauSq M.P + Real.log (ahom M L))) =
      Real.log (ahom M m) - Real.log (ahom M L) := by ring
  rw [e, Real.exp_sub, Real.exp_log (hpos m), Real.exp_log (hpos L)]
  have hL : ahom M L ≠ 0 := (hpos L).ne'
  field_simp

/-- **I9 (application to the induction step).** -/
theorem freshInsertion (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (M : SubdiffusiveProcess.Model.GMCModel d) {D F : ℝ} (hF : 0 ≤ F) (L : ℕ)
    (hpos : 0 < row.Fnext F) (hle : row.Fnext F ≤ row.Dnext D F)
    (hf : fMean M L (L + row.h) ≤ row.Fnext F)
    (hnorm : ∀ z : Homogenization.Vec d,
      paperENNRealLpNorm M.P.toMeasure 32 (normalizedDefect M L (cubeAt z (L + row.h))) ≤
        ENNReal.ofReal (row.Dnext D F)) :
    ∀ z : Homogenization.Vec d,
      paperENNRealLpNorm M.P.toMeasure 32
          (normalizedDefect M (L + row.h) (cubeAt z (L + row.h))) ≤
        ENNReal.ofReal (row.post M.delta D F) ∧
      ∀ e : Homogenization.Vec d, vecNormSq e = 1 →
        ∫⁻ ω, ENNReal.ofReal (frozenJ M (L + row.h) (cubeAt z (L + row.h)) e e ω)
            ∂M.P.toMeasure ≤
          ENNReal.ofReal (row.meanpost M.delta F) := by
  intro z
  refine ⟨?_, freshMean_return row hd hO M hF L hf z⟩
  obtain ⟨hapos, hdrift, -⟩ := normShift_drift row hd hO M
  have h6 := freshNorm_return row hd hO M L hpos hle hf hnorm z
  have hc : |normShift M (L + row.h) - normShift M L| ≤
      kappaH d * (row.h : ℝ) * M.delta ^ 2 := by
    have h := hdrift L (L + row.h) (Nat.le_add_right _ _)
    have e : ((L + row.h : ℕ) : ℝ) - (L : ℝ) = (row.h : ℝ) := by push_cast; ring
    rwa [e] at h
  have hs : 0 < freshNorm M L (L + row.h) := by
    unfold freshNorm; exact mul_pos (hapos L) (Real.exp_pos _)
  have h7 := scaledDefect_shift_le M (L + row.h) (cubeAt z (L + row.h)) hs hc
    (sym_nonneg row _ _ _) h6
  rw [← ahom_eq_freshNorm_mul_exp M hapos L (L + row.h), ← normalizedDefect_eq_scaledDefect] at h7
  refine h7.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  unfold Row.post Row.gammaH kappaH
  split_ifs
  · rw [zero_mul, zero_mul, PhiMap_zero]
  · rfl

/-- **R1** with the measurability conjuncts: bounds at the cutoff scale for every translate give
`𝖯(m; D, F)`. -/
theorem inductionP_of_cubeBounds (M : SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) {D F : ℝ}
    (hD : ∀ z : Homogenization.Vec d,
      paperENNRealLpNorm M.P.toMeasure 32 (normalizedDefect M m (cubeAt z m)) ≤ ENNReal.ofReal D)
    (hF : ∀ z e : Homogenization.Vec d, vecNormSq e = 1 →
      ∫⁻ ω, ENNReal.ofReal (frozenJ M m (cubeAt z m) e e ω) ∂M.P.toMeasure ≤ ENNReal.ofReal F) :
    InductionP M m D F := by
  intro n hmn z
  obtain ⟨hn, he⟩ := inductionBounds_extend M m hD hF n hmn z
  obtain ⟨hmeas1, hmeas2⟩ := measurable_cascadeObservables M m (cubeAt z n)
  exact ⟨hmeas1 (ahom M m), hn, fun e hev =>
    ⟨hmeas2 ((Real.sqrt (ahom M m))⁻¹ • e) (Real.sqrt (ahom M m) • e), he e hev⟩⟩

end GMCExplicitDelta.Assembly
