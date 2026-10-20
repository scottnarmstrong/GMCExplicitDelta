module

public import GMCExplicitDelta.Steps.LocalizationModel
public import GMCExplicitDelta.Steps.LocalizationCore
public import GMCExplicitDelta.Steps.AssemblyFrozen
public import GMCExplicitDelta.Localization.ProbLemmas
public import GMCExplicitDelta.Localization.Basic

/-!
# L4: the localized first-moment inequality on the model

L4. From the pointwise localized inequality `loc_pointwise` (deterministic, on the good
event), the model facts of `Targets/LocalizationModel.lean` (C2, C4, C8, integrability) and the
bad-event bound on the depth-`ν` cells, we take expectations:

* `loc_expectation`: `c^ex 𝔼J(Q_{n-ν}) ≤ (1+ε)/2 · √(2R j⋆) ∑_{k≤K} b_k(√(2y_kΔ_k) + √Var_k)
  + (1+ε)/2 · 2RT_g j⋆ + (1+ε⁻¹)Δ_ν + c^ex·bad₀` with `c^ex ≥ c_ν` (Cauchy–Schwarz, Minkowski,
  stationarity);
* `loc_firstMoment` (L4): `(1-τ_abs) j⋆ ≤ A₀√j⋆ ∑_{k=1}^{K} b_k√(y_k/R)√Δ_k
  + A_{v0}√j⋆ ∑_{k=0}^{K} b_k√Var_k + B₀Δ_ν + bad₀`, `K = n - L`, `j⋆ = meanJ n`,
  `Δ_k = meanJ (n-k) - meanJ n`, `Var_k = varFactor d · |q|² · V_{n-k}`.
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open scoped ENNReal

namespace GMCExplicitDelta.Localization

open Assembly Contract

variable {d : ℕ}

section Integrals

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem integrable_descendantsAverage (Q : Homogenization.TriadicCube d) (k : ℕ)
    {F : Homogenization.TriadicCube d → Ω → ℝ}
    (hF : ∀ R ∈ descendantsAtDepth Q k, Integrable (F R) μ) :
    Integrable (fun ω => descendantsAverage Q k fun R => F R ω) μ := by
  simp only [descendantsAverage_eq]
  exact (integrable_finsetSum _ hF).const_mul _

theorem integral_descendantsAverage (Q : Homogenization.TriadicCube d) (k : ℕ)
    {F : Homogenization.TriadicCube d → Ω → ℝ}
    (hF : ∀ R ∈ descendantsAtDepth Q k, Integrable (F R) μ) :
    ∫ ω, (descendantsAverage Q k fun R => F R ω) ∂μ =
      descendantsAverage Q k fun R => ∫ ω, F R ω ∂μ := by
  simp only [descendantsAverage_eq]
  rw [integral_const_mul, integral_finsetSum _ hF]

end Integrals

/-! ### Measurability of the good event -/

theorem measurable_finset_sup_ennreal {ι Ω : Type*} [MeasurableSpace Ω] (s : Finset ι)
    {f : ι → Ω → ℝ≥0∞} (hf : ∀ i, Measurable (f i)) :
    Measurable fun ω => s.sup fun i => f i ω := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.sup_insert]
    exact Measurable.fun_sup (hf a) ih

theorem measurableSet_goodEvent (row : Row d) (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (z : Homogenization.Vec d) (n : ℕ) : MeasurableSet (goodEvent row M L z n) := by
  have hdef : ∀ R, Measurable (normalizedDefect M L (cellAt z R)) := fun R => by
    rw [normalizedDefect_eq_scaledDefect]
    exact (measurable_cascadeObservables M L (cellAt z R)).1 _
  have hdm : ∀ j, Measurable (depthMax M L z n j) := fun j =>
    measurable_finset_sup_ennreal _ fun R => hdef R
  have hh : Measurable (haarStat row M L z n) :=
    Measurable.ennreal_tsum fun j => (hdm j).const_mul _
  exact measurableSet_le hh measurable_const

/-! ### The expectation step -/

theorem scale_of_mem_depth {n k : ℕ} (hk : k ≤ n) {R : Homogenization.TriadicCube d}
    (hR : R ∈ descendantsAtDepth (originCube d (n : ℤ)) k) : R.scale = ((n - k : ℕ) : ℤ) := by
  rw [scale_eq_sub_of_mem_descendantsAtDepth hR]
  simp only [originCube]
  omega

/-- **Expectation of the pointwise localized inequality** (the probabilistic part of L4). -/
theorem loc_expectation (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (M : SubdiffusiveProcess.Model.GMCModel d) {D F : ℝ} (L : ℕ) (hP : InductionP M L D F)
    (n : ℕ) (hn : L + row.g ≤ n) (p q : Homogenization.Vec d)
    (hmean : -p + betaMean M L n • q = 0) {bad0 : ℝ} (hbad0 : 0 ≤ bad0)
    (hbad : ∀ R ∈ descendantsAtDepth (originCube d (n : ℤ)) row.nu,
      ∫⁻ ω in (goodEvent row M L 0 n)ᶜ, ENNReal.ofReal (frozenJ M L (cellAt 0 R) p q ω)
        ∂M.P.toMeasure ≤ ENNReal.ofReal bad0) :
    ∃ cex : ℝ, row.cNu ≤ cex ∧
      cex * meanJ M L (n - row.nu) p q ≤
        (1 + (row.epsilon : ℝ)) / 2 * (Real.sqrt (2 * (row.R : ℝ) * meanJ M L n p q) *
          ∑ k ∈ Finset.range (n - L + 1), row.haarB k *
            (Real.sqrt (2 * row.yk k * (meanJ M L (n - k) p q - meanJ M L n p q)) +
              Real.sqrt (varFactor d * vecNormSq q * varV M L (n - k)))) +
          ((1 + (row.epsilon : ℝ)) / 2 * (2 * (row.R : ℝ) * row.Tg * meanJ M L n p q) +
            (1 + (row.epsilon : ℝ)⁻¹) * (meanJ M L (n - row.nu) p q - meanJ M L n p q)) +
          cex * bad0 := by
  set μ := M.P.toMeasure with hμ
  set K := n - L with hK
  set Q := originCube d (n : ℤ) with hQ
  set G := goodEvent row M L 0 n with hG
  have hgK : row.g ≤ K := by omega
  have hνK : row.nu ≤ K := by have := hO.par2.2.2.1; omega
  have hLn : L ≤ n := by omega
  have hLk : ∀ k ≤ K, L ≤ n - k := fun k hk => by omega
  have hKn : ∀ k ≤ K, k ≤ n := fun k hk => by omega
  obtain ⟨w, hw, hcw, hpt⟩ := loc_pointwise row hd hO M L n K hgK
  set c : ℕ → Homogenization.Vec d := fun k => -p + betaMean M L (n - k) • q with hc
  have hc0 : c 0 = 0 := by simpa [hc] using hmean
  have hscale : ∀ k ≤ K, ∀ R ∈ descendantsAtDepth Q k, (L : ℤ) ≤ R.scale := fun k hk R hR => by
    rw [scale_of_mem_depth (hKn k hk) hR]
    exact_mod_cast hLk k hk
  -- integrability and means of the cell responses
  have hJint : ∀ k ≤ K, ∀ R ∈ descendantsAtDepth Q k,
      Integrable (frozenJ M L (cellAt 0 R) p q) μ := fun k hk R hR =>
    (integrable_cell M L hP R (hscale k hk R hR) p q 0).1
  have hJmean : ∀ k ≤ K, ∀ R ∈ descendantsAtDepth Q k,
      ∫ ω, frozenJ M L (cellAt 0 R) p q ω ∂μ = meanJ M L (n - k) p q := fun k hk R hR =>
    integral_frozenJ_cell M L hP (n - k) (hLk k hk) R (scale_of_mem_depth (hKn k hk) hR) p q
  have hJ0int : Integrable (frozenJ M L (cubeAt 0 n) p q) μ :=
    (integrable_cell M L hP (originCube d (n : ℤ)) (by simp only [originCube]; exact_mod_cast hLn)
      p q 0).1
  have hJ0mean : ∫ ω, frozenJ M L (cubeAt 0 n) p q ω ∂μ = meanJ M L n p q :=
    integral_frozenJ_cell M L hP n hLn (originCube d (n : ℤ)) rfl p q
  have hcJint : ∀ k ≤ K, Integrable (cellJ M L n k p q) μ := fun k hk =>
    integrable_descendantsAverage Q k (hJint k hk)
  have hcJmean : ∀ k ≤ K, ∫ ω, cellJ M L n k p q ω ∂μ = meanJ M L (n - k) p q := by
    intro k hk
    show ∫ ω, (descendantsAverage Q k fun R => frozenJ M L (cellAt 0 R) p q ω) ∂μ = _
    rw [integral_descendantsAverage Q k (hJint k hk),
      descendantsAverage_congr' Q k (hJmean k hk), descendantsAverage_const']
  have hResInt : ∀ k ≤ K, ∀ R ∈ descendantsAtDepth Q k, Integrable
      (fun ω => vecNormSq (-p + (frozenY M L (cellAt 0 R) ω).mulVec q - c k)) μ :=
    fun k hk R hR => (integrable_cell M L hP R (hscale k hk R hR) p q (c k)).2
  have hcRint : ∀ k ≤ K, Integrable (cellRes M L n k p q (c k)) μ := fun k hk =>
    integrable_descendantsAverage Q k (hResInt k hk)
  have hcRle : ∀ k ≤ K, ∫ ω, cellRes M L n k p q (c k) ω ∂μ ≤
      varFactor d * vecNormSq q * varV M L (n - k) := by
    intro k hk
    show ∫ ω, (descendantsAverage Q k fun R =>
      vecNormSq (-p + (frozenY M L (cellAt 0 R) ω).mulVec q - c k)) ∂μ ≤ _
    rw [integral_descendantsAverage Q k (hResInt k hk)]
    calc _ ≤ descendantsAverage Q k (fun _ => varFactor d * vecNormSq q * varV M L (n - k)) := by
          refine descendantsAverage_le_descendantsAverage Q k fun R hR => ?_
          have heq : (fun ω => vecNormSq (-p + (frozenY M L (cellAt 0 R) ω).mulVec q - c k)) =
              fun ω => vecNormSq ((frozenY M L (cellAt 0 R) ω).mulVec q - betaMean M L (n - k) • q) := by
            funext ω
            congr 1
            simp only [hc]
            abel
          rw [heq]
          exact integral_cellRes_le M L hP (n - k) (hLk k hk) R (scale_of_mem_depth (hKn k hk) hR) q
      _ = _ := descendantsAverage_const' _ _ _
  -- the localized energy and its bad part
  have hSterm : ∀ R ∈ descendantsAtDepth Q row.nu,
      Integrable (fun ω => w R * frozenJ M L (cellAt 0 R) p q ω) μ := fun R hR =>
    (hJint row.nu hνK R hR).const_mul (w R)
  have hSint : Integrable (cellJw M L n row.nu w p q) μ :=
    integrable_descendantsAverage Q row.nu hSterm
  have hSmean : ∫ ω, cellJw M L n row.nu w p q ω ∂μ =
      descendantsAverage Q row.nu w * meanJ M L (n - row.nu) p q := by
    show ∫ ω, (descendantsAverage Q row.nu fun R => w R * frozenJ M L (cellAt 0 R) p q ω) ∂μ = _
    rw [integral_descendantsAverage Q row.nu hSterm,
      descendantsAverage_congr' Q row.nu (G := fun R => w R * meanJ M L (n - row.nu) p q)
        (fun R hR => by rw [integral_const_mul, hJmean row.nu hνK R hR]),
      descendantsAverage_mul_const]
  have hbadR : ∀ R ∈ descendantsAtDepth Q row.nu,
      ∫ ω in Gᶜ, frozenJ M L (cellAt 0 R) p q ω ∂μ ≤ bad0 := by
    intro R hR
    rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun ω => frozenJ_nonneg M L _ p q ω)
      (hJint row.nu hνK R hR).aestronglyMeasurable.restrict]
    exact ENNReal.toReal_le_of_le_ofReal hbad0 (hbad R hR)
  have hSbad : ∫ ω in Gᶜ, cellJw M L n row.nu w p q ω ∂μ ≤
      descendantsAverage Q row.nu w * bad0 := by
    show ∫ ω in Gᶜ, (descendantsAverage Q row.nu fun R =>
      w R * frozenJ M L (cellAt 0 R) p q ω) ∂μ ≤ _
    rw [integral_descendantsAverage (μ := μ.restrict Gᶜ) Q row.nu
      (fun R hR => (hSterm R hR).restrict), ← descendantsAverage_mul_const]
    refine descendantsAverage_le_descendantsAverage Q row.nu fun R hR => ?_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hbadR R hR) (hw R).1
  -- the generic expectation step
  have hRpos := R_pos row hO
  have hεpos := epsilon_pos row hO
  have hJ0nn : ∀ ω, 0 ≤ frozenJ M L (cubeAt 0 n) p q ω := fun ω => frozenJ_nonneg M L _ p q ω
  have hdrop : ∀ k ω, 0 ≤ cellJ M L n k p q ω - frozenJ M L (cubeAt 0 n) p q ω := fun k ω =>
    sub_nonneg.mpr (frozenJ_le_cellJ M L n k p q ω)
  have hmemK : ∀ k ∈ Finset.range (K + 1), k ≤ K := fun k hk => by
    simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hk
  have key := integral_le_of_pointwise_bound (μ := μ) (measurableSet_goodEvent row M L 0 n)
    (S := cellJw M L n row.nu w p q)
    (A := fun ω => 2 * (row.R : ℝ) * frozenJ M L (cubeAt 0 n) p q ω)
    (Z := fun ω => (1 + (row.epsilon : ℝ)) / 2 *
        (2 * (row.R : ℝ) * row.Tg * frozenJ M L (cubeAt 0 n) p q ω) +
      (1 + (row.epsilon : ℝ)⁻¹) *
        (cellJ M L n row.nu p q ω - frozenJ M L (cubeAt 0 n) p q ω))
    (Dk := fun k ω => 2 * row.yk k * (cellJ M L n k p q ω - frozenJ M L (cubeAt 0 n) p q ω))
    (Gk := fun k ω => cellRes M L n k p q (c k) ω) (s := Finset.range (K + 1)) (b := row.haarB)
    (a := (1 + (row.epsilon : ℝ)) / 2) hSint (hJ0int.const_mul _)
    (((hJ0int.const_mul _).const_mul _).add (((hcJint row.nu hνK).sub hJ0int).const_mul _))
    (fun k hk => ((hcJint k (hmemK k hk)).sub hJ0int).const_mul _)
    (fun k hk => hcRint k (hmemK k hk))
    (fun ω => mul_nonneg (by positivity) (hJ0nn ω))
    (fun ω => add_nonneg
      (mul_nonneg (by positivity) (mul_nonneg (mul_nonneg (by positivity) (Tg_nonneg row))
        (hJ0nn ω)))
      (mul_nonneg (by positivity) (hdrop row.nu ω)))
    (fun k _ ω => mul_nonneg (mul_nonneg (by norm_num) (yk_nonneg row hO k)) (hdrop k ω))
    (fun k _ ω => descendantsAverage_nonneg _ _ _ fun R _ => vecNormSq_nonneg _)
    (fun k _ => haarB_nonneg' row k) (by positivity)
    (fun ω hω => by
      have h := hpt ω hω p q c hc0
      simp only [locBound, haarSum] at h
      refine h.trans (le_of_eq ?_)
      ring)
  -- evaluate the integrals
  rw [hSmean, integral_const_mul, hJ0mean] at key
  have hZint : ∫ ω, ((1 + (row.epsilon : ℝ)) / 2 *
        (2 * (row.R : ℝ) * row.Tg * frozenJ M L (cubeAt 0 n) p q ω) +
      (1 + (row.epsilon : ℝ)⁻¹) *
        (cellJ M L n row.nu p q ω - frozenJ M L (cubeAt 0 n) p q ω)) ∂μ =
      (1 + (row.epsilon : ℝ)) / 2 * (2 * (row.R : ℝ) * row.Tg * meanJ M L n p q) +
        (1 + (row.epsilon : ℝ)⁻¹) * (meanJ M L (n - row.nu) p q - meanJ M L n p q) := by
    rw [integral_add (f := fun ω => (1 + (row.epsilon : ℝ)) / 2 *
          (2 * (row.R : ℝ) * row.Tg * frozenJ M L (cubeAt 0 n) p q ω))
        (g := fun ω => (1 + (row.epsilon : ℝ)⁻¹) *
          (cellJ M L n row.nu p q ω - frozenJ M L (cubeAt 0 n) p q ω))
        ((hJ0int.const_mul _).const_mul _) (((hcJint row.nu hνK).sub hJ0int).const_mul _),
      integral_const_mul, integral_const_mul, integral_const_mul,
      integral_sub (hcJint row.nu hνK) hJ0int, hcJmean row.nu hνK, hJ0mean]
  rw [hZint] at key
  have hsum : ∑ k ∈ Finset.range (K + 1), row.haarB k *
      (Real.sqrt (∫ ω, 2 * row.yk k * (cellJ M L n k p q ω -
          frozenJ M L (cubeAt 0 n) p q ω) ∂μ) +
        Real.sqrt (∫ ω, cellRes M L n k p q (c k) ω ∂μ)) ≤
      ∑ k ∈ Finset.range (K + 1), row.haarB k *
        (Real.sqrt (2 * row.yk k * (meanJ M L (n - k) p q - meanJ M L n p q)) +
          Real.sqrt (varFactor d * vecNormSq q * varV M L (n - k))) := by
    refine Finset.sum_le_sum fun k hk => ?_
    have hk' := hmemK k hk
    rw [integral_const_mul, integral_sub (hcJint k hk') hJ0int, hcJmean k hk', hJ0mean]
    exact mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (Real.sqrt_le_sqrt (hcRle k hk'))) (haarB_nonneg' row k)
  refine ⟨descendantsAverage Q row.nu w, hcw, ?_⟩
  have hmono := mul_le_mul_of_nonneg_left hsum
    (mul_nonneg (by positivity : (0 : ℝ) ≤ (1 + (row.epsilon : ℝ)) / 2)
      (Real.sqrt_nonneg (2 * (row.R : ℝ) * meanJ M L n p q)))
  have hbadw := hSbad
  nlinarith [hmono, hbadw, key]

/-- `𝔼J(Q_n) ≥ 0` and `n ↦ 𝔼J(Q_n, p, q)` is nonincreasing on the window (C2, C4). -/
theorem meanJ_nonneg_mono (M : SubdiffusiveProcess.Model.GMCModel d) {D F : ℝ} (L : ℕ)
    (hP : InductionP M L D F) (n : ℕ) (hLn : L ≤ n) (p q : Homogenization.Vec d) :
    0 ≤ meanJ M L n p q ∧ ∀ k, k ≤ n - L → meanJ M L n p q ≤ meanJ M L (n - k) p q := by
  set μ := M.P.toMeasure with hμ
  set Q := originCube d (n : ℤ) with hQ
  have hJ0int : Integrable (frozenJ M L (cubeAt 0 n) p q) μ :=
    (integrable_cell M L hP (originCube d (n : ℤ)) (by simp only [originCube]; exact_mod_cast hLn)
      p q 0).1
  have hJ0mean : ∫ ω, frozenJ M L (cubeAt 0 n) p q ω ∂μ = meanJ M L n p q :=
    integral_frozenJ_cell M L hP n hLn (originCube d (n : ℤ)) rfl p q
  refine ⟨hJ0mean ▸ integral_nonneg fun ω => frozenJ_nonneg M L _ p q ω, fun k hk => ?_⟩
  have hkn : k ≤ n := by omega
  have hJint : ∀ R ∈ descendantsAtDepth Q k, Integrable (frozenJ M L (cellAt 0 R) p q) μ :=
    fun R hR => (integrable_cell M L hP R (by
      rw [scale_of_mem_depth hkn hR]; exact_mod_cast (show L ≤ n - k by omega)) p q 0).1
  have hcJ : ∫ ω, cellJ M L n k p q ω ∂μ = meanJ M L (n - k) p q := by
    show ∫ ω, (descendantsAverage Q k fun R => frozenJ M L (cellAt 0 R) p q ω) ∂μ = _
    rw [integral_descendantsAverage Q k hJint,
      descendantsAverage_congr' Q k (G := fun _ => meanJ M L (n - k) p q) (fun R hR =>
        integral_frozenJ_cell M L hP (n - k) (by omega) R (scale_of_mem_depth hkn hR) p q),
      descendantsAverage_const']
  rw [← hJ0mean, ← hcJ]
  exact integral_mono hJ0int (integrable_descendantsAverage Q k hJint)
    (fun ω => frozenJ_le_cellJ M L n k p q ω)

theorem sqrt_drop_coef {R y j Δ : ℝ} (hR : 0 < R) (hy : 0 ≤ y) (hj : 0 ≤ j) (hΔ : 0 ≤ Δ) :
    Real.sqrt (2 * R * j) * Real.sqrt (2 * y * Δ) =
      2 * R * (Real.sqrt j * (Real.sqrt (y / R) * Real.sqrt Δ)) := by
  rw [← Real.sqrt_mul (by positivity),
    ← Real.sqrt_sq (show 0 ≤ 2 * R * (Real.sqrt j * (Real.sqrt (y / R) * Real.sqrt Δ)) by
      positivity)]
  congr 1
  simp only [mul_pow, Real.sq_sqrt hj, Real.sq_sqrt (div_nonneg hy hR.le), Real.sq_sqrt hΔ]
  field_simp

/-- **L4 (localized first-moment inequality)** on the model, for a pair `(p, q)` with
`𝔼[-p + Y_{Q_n}q] = 0`, `L + g ≤ n`, and a bad-event bound `bad₀` on the depth-`ν` cells:
`(1-τ_abs) j⋆ ≤ A₀√j⋆ ∑_{k=1}^{n-L} b_k√(y_k/R)√Δ_k + A_{v0}√j⋆ ∑_{k=0}^{n-L} b_k√Var_k + B₀Δ_ν + bad₀`
with `j⋆ = meanJ n`, `Δ_k = meanJ (n-k) - meanJ n`, `Var_k = varFactor d · |q|² · V_{n-k}`.
The Haar tail hypothesis `hTg` is the last conjunct of H12 (`haarB_sums`). -/
theorem loc_firstMoment (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (M : SubdiffusiveProcess.Model.GMCModel d) {D F : ℝ} (L : ℕ) (hP : InductionP M L D F)
    (n : ℕ) (hn : L + row.g ≤ n)
    (hTg : row.Tg ≤ row.Ks * row.rhoS ^ (row.g + 1) / (1 - row.rhoS))
    (p q : Homogenization.Vec d) (hmean : -p + betaMean M L n • q = 0) {bad0 : ℝ}
    (hbad0 : 0 ≤ bad0)
    (hbad : ∀ R ∈ descendantsAtDepth (originCube d (n : ℤ)) row.nu,
      ∫⁻ ω in (goodEvent row M L 0 n)ᶜ, ENNReal.ofReal (frozenJ M L (cellAt 0 R) p q ω)
        ∂M.P.toMeasure ≤ ENNReal.ofReal bad0) :
    (1 - row.tauAbs) * meanJ M L n p q ≤
      coefA0 row * Real.sqrt (meanJ M L n p q) *
          ∑ k ∈ Finset.Icc 1 (n - L), row.haarB k * Real.sqrt (row.yk k / (row.R : ℝ)) *
            Real.sqrt (meanJ M L (n - k) p q - meanJ M L n p q) +
        coefAv0 row * Real.sqrt (meanJ M L n p q) *
          ∑ k ∈ Finset.range (n - L + 1), row.haarB k *
            Real.sqrt (varFactor d * vecNormSq q * varV M L (n - k)) +
        coefB0 row * (meanJ M L (n - row.nu) p q - meanJ M L n p q) + bad0 := by
  obtain ⟨cex, hcex, hE⟩ := loc_expectation row hd hO M L hP n hn p q hmean hbad0 hbad
  have hLn : L ≤ n := by omega
  have hνK : row.nu ≤ n - L := by have := hO.par2.2.2.1; omega
  obtain ⟨hj, hmono⟩ := meanJ_nonneg_mono M L hP n hLn p q
  have hc := cNu_pos row hO
  have hR := R_pos row hO
  have hε := epsilon_pos row hO
  have hcexpos : 0 < cex := lt_of_lt_of_le hc hcex
  set K := n - L with hK
  set j := meanJ M L n p q with hjdef
  set jν := meanJ M L (n - row.nu) p q with hjνdef
  set a : ℝ := (1 + (row.epsilon : ℝ)) / 2 with ha
  set b' : ℝ := 1 + (row.epsilon : ℝ)⁻¹ with hb'
  set E := ∑ k ∈ Finset.range (K + 1), row.haarB k *
    (Real.sqrt (2 * row.yk k * (meanJ M L (n - k) p q - j)) +
      Real.sqrt (varFactor d * vecNormSq q * varV M L (n - k))) with hEdef
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun k _ => mul_nonneg (haarB_nonneg' row k) (by positivity)
  have hΔν : 0 ≤ jν - j := sub_nonneg.mpr (hmono row.nu hνK)
  have hTg0 := Tg_nonneg row
  set N := a * (Real.sqrt (2 * (row.R : ℝ) * j) * E) +
    (a * (2 * (row.R : ℝ) * row.Tg * j) + b' * (jν - j)) with hNdef
  have hN : 0 ≤ N := by positivity
  -- divide by `c^ex ≥ c_ν`
  have h1 : jν ≤ N / cex + bad0 := by
    rw [div_add' _ _ _ hcexpos.ne', le_div_iff₀ hcexpos]
    linarith
  have h2 : N / cex ≤ N / row.cNu := div_le_div_of_nonneg_left hN hc hcex
  have h3 : a * (2 * (row.R : ℝ) * row.Tg * j) / row.cNu ≤ row.tauAbs * j := by
    have ht := tau_bound row hO hTg
    have e : a * (2 * (row.R : ℝ) * row.Tg * j) / row.cNu =
        (1 + (row.epsilon : ℝ)) * (row.R : ℝ) * row.Tg / row.cNu * j := by
      rw [ha]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right ht hj
  have hNsplit : N / row.cNu = a * Real.sqrt (2 * (row.R : ℝ) * j) * E / row.cNu +
      a * (2 * (row.R : ℝ) * row.Tg * j) / row.cNu + coefB0 row * (jν - j) := by
    rw [hNdef, coefB0, hb']
    ring
  have hY : (1 - row.tauAbs) * j ≤
      a * Real.sqrt (2 * (row.R : ℝ) * j) * E / row.cNu + coefB0 row * (jν - j) + bad0 := by
    have : j ≤ jν := sub_nonneg.mp hΔν
    nlinarith [h1, h2, h3, hNsplit]
  -- rewrite the Haar sum in the L4 form
  have hΔ : ∀ k ∈ Finset.range (K + 1), 0 ≤ meanJ M L (n - k) p q - j := fun k hk =>
    sub_nonneg.mpr (hmono k (by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hk))
  have hsplitE : E = ∑ k ∈ Finset.Icc 1 K, row.haarB k *
      Real.sqrt (2 * row.yk k * (meanJ M L (n - k) p q - j)) +
      ∑ k ∈ Finset.range (K + 1), row.haarB k *
        Real.sqrt (varFactor d * vecNormSq q * varV M L (n - k)) := by
    have hadd : E = ∑ k ∈ Finset.range (K + 1), row.haarB k *
          Real.sqrt (2 * row.yk k * (meanJ M L (n - k) p q - j)) +
        ∑ k ∈ Finset.range (K + 1), row.haarB k *
          Real.sqrt (varFactor d * vecNormSq q * varV M L (n - k)) := by
      rw [hEdef, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hadd]
    congr 1
    have hr : Finset.range (K + 1) = insert 0 (Finset.Icc 1 K) := by
      ext k
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [hr, Finset.sum_insert (by simp), Nat.sub_zero, ← hjdef, sub_self, mul_zero,
      Real.sqrt_zero, mul_zero, zero_add]
  have hT1 : a * Real.sqrt (2 * (row.R : ℝ) * j) *
      (∑ k ∈ Finset.Icc 1 K, row.haarB k *
        Real.sqrt (2 * row.yk k * (meanJ M L (n - k) p q - j))) / row.cNu =
      coefA0 row * Real.sqrt j * ∑ k ∈ Finset.Icc 1 K, row.haarB k *
        Real.sqrt (row.yk k / (row.R : ℝ)) * Real.sqrt (meanJ M L (n - k) p q - j) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ∈ Finset.range (K + 1) := by
      simp only [Finset.mem_Icc] at hk
      simp only [Finset.mem_range]
      omega
    have e := sqrt_drop_coef hR (yk_nonneg row hO k) hj (hΔ k hk')
    calc a * Real.sqrt (2 * (row.R : ℝ) * j) * (row.haarB k *
          Real.sqrt (2 * row.yk k * (meanJ M L (n - k) p q - j))) / row.cNu =
        a * row.haarB k * (Real.sqrt (2 * (row.R : ℝ) * j) *
          Real.sqrt (2 * row.yk k * (meanJ M L (n - k) p q - j))) / row.cNu := by ring
      _ = a * row.haarB k * (2 * (row.R : ℝ) * (Real.sqrt j *
          (Real.sqrt (row.yk k / (row.R : ℝ)) * Real.sqrt (meanJ M L (n - k) p q - j)))) /
            row.cNu := by rw [e]
      _ = _ := by
        rw [coefA0, ha]
        field_simp
  have hT2 : a * Real.sqrt (2 * (row.R : ℝ) * j) *
      (∑ k ∈ Finset.range (K + 1), row.haarB k *
        Real.sqrt (varFactor d * vecNormSq q * varV M L (n - k))) / row.cNu =
      coefAv0 row * Real.sqrt j * ∑ k ∈ Finset.range (K + 1), row.haarB k *
        Real.sqrt (varFactor d * vecNormSq q * varV M L (n - k)) := by
    rw [Real.sqrt_mul (by positivity), coefAv0, ha]
    field_simp
  have hfinal : a * Real.sqrt (2 * (row.R : ℝ) * j) * E / row.cNu =
      coefA0 row * Real.sqrt j * ∑ k ∈ Finset.Icc 1 K, row.haarB k *
        Real.sqrt (row.yk k / (row.R : ℝ)) * Real.sqrt (meanJ M L (n - k) p q - j) +
      coefAv0 row * Real.sqrt j * ∑ k ∈ Finset.range (K + 1), row.haarB k *
        Real.sqrt (varFactor d * vecNormSq q * varV M L (n - k)) := by
    rw [hsplitE, mul_add, add_div, hT1, hT2]
  rw [hfinal] at hY
  linarith [hY]

end GMCExplicitDelta.Localization
