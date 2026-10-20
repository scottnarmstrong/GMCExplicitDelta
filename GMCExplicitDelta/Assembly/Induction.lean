module

public import GMCExplicitDelta.Assembly.FrozenStep
public import GMCExplicitDelta.Assembly.Insertion
public import GMCExplicitDelta.Steps.AssemblyScaling

/-!
# Assembly: the induction on the cutoff (steps R3, R5) and `cascade_of_obligations`

Fix a row in dimension `d ∈ {2,3,4}` with its numeric obligations, a model with `δ ≤ δ_*`, and
`λ = (δ/δ_*)²`. `inductionP_all` proves `𝖯(m; λD, λF)` for every cutoff `m` by strong induction:

* **seeds** (`m ≤ h - 1`): K2, K3 at `δ`, and R4(g) `seed_λ ≤ λ seed < λD`,
  `meanseed_λ ≤ λ meanseed < λF` (O.ret.3, O.ret.4);
* **step** (`m = L + h`): R4 supplies the scalar hypotheses of the frozen step at `(δ, λD, λF)`
  (`z_F` monotone, `𝔲_ℓ` invariant, `θ_R > F ≥ λF`, `bad_λ ≤ bad < b_bad`, `𝔰_λ > 0`); the frozen
  step R2 gives `f_{L+h} < F_next` and the cap `D_next`; the insertion I9 (with
  `F_next(λF) = λF_next ≤ λD_next = D_next(λD, λF)`, O.fin.1) and R4(g) give
  `post_λ ≤ λ post < λD`, `meanpost_λ ≤ λ meanpost < λF` (O.ret.1, O.ret.2); R1 extends to all cubes
  (R3).

`cascade_assembled` rewrites `λD = (D/δ_*²)δ²`, `λF = (F/δ_*²)δ²` into the cascade conclusion.
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta.Assembly

open Contract

variable {d : ℕ}

theorem tStar_pos (row : Row d) (hO : row.Obligations) : 0 < row.tStar := by
  unfold Row.tStar
  have hZ : (0 : ℝ) < (row.Z : ℝ) := by exact_mod_cast hO.bar1.1
  have hM : (0 : ℝ) < (row.Mwin : ℝ) := by unfold Row.Mwin; exact_mod_cast Nat.succ_pos _
  exact div_pos hZ hM

/-- **R5 (strong induction on the cutoff).** `𝖯(m; λD, λF)` for every `m`, `λ = (δ/δ_*)²`. -/
theorem inductionP_all (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (M : SubdiffusiveProcess.Model.GMCModel d) (hδ : M.delta ≤ (row.deltaStar : ℝ)) :
    ∀ m, InductionP M m (lamOf row M.delta * row.D) (lamOf row M.delta * row.F) := by
  have hδ0 := M.shellPrefix.delta_pos
  have hl0 := lamOf_pos row hδ0 hδ
  have hl1 := lamOf_le_one row hδ0 hδ
  obtain ⟨hpost, hmeanpost, hseed, hmeanseed⟩ := freshReturns_scale_le row hd hO hδ0 hδ
  have hD0 : (0 : ℝ) < (row.D : ℝ) := by exact_mod_cast hO.par1.1
  have hF0 : (0 : ℝ) < (row.F : ℝ) := by exact_mod_cast hO.par1.2.1
  have hFmin : (row.F : ℝ) ≤ min (row.D : ℝ) 1 := by exact_mod_cast hO.par1.2.2.1
  have hFD : (row.F : ℝ) ≤ (row.D : ℝ) := hFmin.trans (min_le_left _ _)
  have hF1 : (row.F : ℝ) ≤ 1 := hFmin.trans (min_le_right _ _)
  have hh : 1 ≤ row.h := by
    have h1 := hO.par1.2.2.2.1
    have h2 := hO.par1.2.2.2.2.1
    have : 2 ≤ row.g := le_trans (le_max_right _ _) h1
    omega
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  by_cases hm : m + 1 ≤ row.h
  · -- seeds (K2, K3)
    intro n hmn z
    obtain ⟨hmeas1, hmeas2⟩ := measurable_cascadeObservables M m (cubeAt z n)
    have hs : row.seed M.delta ≤ lamOf row M.delta * row.D :=
      hseed.trans (mul_le_mul_of_nonneg_left hO.ret3.le hl0.le)
    have hms : row.meanseed M.delta ≤ lamOf row M.delta * row.F :=
      hmeanseed.trans (mul_le_mul_of_nonneg_left hO.ret4.le hl0.le)
    exact ⟨hmeas1 (ahom M m),
      (normSeed_bound row hd hO M m hm n hmn z).trans (ENNReal.ofReal_le_ofReal hs),
      fun e he => ⟨hmeas2 ((Real.sqrt (ahom M m))⁻¹ • e) (Real.sqrt (ahom M m) • e),
        (meanSeed_bound row hd hO M m hm n hmn z e he).trans (ENNReal.ofReal_le_ofReal hms)⟩⟩
  · -- step (R2, I9, R1)
    obtain ⟨L, rfl⟩ : ∃ L, m = L + row.h := ⟨m - row.h, by omega⟩
    have hP : ∀ k ≤ L, InductionP M k (lamOf row M.delta * row.D) (lamOf row M.delta * row.F) :=
      fun k hk => ih k (by omega)
    -- R4: the scalar hypotheses at (δ, λD, λF)
    have hzF : row.zF M.delta < 1 :=
      (zF_le_of_le row hδ0 hδ).trans_lt hO.hist1.2
    have hu : frakU d row.historyCutoff (lamOf row M.delta * row.D)
        (lamOf row M.delta * row.F) < 1 := by
      rw [frakU_smul hl0]; exact hO.avg5
    have hlF : lamOf row M.delta * row.F ≤ row.F := mul_le_of_le_one_left hF0.le hl1
    have hθ : lamOf row M.delta * row.F < row.thetaR := hlF.trans_lt hO.bad1
    have hbad : row.badCharge M.delta (lamOf row M.delta * row.D) (lamOf row M.delta * row.F) ≤
        row.badBudget :=
      (badCharge_scale_le row hd hO hδ0 hδ).trans hO.bad2.le
    have hbar := barrier_scale_pos row hd hO hl0 hl1
    -- R2: the frozen step
    obtain ⟨hfs, hDn⟩ := frozenStep row hd hO M (mul_pos hl0 hD0) (mul_pos hl0 hF0)
      (hlF.trans hF1) (mul_le_mul_of_nonneg_left hFD hl0.le) hzF hu hθ hbad hbar L hP
    -- I9: the insertion
    have hpos : 0 < row.Fnext (lamOf row M.delta * row.F) := by
      unfold Row.Fnext; exact mul_pos (tStar_pos row hO) (mul_pos hl0 hF0)
    have hle : row.Fnext (lamOf row M.delta * row.F) ≤
        row.Dnext (lamOf row M.delta * row.D) (lamOf row M.delta * row.F) := by
      rw [Fnext_smul, Dnext_smul row hl0]
      exact mul_le_mul_of_nonneg_left hO.fin1 hl0.le
    have hI9 := freshInsertion row hd hO M (mul_pos hl0 hF0).le L hpos hle hfs.le hDn
    have hp : row.post M.delta (lamOf row M.delta * row.D) (lamOf row M.delta * row.F) ≤
        lamOf row M.delta * row.D :=
      hpost.trans (mul_le_mul_of_nonneg_left hO.ret1.le hl0.le)
    have hmp : row.meanpost M.delta (lamOf row M.delta * row.F) ≤ lamOf row M.delta * row.F :=
      hmeanpost.trans (mul_le_mul_of_nonneg_left hO.ret2.le hl0.le)
    -- R1: all larger cubes
    exact inductionP_of_cubeBounds M (L + row.h)
      (fun z => (hI9 z).1.trans (ENNReal.ofReal_le_ofReal hp))
      (fun z e he => ((hI9 z).2 e he).trans (ENNReal.ofReal_le_ofReal hmp))

/-- **The assembled analytic half of the contract (R5).** -/
theorem cascade_assembled (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ))
    (hO : row.Obligations) (M : SubdiffusiveProcess.Model.GMCModel d)
    (hδ : M.delta ≤ (row.deltaStar : ℝ)) :
    CascadeConclusion M ((row.D : ℝ) / (row.deltaStar : ℝ) ^ 2)
      ((row.F : ℝ) / (row.deltaStar : ℝ) ^ 2) := by
  rw [cascadeConclusion_iff_forall_inductionP]
  intro m
  have h := inductionP_all row hd hO M hδ m
  rwa [lamOf_mul, lamOf_mul] at h

end GMCExplicitDelta.Assembly
