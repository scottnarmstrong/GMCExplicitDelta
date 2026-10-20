module

public import SubdiffusiveProcess.Model.G2Observable
public import GMCExplicitDelta.Source.EndpointStripReal
public import Mathlib.Analysis.Calculus.FDeriv.Comp

/-!
# The diagonal process of a potential field and the pointwise endpoint-strip bound

For `g : PotentialField d` put `G(t) = g((t - 1/2) e)`, `e = (1,…,1)`.  The cube norm
`g2Observable g` dominates `A + B + C`, and the endpoint-strip estimate gives
`max |G 0| |G 1| + K |G 1 - G 0 - r (G' 0 + G' 1)| ≤ g2Observable g`.
-/

@[expose] public section

namespace GMCExplicitDelta.Source

open Homogenization SubdiffusiveProcess.Model SubdiffusiveProcess.Model.PotentialField

variable {d : ℕ}

/-- The point `(t - 1/2) e` of the main diagonal. -/
noncomputable def diagPt (d : ℕ) (t : ℝ) : Vec d := fun _ => t - 1 / 2

/-- The diagonal direction `e = (1,…,1)`. -/
def diagDir (d : ℕ) : Vec d := fun _ => 1

theorem diagPt_eq (t : ℝ) : diagPt d t = (t - 1 / 2) • diagDir d := by
  ext i; simp [diagPt, diagDir]

theorem norm_diagDir_le : ‖diagDir d‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro i; simp [diagDir]

theorem hasDerivAt_diagPt (t : ℝ) : HasDerivAt (diagPt d) (diagDir d) t := by
  rw [hasDerivAt_pi]
  intro i
  simpa [diagPt, diagDir] using (hasDerivAt_id t).sub_const (1 / 2 : ℝ)

theorem diagPt_mem_openCube {t : ℝ} (ht : t ∈ Set.Ioo (0:ℝ) 1) :
    diagPt d t ∈ openCubeSet (originCube d 0) := by
  intro i
  simp [diagPt, originCube, cubeScaleFactor]
  constructor <;> linarith [ht.1, ht.2]

/-- Diagonal value process. -/
noncomputable def diagG (g : PotentialField d) (t : ℝ) : ℝ := g (diagPt d t)

/-- Diagonal derivative process. -/
noncomputable def diagG' (g : PotentialField d) (t : ℝ) : ℝ := deriv g (diagPt d t) (diagDir d)

theorem hasDerivAt_diagG (g : PotentialField d) (t : ℝ) :
    HasDerivAt (diagG g) (diagG' g t) t := by
  have h := (g.hasFDerivAt (diagPt d t)).comp_hasDerivAt t (hasDerivAt_diagPt t)
  exact h

theorem continuous_diagG' (g : PotentialField d) : Continuous (diagG' g) := by
  unfold diagG'
  have : Continuous (diagPt d) := continuous_pi fun i => continuous_id.sub continuous_const
  exact ((deriv g).continuous.comp this).clm_apply continuous_const


/-! ### Boundedness of the cube suprema -/

theorem openCube_subset_Icc : openCubeSet (originCube d 0) ⊆ Set.Icc (fun _ => (-1 / 2 : ℝ)) (fun _ => 1 / 2) := by
  intro x hx
  constructor <;> intro i <;> have := hx i <;> simp [originCube, cubeScaleFactor] at this <;>
    linarith [this.1, this.2]

theorem isCompact_cubeIcc : IsCompact (Set.Icc (fun _ : Fin d => (-1 / 2 : ℝ)) (fun _ => 1 / 2)) :=
  isCompact_Icc

theorem bddAbove_value (g : PotentialField d) :
    BddAbove (Set.range fun o : Option {x : Vec d // x ∈ openCubeSet (originCube d 0)} ↦
      match o with
      | none => (0:ℝ)
      | some x => |g x.1|) := by
  obtain ⟨M, hM⟩ := (isCompact_cubeIcc (d := d)).exists_bound_of_continuousOn
    (f := fun x : Vec d => g x) g.1.1.continuous.continuousOn
  refine ⟨max M 0, ?_⟩
  rintro _ ⟨o, rfl⟩
  cases o with
  | none => exact le_max_right _ _
  | some x =>
    exact (hM x.1 (openCube_subset_Icc x.2)).trans (le_max_left _ _)

theorem bddAbove_deriv (g : PotentialField d) :
    BddAbove (Set.range fun o : Option {x : Vec d // x ∈ openCubeSet (originCube d 0)} ↦
      match o with
      | none => (0:ℝ)
      | some x => ‖deriv g x.1‖) := by
  obtain ⟨M, hM⟩ := (isCompact_cubeIcc (d := d)).exists_bound_of_continuousOn
    (f := fun x : Vec d => deriv g x) (deriv g).continuous.continuousOn
  refine ⟨max M 0, ?_⟩
  rintro _ ⟨o, rfl⟩
  cases o with
  | none => exact le_max_right _ _
  | some x =>
    exact (hM x.1 (openCube_subset_Icc x.2)).trans (le_max_left _ _)

theorem bddAbove_lip (g : PotentialField d) :
    BddAbove (Set.range fun o : Option
      {p : ({x : Vec d // x ∈ openCubeSet (originCube d 0)} ×
          {x : Vec d // x ∈ openCubeSet (originCube d 0)}) // p.1 ≠ p.2} ↦
    match o with
    | none => (0:ℝ)
    | some p => dist (deriv g p.1.1.1) (deriv g p.1.2.1) / dist p.1.1.1 p.1.2.1) := by
  obtain ⟨C, hC⟩ := g.2.2 _ (isCompact_cubeIcc (d := d))
  refine ⟨max (C : ℝ) 0, ?_⟩
  rintro _ ⟨o, rfl⟩
  cases o with
  | none => exact le_max_right _ _
  | some p =>
    refine le_trans ?_ (le_max_left _ _)
    have hne : p.1.1.1 ≠ p.1.2.1 := fun h => p.2 (Subtype.ext h)
    have hpos : 0 < dist p.1.1.1 p.1.2.1 := dist_pos.2 hne
    rw [div_le_iff₀ hpos]
    exact hC.dist_le_mul _ (openCube_subset_Icc p.1.1.2) _ (openCube_subset_Icc p.1.2.2)


/-! ### Diagonal bounds -/

theorem Icc_le_of_Ioo_le {F : ℝ → ℝ} (hF : Continuous F) {c : ℝ}
    (h : ∀ t ∈ Set.Ioo (0:ℝ) 1, F t ≤ c) : ∀ t ∈ Set.Icc (0:ℝ) 1, F t ≤ c := by
  have hsub : Set.Icc (0:ℝ) 1 ⊆ closure (Set.Ioo (0:ℝ) 1) := by
    rw [closure_Ioo zero_ne_one]
  exact fun t ht => (isClosed_le hF continuous_const).closure_subset_iff.2 h (hsub ht)

theorem Icc2_le_of_Ioo_le {F : ℝ × ℝ → ℝ} (hF : Continuous F) {c : ℝ}
    (h : ∀ s ∈ Set.Ioo (0:ℝ) 1, ∀ t ∈ Set.Ioo (0:ℝ) 1, F (s, t) ≤ c) :
    ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1, F (s, t) ≤ c := by
  have hsub : Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 ⊆
      closure (Set.Ioo (0:ℝ) 1 ×ˢ Set.Ioo (0:ℝ) 1) := by
    rw [closure_prod_eq, closure_Ioo zero_ne_one]
  intro s hs t ht
  exact (isClosed_le hF continuous_const).closure_subset_iff.2
    (fun p hp => h p.1 hp.1 p.2 hp.2) (hsub ⟨hs, ht⟩)

theorem continuous_diagPt : Continuous (diagPt d) :=
  continuous_pi fun _ => continuous_id.sub continuous_const

theorem continuous_diagG (g : PotentialField d) : Continuous (diagG g) :=
  g.1.1.continuous.comp continuous_diagPt

theorem diagG_le (g : PotentialField d) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    |diagG g t| ≤ unitCubeValueNorm g := by
  refine Icc_le_of_Ioo_le (F := fun t => |diagG g t|) (continuous_diagG g).abs ?_ t ht
  intro t ht
  unfold unitCubeValueNorm
  exact le_csSup (bddAbove_value g) ⟨some ⟨diagPt d t, diagPt_mem_openCube ht⟩, rfl⟩

theorem diagG'_le (g : PotentialField d) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    |diagG' g t| ≤ unitCubeDerivNorm g := by
  refine Icc_le_of_Ioo_le (F := fun t => |diagG' g t|) (continuous_diagG' g).abs ?_ t ht
  intro t ht
  unfold unitCubeDerivNorm
  refine le_trans ?_ (le_csSup (bddAbove_deriv g)
    ⟨some ⟨diagPt d t, diagPt_mem_openCube ht⟩, rfl⟩)
  have := (deriv g (diagPt d t)).le_opNorm (diagDir d)
  rw [diagG', Real.norm_eq_abs] at *
  calc _ ≤ ‖deriv g (diagPt d t)‖ * ‖diagDir d‖ := this
    _ ≤ ‖deriv g (diagPt d t)‖ * 1 := by gcongr; exact norm_diagDir_le
    _ = _ := mul_one _

theorem diagG'_lip (g : PotentialField d) {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) 1) :
    |diagG' g s - diagG' g t| ≤ unitCubeDerivLipschitzSeminorm g * |s - t| := by
  have hcont : Continuous (fun p : ℝ × ℝ =>
      |diagG' g p.1 - diagG' g p.2| - unitCubeDerivLipschitzSeminorm g * |p.1 - p.2|) := by
    have := continuous_diagG' g
    fun_prop
  have := Icc2_le_of_Ioo_le (F := fun p : ℝ × ℝ =>
      |diagG' g p.1 - diagG' g p.2| - unitCubeDerivLipschitzSeminorm g * |p.1 - p.2|)
    hcont (c := 0) ?_ s hs t ht
  · simpa using this
  · intro s hs t ht
    have hL : 0 ≤ unitCubeDerivLipschitzSeminorm g := by
      unfold unitCubeDerivLipschitzSeminorm
      exact le_csSup_of_le (bddAbove_lip g) ⟨none, rfl⟩ le_rfl
    show |diagG' g s - diagG' g t| - unitCubeDerivLipschitzSeminorm g * |s - t| ≤ 0
    rw [sub_nonpos]
    by_cases hst : diagPt d s = diagPt d t
    · have : diagG' g s = diagG' g t := by unfold diagG'; rw [hst]
      rw [this]; simp; positivity
    · have hle : dist (deriv g (diagPt d s)) (deriv g (diagPt d t)) /
          dist (diagPt d s) (diagPt d t) ≤ unitCubeDerivLipschitzSeminorm g := by
        unfold unitCubeDerivLipschitzSeminorm
        exact le_csSup (bddAbove_lip g)
          ⟨some ⟨(⟨diagPt d s, diagPt_mem_openCube hs⟩, ⟨diagPt d t, diagPt_mem_openCube ht⟩),
            fun h => hst (congrArg Subtype.val h)⟩, rfl⟩
      have hpts : dist (diagPt d s) (diagPt d t) = |s - t| * ‖diagDir d‖ := by
        rw [dist_eq_norm, diagPt_eq, diagPt_eq, ← sub_smul, norm_smul, Real.norm_eq_abs]
        congr 2; ring
      have hpos : 0 < dist (diagPt d s) (diagPt d t) := dist_pos.2 hst
      rw [div_le_iff₀ hpos, hpts] at hle
      have h1 : |diagG' g s - diagG' g t| ≤
          dist (deriv g (diagPt d s)) (deriv g (diagPt d t)) * ‖diagDir d‖ := by
        have : diagG' g s - diagG' g t =
            (deriv g (diagPt d s) - deriv g (diagPt d t)) (diagDir d) := by
          unfold diagG'; simp
        rw [this, ← Real.norm_eq_abs, dist_eq_norm]
        exact (deriv g (diagPt d s) - deriv g (diagPt d t)).le_opNorm (diagDir d)
      have he := norm_diagDir_le (d := d)
      have he0 := norm_nonneg (diagDir d)
      calc _ ≤ _ := h1
        _ ≤ (unitCubeDerivLipschitzSeminorm g * (|s - t| * ‖diagDir d‖)) * ‖diagDir d‖ :=
            mul_le_mul_of_nonneg_right hle he0
        _ ≤ (unitCubeDerivLipschitzSeminorm g * (|s - t| * 1)) * 1 := by
            gcongr
        _ = _ := by ring


theorem unitCubeValueNorm_nonneg (g : PotentialField d) : 0 ≤ unitCubeValueNorm g := by
  unfold unitCubeValueNorm
  exact le_csSup_of_le (bddAbove_value g) ⟨none, rfl⟩ le_rfl

theorem unitCubeDerivNorm_nonneg (g : PotentialField d) : 0 ≤ unitCubeDerivNorm g := by
  unfold unitCubeDerivNorm
  exact le_csSup_of_le (bddAbove_deriv g) ⟨none, rfl⟩ le_rfl

theorem unitCubeDerivLipschitzSeminorm_nonneg (g : PotentialField d) :
    0 ≤ unitCubeDerivLipschitzSeminorm g := by
  unfold unitCubeDerivLipschitzSeminorm
  exact le_csSup_of_le (bddAbove_lip g) ⟨none, rfl⟩ le_rfl

theorem g2Observable_nonneg (g : PotentialField d) : 0 ≤ g2Observable g :=
  add_nonneg (add_nonneg (unitCubeValueNorm_nonneg g) (unitCubeDerivNorm_nonneg g))
    (unitCubeDerivLipschitzSeminorm_nonneg g)

theorem abs_apply_le_g2Observable (g : PotentialField d) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d 0)) : |g x| ≤ g2Observable g := by
  have h1 : |g x| ≤ unitCubeValueNorm g := by
    unfold unitCubeValueNorm
    exact le_csSup (bddAbove_value g) ⟨some ⟨x, hx⟩, rfl⟩
  have := unitCubeDerivNorm_nonneg g
  have := unitCubeDerivLipschitzSeminorm_nonneg g
  unfold g2Observable; linarith

theorem norm_deriv_le_g2Observable (g : PotentialField d) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d 0)) : ‖deriv g x‖ ≤ g2Observable g := by
  have h1 : ‖deriv g x‖ ≤ unitCubeDerivNorm g := by
    unfold unitCubeDerivNorm
    exact le_csSup (bddAbove_deriv g) ⟨some ⟨x, hx⟩, rfl⟩
  have := unitCubeValueNorm_nonneg g
  have := unitCubeDerivLipschitzSeminorm_nonneg g
  unfold g2Observable; linarith

/-- The endpoint values and derivatives of the diagonal process. -/
noncomputable def epX (g : PotentialField d) : ℝ := diagG g 0
noncomputable def epY (g : PotentialField d) : ℝ := diagG g 1
noncomputable def epP (g : PotentialField d) : ℝ := diagG' g 0
noncomputable def epQ (g : PotentialField d) : ℝ := diagG' g 1
noncomputable def epZ (g : PotentialField d) : ℝ := epP g + epQ g

/-- Pointwise: `max(|X|,|Y|) + K |Y - X - r (P+Q)| ≤ W`. -/
theorem endpoint_pointwise (g : PotentialField d) :
    max |epX g| |epY g| + stripK * |(epY g - epX g) - stripR * epZ g| ≤
      g2Observable g := by
  have := endpoint_strip_bound (G := diagG g) (G' := diagG' g) (hG := hasDerivAt_diagG g)
    (continuous_diagG' g) (fun t ht => diagG_le g ht) (fun t ht => diagG'_le g ht)
    (fun s hs t ht => diagG'_lip g hs ht)
  exact this

end GMCExplicitDelta.Source
