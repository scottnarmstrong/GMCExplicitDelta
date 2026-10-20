module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Topology.Order.Real
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Data.Rat.Floor

/-!
# Measurable suprema over the rational points of `[0,1]`

For a path family `F t ω`, continuous in `t`, the suprema `supSurr F ω = sup_q |F q ω|` and the Lipschitz
seminorm `lipSurr F ω = sup_{p ≠ q} |F p ω - F q ω| / |p - q|` over rational `p, q ∈ [0,1]` are measurable,
are dominated by any given bound valid on `[0,1]`, and themselves bound the path on all of `[0,1]`.
-/

@[expose] public section

namespace GMCExplicitDelta.Source

open MeasureTheory Set

/-- Rational points of `[0,1]`. -/
abbrev RatI : Type := {q : ℚ // 0 ≤ q ∧ q ≤ 1}

instance : Nonempty RatI := ⟨⟨0, le_rfl, zero_le_one⟩⟩

theorem ratI_mem (q : RatI) : ((q.1 : ℚ) : ℝ) ∈ Set.Icc (0:ℝ) 1 :=
  ⟨by exact_mod_cast q.2.1, by exact_mod_cast q.2.2⟩

theorem Icc_subset_closure_ratI :
    Set.Icc (0:ℝ) 1 ⊆ closure (Set.range fun q : RatI => ((q.1 : ℚ) : ℝ)) := by
  intro t ht
  rw [Metric.mem_closure_iff]
  intro ε hε
  by_cases h1 : t < 1
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show t < min (t + ε) 1 from lt_min (by linarith) h1)
    refine ⟨(q:ℝ), ⟨⟨q, ?_, ?_⟩, rfl⟩, ?_⟩
    · exact_mod_cast (ht.1.trans hq1.le)
    · exact_mod_cast (hq2.le.trans (min_le_right _ _))
    · have := lt_of_lt_of_le hq2 (min_le_left _ _)
      rw [Real.dist_eq, abs_of_neg (by linarith)]; linarith
  · have : t = 1 := le_antisymm ht.2 (not_lt.1 h1)
    refine ⟨((1:ℚ):ℝ), ⟨⟨1, zero_le_one, le_rfl⟩, rfl⟩, ?_⟩
    simp [this, hε]

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Supremum of `|F q ω|` over rational `q ∈ [0,1]`. -/
noncomputable def supSurr (F : ℝ → Ω → ℝ) (ω : Ω) : ℝ := ⨆ q : RatI, |F ((q.1 : ℚ) : ℝ) ω|

/-- Supremum of the difference quotients of `F · ω` over rational points of `[0,1]`. -/
noncomputable def lipSurr (F : ℝ → Ω → ℝ) (ω : Ω) : ℝ :=
  ⨆ p : RatI × RatI, |F ((p.1.1 : ℚ) : ℝ) ω - F ((p.2.1 : ℚ) : ℝ) ω| /
    |((p.1.1 : ℚ) : ℝ) - ((p.2.1 : ℚ) : ℝ)|

theorem measurable_supSurr {F : ℝ → Ω → ℝ} (hF : ∀ t, Measurable (F t)) :
    Measurable (supSurr F) :=
  Measurable.iSup fun _ => continuous_abs.measurable.comp (hF _)

theorem measurable_lipSurr {F : ℝ → Ω → ℝ} (hF : ∀ t, Measurable (F t)) :
    Measurable (lipSurr F) :=
  Measurable.iSup fun _ =>
    (continuous_abs.measurable.comp ((hF _).sub (hF _))).div_const _

section
variable {F : ℝ → Ω → ℝ} {W : Ω → ℝ} (hc : ∀ ω, Continuous fun t => F t ω)

theorem bddAbove_supSurr (hW : ∀ ω, ∀ t ∈ Set.Icc (0:ℝ) 1, |F t ω| ≤ W ω) (ω : Ω) :
    BddAbove (Set.range fun q : RatI => |F ((q.1 : ℚ) : ℝ) ω|) :=
  ⟨W ω, by rintro _ ⟨q, rfl⟩; exact hW ω _ (ratI_mem q)⟩

include hc in
theorem abs_le_supSurr (hW : ∀ ω, ∀ t ∈ Set.Icc (0:ℝ) 1, |F t ω| ≤ W ω) (ω : Ω) {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) 1) : |F t ω| ≤ supSurr F ω := by
  have hS : IsClosed {t : ℝ | |F t ω| ≤ supSurr F ω} :=
    isClosed_le (continuous_abs.comp (hc ω)) continuous_const
  have hsub : Set.range (fun q : RatI => ((q.1 : ℚ) : ℝ)) ⊆ {t : ℝ | |F t ω| ≤ supSurr F ω} := by
    rintro _ ⟨q, rfl⟩
    exact le_ciSup (bddAbove_supSurr hW ω) q
  exact (closure_minimal hsub hS) (Icc_subset_closure_ratI ht)

theorem supSurr_le (hW : ∀ ω, ∀ t ∈ Set.Icc (0:ℝ) 1, |F t ω| ≤ W ω) (ω : Ω) :
    supSurr F ω ≤ W ω :=
  ciSup_le fun q => hW ω _ (ratI_mem q)

end

section
variable {F : ℝ → Ω → ℝ} {W : Ω → ℝ} (hc : ∀ ω, Continuous fun t => F t ω)
  (hW : ∀ ω, ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1, |F s ω - F t ω| ≤ W ω * |s - t|)

include hW in
theorem W_nonneg_of_lip (ω : Ω) : 0 ≤ W ω := by
  have := hW ω 0 ⟨le_rfl, zero_le_one⟩ 1 ⟨zero_le_one, le_rfl⟩
  have h2 := (abs_nonneg _).trans this
  simpa using h2

include hW in
theorem bddAbove_lipSurr (ω : Ω) :
    BddAbove (Set.range fun p : RatI × RatI => |F ((p.1.1 : ℚ) : ℝ) ω - F ((p.2.1 : ℚ) : ℝ) ω| /
      |((p.1.1 : ℚ) : ℝ) - ((p.2.1 : ℚ) : ℝ)|) := by
  refine ⟨W ω, ?_⟩
  rintro _ ⟨p, rfl⟩
  by_cases hp : ((p.1.1 : ℚ) : ℝ) = ((p.2.1 : ℚ) : ℝ)
  · simp only [hp, sub_self, abs_zero, div_zero]
    exact W_nonneg_of_lip hW ω
  · have hpos : 0 < |((p.1.1 : ℚ) : ℝ) - ((p.2.1 : ℚ) : ℝ)| := abs_pos.2 (sub_ne_zero.2 hp)
    rw [div_le_iff₀ hpos]
    exact hW ω _ (ratI_mem p.1) _ (ratI_mem p.2)

include hW in
theorem lipSurr_le (ω : Ω) : lipSurr F ω ≤ W ω := by
  refine ciSup_le fun p => ?_
  by_cases hp : ((p.1.1 : ℚ) : ℝ) = ((p.2.1 : ℚ) : ℝ)
  · simp only [hp, sub_self, abs_zero, div_zero]
    exact W_nonneg_of_lip hW ω
  · have hpos : 0 < |((p.1.1 : ℚ) : ℝ) - ((p.2.1 : ℚ) : ℝ)| := abs_pos.2 (sub_ne_zero.2 hp)
    rw [div_le_iff₀ hpos]
    exact hW ω _ (ratI_mem p.1) _ (ratI_mem p.2)

include hc hW in
theorem abs_sub_le_lipSurr (ω : Ω) {s t : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    |F s ω - F t ω| ≤ lipSurr F ω * |s - t| := by
  have hS : IsClosed {x : ℝ × ℝ | |F x.1 ω - F x.2 ω| ≤ lipSurr F ω * |x.1 - x.2|} :=
    isClosed_le ((continuous_abs.comp (((hc ω).comp continuous_fst).sub ((hc ω).comp continuous_snd))))
      (continuous_const.mul (continuous_abs.comp (continuous_fst.sub continuous_snd)))
  have hsub : Set.range (fun p : RatI × RatI => (((p.1.1 : ℚ) : ℝ), ((p.2.1 : ℚ) : ℝ))) ⊆
      {x : ℝ × ℝ | |F x.1 ω - F x.2 ω| ≤ lipSurr F ω * |x.1 - x.2|} := by
    rintro _ ⟨p, rfl⟩
    by_cases hp : ((p.1.1 : ℚ) : ℝ) = ((p.2.1 : ℚ) : ℝ)
    · simp only [Set.mem_setOf_eq, hp, sub_self, abs_zero, mul_zero]; exact le_rfl
    · have hpos : 0 < |((p.1.1 : ℚ) : ℝ) - ((p.2.1 : ℚ) : ℝ)| := abs_pos.2 (sub_ne_zero.2 hp)
      have := le_ciSup (bddAbove_lipSurr hW ω) p
      change |F _ ω - F _ ω| / |_| ≤ lipSurr F ω at this
      rw [div_le_iff₀ hpos] at this
      exact this
  have hcl : Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 ⊆
      closure (Set.range (fun p : RatI × RatI => (((p.1.1 : ℚ) : ℝ), ((p.2.1 : ℚ) : ℝ)))) := by
    have e : Set.range (fun p : RatI × RatI => (((p.1.1 : ℚ) : ℝ), ((p.2.1 : ℚ) : ℝ))) =
        Set.range (fun q : RatI => ((q.1 : ℚ) : ℝ)) ×ˢ Set.range (fun q : RatI => ((q.1 : ℚ) : ℝ)) := by
      ext x; simp [Prod.ext_iff]
    rw [e, closure_prod_eq]
    exact Set.prod_mono Icc_subset_closure_ratI Icc_subset_closure_ratI
  exact (closure_minimal hsub hS) (hcl (show (s, t) ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 from ⟨hs, ht⟩))

end

end GMCExplicitDelta.Source
