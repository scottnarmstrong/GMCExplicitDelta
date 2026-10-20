module

public import SubdiffusiveProcess.CoarseGrainingVocab.PrefixSuffixMeasurability

/-! # Replacing the strict suffix by an independent sample preserves the model law -/

@[expose] public section

open MeasureTheory ProbabilityTheory SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

namespace GMCExplicitDelta.Insertion

/-- Keep the old prefix and take the strict suffix from an independent fresh sample. -/
noncomputable def spliceSample {d : ℕ} (L : ℕ) (q : PotentialSample d × PotentialSample d) : PotentialSample d :=
  fun k => if k ≤ L then q.1 k else q.2 k

theorem measurable_spliceSample {d : ℕ} (L : ℕ) : Measurable (spliceSample (d := d) L) := by
  apply measurable_pi_iff.mpr
  intro k
  by_cases hk : k ≤ L
  · simpa only [spliceSample, ite_eq_left hk, Function.comp_def] using (measurable_potentialCoordinate k).comp
      (show Measurable (Prod.fst : PotentialSample d × PotentialSample d → PotentialSample d) from measurable_fst)
  · simpa only [spliceSample, ite_eq_right hk, Function.comp_def] using (measurable_potentialCoordinate k).comp
      (show Measurable (Prod.snd : PotentialSample d × PotentialSample d → PotentialSample d) from measurable_snd)

/-- The independent old-prefix/fresh-suffix splice has exactly the original sample law. -/
theorem spliceSample_measurePreserving {d : ℕ} (M : GMCModel d) (L : ℕ) :
    MeasurePreserving (spliceSample L) (M.P.toMeasure.prod M.P.toMeasure) M.P.toMeasure := by
  let X : PotentialSample d → PotentialSample d := potentialShellProjection (Set.Iic L)
  let Y : PotentialSample d → PotentialSample d := potentialShellProjection (Set.Ioi L)
  have hXσ := measurable_potentialShellProjection (d := d) (Set.Iic L)
  have hYσ := measurable_potentialShellProjection (d := d) (Set.Ioi L)
  have hX : Measurable X := hXσ.mono (potentialShellIndexSigma_le_borel (Set.Iic L)) le_rfl
  have hY : Measurable Y := hYσ.mono (potentialShellIndexSigma_le_borel (Set.Ioi L)) le_rfl
  have hd : Disjoint (Set.Iic L) (Set.Ioi L) := Set.disjoint_left.mpr fun _ hx hy =>
    (not_lt_of_ge (Set.mem_Iic.mp hx)) (Set.mem_Ioi.mp hy)
  have hi : IndepFun X Y M.P.toMeasure :=
    indepFun_of_measurable_potentialShellIndexSigma_of_disjoint M hd hXσ hYσ
  have hpair := hi.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable
  have hdiag (ω : PotentialSample d) : spliceSample L (X ω, Y ω) = ω := by
    funext k
    by_cases hk : k ≤ L <;> simp [spliceSample, X, Y, potentialShellProjection, hk, Set.mem_Iic, Set.mem_Ioi]
  have hproj (q : PotentialSample d × PotentialSample d) :
      spliceSample L (Prod.map X Y q) = spliceSample L q := by
    funext k
    by_cases hk : k ≤ L <;> simp [spliceSample, X, Y, potentialShellProjection, hk, Set.mem_Iic, Set.mem_Ioi]
  refine ⟨measurable_spliceSample L, ?_⟩
  calc
    _ = (M.P.toMeasure.prod M.P.toMeasure).map (spliceSample L ∘ Prod.map X Y) := by
      congr 1
      funext q
      exact (hproj q).symm
    _ = ((M.P.toMeasure.prod M.P.toMeasure).map (Prod.map X Y)).map (spliceSample L) :=
      (Measure.map_map (measurable_spliceSample L) (hX.prodMap hY)).symm
    _ = ((M.P.toMeasure.map X).prod (M.P.toMeasure.map Y)).map (spliceSample L) := by
      rw [← Measure.map_prod_map _ _ hX hY]
    _ = (M.P.toMeasure.map (fun ω => (X ω, Y ω))).map (spliceSample L) := by rw [← hpair]
    _ = M.P.toMeasure.map (spliceSample L ∘ fun ω => (X ω, Y ω)) :=
      Measure.map_map (measurable_spliceSample L) (hX.prodMk hY)
    _ = M.P.toMeasure := by
      have he : (spliceSample L ∘ fun ω => (X ω, Y ω)) = id := funext hdiag
      rw [he, Measure.map_id]

/-- Expectations may be evaluated by first fixing the old sample and averaging the fresh sample. -/
theorem lintegral_eq_spliced_iterated {d : ℕ} (M : GMCModel d) (L : ℕ)
    {F : PotentialSample d → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ ω, F ω ∂M.P.toMeasure) =
      ∫⁻ old, ∫⁻ fresh, F (spliceSample L (old, fresh)) ∂M.P.toMeasure ∂M.P.toMeasure := by
  rw [← (spliceSample_measurePreserving M L).lintegral_comp hF]
  have hm : AEMeasurable (fun q : PotentialSample d × PotentialSample d => F (spliceSample L q))
      (M.P.toMeasure.prod M.P.toMeasure) := (hF.comp (measurable_spliceSample L)).aemeasurable
  exact lintegral_prod _ hm

end GMCExplicitDelta.Insertion
