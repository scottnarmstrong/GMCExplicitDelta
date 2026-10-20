module

public import GMCExplicitDelta.HistoryLane.Defs
public import GMCExplicitDelta.Proofs.Normalization.Drift
public import SubdiffusiveProcess.CoarseGrainingVocab.PrefixSuffixMeasurability

/-! # The fresh ratio as a suffix-measurable exponential -/

@[expose] public section

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Model

namespace GMCExplicitDelta.Assembly

variable {d : ℕ}

/-- The uncentered fresh band of layers above `k` through `L`. -/
noncomputable def fineBand (k L : ℕ) (ω : PotentialSample d) (x : Homogenization.Vec d) : ℝ :=
  ∑ i ∈ Finset.Ioc k L, ω i x

theorem cutoffRatio_pos (M : GMCModel d) (k L : ℕ) (ω : PotentialSample d) (x : Homogenization.Vec d) :
    0 < cutoffRatio M k L ω x :=
  div_pos (div_pos (aCutoff_pos M L ω x) (driftSeed_ahom_pos M L))
    (div_pos (aCutoff_pos M k ω x) (driftSeed_ahom_pos M k))

/-- The normalized coefficient ratio has exactly the deterministic N2 drift. -/
theorem cutoffRatio_eq_exp (M : GMCModel d) {k L : ℕ} (hkL : k ≤ L)
    (ω : PotentialSample d) (x : Homogenization.Vec d) :
    cutoffRatio M k L ω x =
      Real.exp (fineBand k L ω x - (normShift M L - normShift M k)) := by
  have hsplit : (∑ i ∈ Finset.range (L + 1), (ω i x - tauSq M.P)) =
      (∑ i ∈ Finset.range (k + 1), (ω i x - tauSq M.P)) +
        (fineBand k L ω x - ((L : ℝ) - k) * tauSq M.P) := by
    have hsum := Finset.sum_range_add_sum_Ico (fun i => ω i x - tauSq M.P)
      (Nat.add_le_add_right hkL 1)
    have hinterval : Finset.Ico (k + 1) (L + 1) = Finset.Ioc k L := by
      ext i
      simp only [Finset.mem_Ico, Finset.mem_Ioc]
      omega
    rw [hinterval] at hsum
    simpa [fineBand, Finset.sum_sub_distrib, Nat.card_Ioc, Nat.cast_sub hkL] using hsum.symm
  unfold cutoffRatio aCutoff
  rw [hsplit, Real.exp_add]
  unfold normShift
  have he : fineBand k L ω x -
      (((L : ℝ) + 1) * tauSq M.P + Real.log (ahom M L) -
        (((k : ℝ) + 1) * tauSq M.P + Real.log (ahom M k))) =
      (fineBand k L ω x - ((L : ℝ) - k) * tauSq M.P) +
        Real.log (ahom M k) - Real.log (ahom M L) := by ring
  rw [he]
  simp only [Real.exp_sub, Real.exp_add, Real.exp_log (driftSeed_ahom_pos M k),
    Real.exp_log (driftSeed_ahom_pos M L)]
  field_simp [(driftSeed_ahom_pos M k).ne', (driftSeed_ahom_pos M L).ne', Real.exp_ne_zero]

/-- The band is measurable with respect to the shells strictly above `k`. -/
theorem measurable_fineBand_suffix (k L : ℕ) (x : Homogenization.Vec d) :
    @Measurable (PotentialSample d) ℝ (potentialShellIndexSigma (Set.Ioi k))
      inferInstance (fun ω => fineBand k L ω x) := by
  apply Finset.measurable_sum
  intro i hi
  exact (PotentialField.measurable_eval x).comp
    (measurable_potentialCoordinate_shellIndexSigma (Finset.mem_Ioc.mp hi).1)

/-- Normalization is deterministic, so the ratio retains suffix measurability. -/
theorem measurable_cutoffRatio_suffix (M : GMCModel d) {k L : ℕ} (hkL : k ≤ L)
    (x : Homogenization.Vec d) :
    @Measurable (PotentialSample d) ℝ (potentialShellIndexSigma (Set.Ioi k))
      inferInstance (fun ω => cutoffRatio M k L ω x) := by
  simp_rw [cutoffRatio_eq_exp M hkL]
  exact ((measurable_fineBand_suffix k L x).sub measurable_const).exp

/-- Any prefix observable is independent of the fresh ratio at a fixed point. -/
theorem indepFun_cutoffRatio {E : Type*} [MeasurableSpace E] (M : GMCModel d)
    {k L : ℕ} (hkL : k ≤ L) (x : Homogenization.Vec d)
    {X : PotentialSample d → E}
    (hX : @Measurable (PotentialSample d) E (potentialShellIndexSigma (Set.Iic k))
      inferInstance X) :
    ProbabilityTheory.IndepFun X (fun ω => cutoffRatio M k L ω x) M.P.toMeasure := by
  rw [ProbabilityTheory.IndepFun_iff_Indep, ProbabilityTheory.Indep_iff]
  intro s t hs ht
  exact (ProbabilityTheory.Indep_iff _ _ _).mp
    (indep_potentialShellIndexSigma_Iic_Ioi M k) s t
      (hX.comap_le s hs) ((measurable_cutoffRatio_suffix M hkL x).comap_le t ht)

/-- N2 in the natural fresh-band length used by G4. -/
theorem fine_drift_le (row : Contract.Row d)
    (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (M : GMCModel d) {k L : ℕ} (hkL : k ≤ L) :
    |normShift M L - normShift M k| ≤
      Contract.kappaH d * ((L - k : ℕ) : ℝ) * M.delta ^ 2 := by
  simpa only [Nat.cast_sub hkL] using (normShift_drift_proof row hd hO M).2.1 k L hkL

end GMCExplicitDelta.Assembly
