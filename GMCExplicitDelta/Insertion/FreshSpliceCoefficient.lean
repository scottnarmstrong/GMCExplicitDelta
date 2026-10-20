module

public import GMCExplicitDelta.Insertion.FreshSplice
public import GMCExplicitDelta.Proofs.FineSensitivity.Scaled

/-! # The unshifted fresh coefficient on the independent splice -/

@[expose] public section

open MeasureTheory Homogenization Homogenization.Book.Ch02 SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab (aCutoffCoeffOnData ScalarCoeffOnData ahom)

namespace GMCExplicitDelta.Assembly

/-- Positivity of the literal unshifted fresh normalization. -/
theorem freshNorm_pos {d : ℕ} (M : GMCModel d) (L m : ℕ) : 0 < freshNorm M L m :=
  mul_pos (driftSeed_ahom_pos M L) (Real.exp_pos _)

end GMCExplicitDelta.Assembly

namespace GMCExplicitDelta.Insertion

/-- The low cutoff only reads the old coordinates of the splice. -/
theorem aCutoff_splice_prefix {d : ℕ} (M : GMCModel d) (L : ℕ)
    (old fresh : PotentialSample d) (x : Vec d) :
    aCutoff M L (spliceSample L (old, fresh)) x = aCutoff M L old x := by
  unfold aCutoff
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hkL : k ≤ L := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
  simp only [spliceSample, ite_eq_left hkL]

/-- The higher cutoff splits into the old coefficient and the centered fresh band. -/
theorem aCutoff_splice_eq {d : ℕ} (M : GMCModel d) {L m : ℕ} (hLm : L ≤ m)
    (old fresh : PotentialSample d) (x : Vec d) :
    aCutoff M m (spliceSample L (old, fresh)) x = aCutoff M L old x *
      Real.exp ((∑ k ∈ Finset.Ioc L m, fresh k x) - ((m : ℝ) - L) * tauSq M.P) := by
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun k => (spliceSample L (old, fresh)) k x - tauSq M.P)
    (Nat.add_le_add_right hLm 1)
  have hI : Finset.Ico (L + 1) (m + 1) = Finset.Ioc L m := by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_Ioc]
    omega
  rw [hI] at hsplit
  have hband : (∑ k ∈ Finset.Ioc L m, ((spliceSample L (old, fresh)) k x - tauSq M.P)) =
      (∑ k ∈ Finset.Ioc L m, fresh k x) - ((m : ℝ) - L) * tauSq M.P := by
    have he : (∑ k ∈ Finset.Ioc L m, ((spliceSample L (old, fresh)) k x - tauSq M.P)) =
        ∑ k ∈ Finset.Ioc L m, (fresh k x - tauSq M.P) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkL : ¬k ≤ L := by have := (Finset.mem_Ioc.mp hk).1; omega
      simp only [spliceSample, ite_eq_right hkL]
    rw [he, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, Nat.cast_sub hLm]
  unfold aCutoff
  rw [← hsplit, hband, Real.exp_add]
  change aCutoff M L (spliceSample L (old, fresh)) x * _ = aCutoff M L old x * _
  rw [aCutoff_splice_prefix]

/-- Undoing the deterministic fresh centering gives exactly the old normalized
coefficient times the uncentered fresh exponential. -/
theorem splice_unshifted_coefficient {d : ℕ} (M : GMCModel d) {L m : ℕ} (hLm : L ≤ m)
    (old fresh : PotentialSample d) (x : Vec d) :
    (Assembly.freshNorm M L m)⁻¹ * aCutoff M m (spliceSample L (old, fresh)) x =
      ((ahom M L)⁻¹ * aCutoff M L old x) * Real.exp (∑ k ∈ Finset.Ioc L m, fresh k x) := by
  rw [aCutoff_splice_eq M hLm, Assembly.freshNorm, Real.exp_sub, Real.exp_neg]
  field_simp [(Assembly.driftSeed_ahom_pos M L).ne', Real.exp_ne_zero]

/-- Certified scalar data for the literal unshifted new coefficient, written
in the product form required by the conditional transfer. -/
noncomputable def splicedFreshCoeffData {d : ℕ} (M : GMCModel d) {L m : ℕ} (hLm : L ≤ m)
    (old fresh : PotentialSample d) (U : Domain d) :
    ScalarCoeffOnData U (fun x => ((ahom M L)⁻¹ * aCutoff M L old x) *
      Real.exp (∑ k ∈ Finset.Ioc L m, fresh k x)) := by
  have hd := Assembly.fineScaledScalarData
    (aCutoffCoeffOnData M m (spliceSample L (old, fresh)) U)
    (inv_pos.mpr (Assembly.freshNorm_pos M L m))
  convert hd using 1
  funext x
  exact (splice_unshifted_coefficient M hLm old fresh x).symm

end GMCExplicitDelta.Insertion
