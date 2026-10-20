module

public import GMCExplicitDelta.Proofs.HaarMode.Sobolev

/-! # Finite products of bounded H¹ witnesses -/

@[expose] public section

open MeasureTheory Homogenization Set Filter
open scoped ENNReal

namespace GMCExplicitDelta.Localization

variable {d : ℕ} {U : Set (Homogenization.Vec d)}

/-- Finite products preserve bounded H¹ and satisfy the full Leibniz rule. -/
theorem haarMode_h1_finset_prod {ι : Type*} [DecidableEq ι]
    (hU : IsOpenBoundedConvexDomain U) (s : Finset ι) (u : ι → H1Function U)
    {C : ℝ} (hC : 1 ≤ C)
    (hb : ∀ i ∈ s, ∀ᵐ x ∂volume.restrict U, |u i x| ≤ C) :
    ∃ w : H1Function U, w.toFun = (fun x => ∏ i ∈ s, u i x) ∧
      w.grad = (fun x j => ∑ i ∈ s, (u i).grad x j * ∏ k ∈ s.erase i, u k x) ∧
      ∀ᵐ x ∂volume.restrict U, |w x| ≤ C ^ s.card := by
  let : IsFiniteMeasure (volumeMeasureOn U) := hU.isBoundedDomain.isFiniteMeasure_restrict_volume
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  revert hb
  induction s using Finset.induction_on with
  | empty =>
    intro _
    refine ⟨H1Function.const 1, ?_, ?_, ?_⟩
    · funext x
      simp only [Finset.prod_empty, H1Function.const]
    · funext x j
      simp only [Finset.sum_empty, H1Function.const, Pi.zero_apply]
    · exact Filter.Eventually.of_forall fun x => by simp [H1Function.const]
  | @insert a s ha ih =>
    intro hb
    obtain ⟨v, hvf, hvg, hvb⟩ := ih (fun i hi => hb i (Finset.mem_insert_of_mem hi))
    have hab := hb a (Finset.mem_insert_self a s)
    let B := max C (C ^ s.card)
    have hB0 : 0 ≤ B := hC0.trans (le_max_left _ _)
    have hau : ∀ᵐ x ∂volume.restrict U, |u a x| ≤ B := hab.mono fun _ hx => hx.trans (le_max_left _ _)
    have hav : ∀ᵐ x ∂volume.restrict U, |v x| ≤ B := hvb.mono fun _ hx => hx.trans (le_max_right _ _)
    obtain ⟨w, hwf, hwg⟩ := haarMode_h1_mul hU (u a) v hB0 hau hav
    refine ⟨w, ?_, ?_, ?_⟩
    · funext x
      rw [hwf, hvf, Finset.prod_insert ha]
    · have hsum (x : Homogenization.Vec d) (j : Fin d) :
          (∑ i ∈ insert a s, (u i).grad x j * ∏ k ∈ (insert a s).erase i, u k x) =
            (u a).grad x j * ∏ k ∈ s, u k x +
              u a x * ∑ i ∈ s, (u i).grad x j * ∏ k ∈ s.erase i, u k x := by
        rw [Finset.sum_insert ha, Finset.erase_insert ha, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        have hai : a ≠ i := fun heq => ha (heq ▸ hi)
        rw [Finset.erase_insert_of_ne hai, Finset.prod_insert
          (fun hx => ha (Finset.mem_of_mem_erase hx))]
        ring
      funext x j
      rw [hwg, hsum]
      simp only [hvf, hvg]
      ring
    · filter_upwards [hab, hvb] with x hax hvx
      rw [hwf]
      simp only [Finset.card_insert_of_notMem ha, pow_succ, abs_mul]
      exact (mul_le_mul hax hvx (abs_nonneg _) hC0).trans_eq (mul_comm _ _)

end GMCExplicitDelta.Localization
