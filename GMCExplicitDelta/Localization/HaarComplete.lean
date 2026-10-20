module

public import GMCExplicitDelta.Haar.TriadicProjection
public import Homogenization.Multiscale.ProjectionConvergence

/-!
# Completeness of the triadic Haar system in `L²` (H1)

`energy_sub_projection_tendsto_proof`: for `f ∈ L²(Q)`, `‖f - E_N f‖² → 0`. Proof: `‖E_N f‖²` is
nondecreasing and bounded by `‖f‖²` (finite Parseval); by the a.e. convergence `E_N f → f`
(Lebesgue differentiation, CoarseGraining `ae_tendsto_cubeProjection_of_integrableOn`) and Fatou,
`‖f‖² ≤ lim ‖E_N f‖²`; hence `‖f - E_N f‖² = ‖f‖² - ‖E_N f‖² → 0`.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace GMCExplicitDelta.Localization

variable {d : ℕ}

theorem ofReal_energy_eq_lintegral (Q : TriadicCube d) {g : Vec d → ℝ}
    (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    ENNReal.ofReal (Haar.energy Q g) = ∫⁻ x, ENNReal.ofReal (g x * g x) ∂normalizedCubeMeasure Q := by
  rw [Haar.energy, Haar.pairing, cubeAverage_eq_integral_normalizedCubeMeasure]
  exact ofReal_integral_eq_lintegral_ofReal (hg.integrable_mul hg)
    (Filter.Eventually.of_forall fun x => mul_self_nonneg (g x))

theorem energy_projection_mono (Q : TriadicCube d) {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    Monotone fun N => Haar.energy Q (cubeProjection Q N f) := by
  refine monotone_nat_of_le_succ fun N => ?_
  rw [Haar.energy_projection_sum Q N hf, Haar.energy_projection_sum Q (N + 1) hf,
    Finset.sum_range_succ _ (N + 1)]
  exact le_add_of_nonneg_right (Haar.energy_nonneg Q _)

theorem energy_sub_projection_tendsto_proof (Q : TriadicCube d) {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    Filter.Tendsto (fun N => Haar.energy Q (fun x => f x - cubeProjection Q N f x))
      Filter.atTop (nhds 0) := by
  set a : ℕ → ℝ := fun N => Haar.energy Q (cubeProjection Q N f) with ha
  have hmono : Monotone a := energy_projection_mono Q hf
  have hbdd : ∀ N, a N ≤ Haar.energy Q f := fun N => Haar.energy_projection_le Q N hf
  have hlim : Filter.Tendsto a Filter.atTop (nhds (⨆ N, a N)) :=
    tendsto_atTop_ciSup hmono ⟨Haar.energy Q f, fun _ ⟨N, hN⟩ => hN ▸ hbdd N⟩
  set A := ⨆ N, a N with hA
  have hAle : A ≤ Haar.energy Q f := ciSup_le hbdd
  have hA0 : 0 ≤ A := (Haar.energy_nonneg Q _).trans (le_ciSup ⟨Haar.energy Q f,
    fun _ ⟨N, hN⟩ => hN ▸ hbdd N⟩ 0)
  -- Fatou
  have hint : IntegrableOn f (cubeSet Q) volume :=
    integrableOn_of_integrable_normalizedCubeMeasure Q (hf.integrable (by norm_num))
  have hae : ∀ᵐ x ∂normalizedCubeMeasure Q,
      Filter.Tendsto (fun N => cubeProjection Q N f x) Filter.atTop (nhds (f x)) := by
    have h := ae_tendsto_cubeProjection_of_integrableOn Q f hint
    simpa [normalizedCubeMeasure, cubeMeasure] using
      Measure.ae_smul_measure h (ENNReal.ofReal ((cubeVolume Q)⁻¹))
  have hfatou : ∫⁻ x, ENNReal.ofReal (f x * f x) ∂normalizedCubeMeasure Q ≤
      Filter.liminf (fun N => ∫⁻ x, ENNReal.ofReal (cubeProjection Q N f x *
        cubeProjection Q N f x) ∂normalizedCubeMeasure Q) Filter.atTop := by
    calc ∫⁻ x, ENNReal.ofReal (f x * f x) ∂normalizedCubeMeasure Q =
        ∫⁻ x, Filter.liminf (fun N => ENNReal.ofReal (cubeProjection Q N f x *
          cubeProjection Q N f x)) Filter.atTop ∂normalizedCubeMeasure Q := by
          refine lintegral_congr_ae (hae.mono fun x hx => ?_)
          exact ((ENNReal.tendsto_ofReal (hx.mul hx)).liminf_eq).symm
      _ ≤ _ := lintegral_liminf_le' fun N =>
          (ENNReal.measurable_ofReal.comp_aemeasurable
            ((Haar.projection_memLp Q N f 2).aestronglyMeasurable.aemeasurable.mul
              (Haar.projection_memLp Q N f 2).aestronglyMeasurable.aemeasurable))
  have hle : Haar.energy Q f ≤ A := by
    have h1 : ENNReal.ofReal (Haar.energy Q f) ≤ ENNReal.ofReal A := by
      rw [ofReal_energy_eq_lintegral Q hf]
      refine hfatou.trans (Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall
        fun N => ?_))
      rw [← ofReal_energy_eq_lintegral Q (Haar.projection_memLp Q N f 2)]
      exact ENNReal.ofReal_le_ofReal (le_ciSup ⟨Haar.energy Q f, fun _ ⟨M, hM⟩ => hM ▸ hbdd M⟩ N)
    exact (ENNReal.ofReal_le_ofReal_iff hA0).mp h1
  have hAeq : A = Haar.energy Q f := le_antisymm hAle hle
  have heq : (fun N => Haar.energy Q (fun x => f x - cubeProjection Q N f x)) =
      fun N => Haar.energy Q f - a N := by
    funext N
    exact Haar.energy_residual Q N hf
  rw [heq]
  have := hlim.const_sub (Haar.energy Q f)
  rwa [hAeq, sub_self] at this

end GMCExplicitDelta.Localization
