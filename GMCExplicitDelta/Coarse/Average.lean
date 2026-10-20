module

public import Homogenization.Book.Ch02.Theorems

/-!
# Averages over a `Domain`: elementary calculus

Linearity, monotonicity and a.e.-congruence for `Homogenization.Book.Ch02.average`, and the
integrability of pairings of `L²` fields on `U`.
-/

@[expose] public section

open Homogenization.Book.Ch02
open Homogenization (Vec Mat vecDot vecNormSq matVecMul matTranspose symmPart MatLoewnerLE
  scalarMatrix volumeMeasureOn MemVectorL2 GradMemL2On H1Function restrictCoeffField
  vecNormSq_nonneg vecNormSq_eq_zero)
open Matrix
open MeasureTheory hiding average

namespace GMCExplicitDelta.Coarse

variable {d : ℕ} {U : Domain d}

theorem average_congr_ae {f g : Vec d → ℝ}
    (h : f =ᵐ[volumeMeasureOn (U : Set (Vec d))] g) : average U f = average U g := by
  unfold average
  rw [integral_congr_ae h]

theorem volume_toReal_pos' (U : Domain d) : 0 < (volume (U : Set (Vec d))).toReal := by
  refine ENNReal.toReal_pos ?_ ?_
  · exact (U.isOpen.measure_pos volume U.nonempty).ne'
  · exact U.isBoundedDomain.isBounded.measure_lt_top.ne

theorem average_const (U : Domain d) (c : ℝ) : average U (fun _ => c) = c := by
  have hv := (volume_toReal_pos' U).ne'
  unfold average
  rw [setIntegral_const]
  simp only [Measure.real, smul_eq_mul]
  field_simp

theorem average_add_sub {f g : Vec d → ℝ}
    (hf : Integrable f (volumeMeasureOn (U : Set (Vec d))))
    (hg : Integrable g (volumeMeasureOn (U : Set (Vec d)))) :
    average U (fun x => (f x + g x) / 2 - 1) =
      (average U f + average U g) / 2 - 1 := by
  have hv := (volume_toReal_pos' U).ne'
  have h1 : ∫ x in (U : Set (Vec d)), ((f x + g x) / 2 - 1) ∂volume =
      (∫ x in (U : Set (Vec d)), f x ∂volume + ∫ x in (U : Set (Vec d)), g x ∂volume) / 2
        - (volume (U : Set (Vec d))).toReal := by
    have hc : Integrable (fun _ : Vec d => (1 : ℝ)) (volumeMeasureOn (U : Set (Vec d))) :=
      integrable_const 1
    have hfg : Integrable (fun x => (f x + g x) / 2) (volumeMeasureOn (U : Set (Vec d))) :=
      (hf.add hg).div_const 2
    rw [integral_sub hfg hc, integral_div, integral_add hf hg]
    simp [Measure.real]
  unfold average
  rw [h1]
  field_simp

theorem average_sub' {f g : Vec d → ℝ}
    (hf : Integrable f (volumeMeasureOn (U : Set (Vec d))))
    (hg : Integrable g (volumeMeasureOn (U : Set (Vec d)))) :
    average U (fun x => f x - g x) = average U f - average U g := by
  unfold average
  rw [integral_sub hf hg]; ring

theorem average_add' {f g : Vec d → ℝ}
    (hf : Integrable f (volumeMeasureOn (U : Set (Vec d))))
    (hg : Integrable g (volumeMeasureOn (U : Set (Vec d)))) :
    average U (fun x => f x + g x) = average U f + average U g := by
  unfold average
  rw [integral_add hf hg]; ring

theorem average_neg' (f : Vec d → ℝ) : average U (fun x => -f x) = -average U f := by
  unfold average
  rw [integral_neg]; ring

theorem average_const_mul' (c : ℝ) (f : Vec d → ℝ) :
    average U (fun x => c * f x) = c * average U f := by
  unfold average
  rw [integral_const_mul]; ring

theorem average_nonneg' {f : Vec d → ℝ} (h : 0 ≤ᵐ[volumeMeasureOn (U : Set (Vec d))] f) :
    0 ≤ average U f := by
  unfold average
  exact mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg) (integral_nonneg_of_ae h)

theorem average_mono' {f g : Vec d → ℝ}
    (hf : Integrable f (volumeMeasureOn (U : Set (Vec d))))
    (hg : Integrable g (volumeMeasureOn (U : Set (Vec d))))
    (h : f ≤ᵐ[volumeMeasureOn (U : Set (Vec d))] g) : average U f ≤ average U g := by
  unfold average
  exact mul_le_mul_of_nonneg_left (integral_mono_ae hf hg h)
    (inv_nonneg.mpr ENNReal.toReal_nonneg)

theorem integrable_dot {g F : Vec d → Vec d} (hg : GradMemL2On (U : Set (Vec d)) g)
    (hF : MemVectorL2 (U : Set (Vec d)) F) :
    Integrable (fun x => vecDot (g x) (F x)) (volumeMeasureOn (U : Set (Vec d))) := by
  unfold vecDot
  refine integrable_finsetSum _ (fun i _ => ?_)
  exact MemLp.integrable_mul (p := 2) (q := 2) (hg i) (hF.eval i)

theorem integrable_dot_grad {g h : Vec d → Vec d} (hg : GradMemL2On (U : Set (Vec d)) g)
    (hh : GradMemL2On (U : Set (Vec d)) h) :
    Integrable (fun x => vecDot (g x) (h x)) (volumeMeasureOn (U : Set (Vec d))) := by
  unfold vecDot
  refine integrable_finsetSum _ (fun i _ => ?_)
  exact MemLp.integrable_mul (p := 2) (q := 2) (hg i) (hh i)

theorem integrable_comp {F : Vec d → Vec d} (hF : MemVectorL2 (U : Set (Vec d)) F) (i : Fin d) :
    Integrable (fun x => F x i) (volumeMeasureOn (U : Set (Vec d))) :=
  (hF.eval i).integrable one_le_two

theorem integrable_grad_comp {g : Vec d → Vec d} (hg : GradMemL2On (U : Set (Vec d)) g)
    (i : Fin d) : Integrable (fun x => g x i) (volumeMeasureOn (U : Set (Vec d))) :=
  (hg i).integrable one_le_two

theorem average_vecDot_const (e : Vec d) {F : Vec d → Vec d}
    (hF : ∀ i, Integrable (fun x => F x i) (volumeMeasureOn (U : Set (Vec d)))) :
    average U (fun x => vecDot e (F x)) = vecDot e (averageVec U F) := by
  unfold averageVec vecDot
  unfold average
  rw [integral_finsetSum _ (fun i _ => (hF i).const_mul (e i)), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_const_mul]; ring

theorem integrable_vecDot_const (e : Vec d) {F : Vec d → Vec d}
    (hF : ∀ i, Integrable (fun x => F x i) (volumeMeasureOn (U : Set (Vec d)))) :
    Integrable (fun x => vecDot e (F x)) (volumeMeasureOn (U : Set (Vec d))) := by
  unfold vecDot
  exact integrable_finsetSum _ (fun i _ => (hF i).const_mul (e i))

end GMCExplicitDelta.Coarse
