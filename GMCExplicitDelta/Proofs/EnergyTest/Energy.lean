module

public import GMCExplicitDelta.Proofs.EnergyTest.Centered
public import GMCExplicitDelta.Proofs.EnergyTest.CutoffBoundary
public import GMCExplicitDelta.Localization.L3Basic

/-! The harmonic identity for the literal frozen maximizer and cutoff. -/

@[expose] public section

open Homogenization Homogenization.Book MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab (ahom)
open scoped ENNReal

namespace GMCExplicitDelta.Localization.EnergyTest

open Assembly
variable {d : ℕ}

theorem frozenFlux_memL2 (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (U : Ch02.Domain d) (p q : Vec d) (ω : SubdiffusiveProcess.Model.PotentialSample d)
    (i : Fin d) : MemL2On (U : Set (Vec d)) (fun x => frozenFlux M L U p q ω x i) := by
  have hh := memLp_aCutoff_mul M L ω U.measurableSet U.isDomain.isBoundedDomain.isBounded
    (((frozenH1 M L U p q ω).gradMemL2 i).const_mul (ahom M L)⁻¹)
  refine MemLp.ae_eq (Filter.Eventually.of_forall fun x => ?_) hh
  change SubdiffusiveProcess.Model.aCutoff M L ω x * ((ahom M L)⁻¹ * (frozenH1 M L U p q ω).grad x i) =
    (SubdiffusiveProcess.Model.aCutoff M L ω x / ahom M L) * (frozenH1 M L U p q ω).grad x i
  ring

/-- The localized test field is square integrable componentwise. -/
theorem locTestField_memL2 (row : Contract.Row d) (hO : row.Obligations)
    (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) (p q : Vec d)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) (i : Fin d) :
    MemL2On ((cubeAt 0 n : Ch02.Domain d) : Set (Vec d))
      (fun x => locTestField row n (frozenH1 M L (cubeAt 0 n) p q ω).toFun x i) := by
  let U := cubeAt (d := d) 0 n
  let v := frozenH1 M L U p q ω
  let w := subtractConstantH1 U.isDomain v (cubeAverage (originCube d (n : ℤ)) v.toFun)
  have hc : Continuous (fun x => cubeCutoffGrad row n x i) :=
    (((cubeCutoff_contDiff row hO n).continuous_fderiv (by norm_num)).clm_apply
      (continuous_const (y := basisVec i))).congr (fun x => cubeCutoff_fderiv row hO n x i)
  have hh := continuous_mul_memL2 U.isDomain w.memL2 hc
  refine MemLp.ae_eq (Filter.Eventually.of_forall fun x => ?_) hh
  simp only [w, subtractConstantH1_toFun, locTestField, Pi.smul_apply, smul_eq_mul]
  exact mul_comm _ _

/-- Harmonic testing yields the signed pairing identity before Haar duality. -/
theorem locEnergy_eq_neg_pairing (row : Contract.Row d) (hO : row.Obligations)
    (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) (p q : Vec d)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    locEnergy row M L n p q ω = -cubeAverage (originCube d (n : ℤ))
      (fun x => vecDot (frozenFlux M L (cubeAt 0 n) p q ω x)
        (locTestField row n (frozenH1 M L (cubeAt 0 n) p q ω).toFun x)) := by
  let Q := originCube d (n : ℤ)
  let D := cubeAt (d := d) 0 n
  let U : Set (Vec d) := D
  let v := frozenH1 M L D p q ω
  let F := frozenFlux M L D p q ω
  let w := subtractConstantH1 D.isDomain v (cubeAverage Q v.toFun)
  have hUQ : U = openCubeSet Q := cellAt_zero_coe Q
  have hFL i : MemL2On U (fun x => F x i) := frozenFlux_memL2 M L D p q ω i
  have hG i : MemL2On U (fun x => locTestField row n v.toFun x i) :=
    locTestField_memL2 row hO M L n p q ω i
  have hz := boundary_c1_test D.isDomain (frozenFlux_isSolenoidal M L D p q ω) hFL w
    (cubeCutoff_contDiff row hO n)
    (fun x hx => by
      change x ∈ U at hx
      rw [hUQ] at hx
      exact cubeCutoff_pos row hO n hx)
    (fun x hx hxU => by
      change x ∈ closure U at hx
      change x ∉ U at hxU
      rw [hUQ] at hx hxU
      exact cubeCutoff_boundary_zero row hO n hx hxU)
  have he (x : Vec d) : vecDot (F x)
      (fun i => cubeCutoff row n x * w.grad x i + w.toFun x * (fderiv ℝ (cubeCutoff row n) x) (basisVec i)) =
      cubeCutoff row n x * vecDot (v.grad x) (F x) +
        vecDot (F x) (locTestField row n v.toFun x) := by
    simp only [w, subtractConstantH1_grad, subtractConstantH1_toFun,
      cubeCutoff_fderiv row hO n, locTestField, Pi.smul_apply, smul_eq_mul, vecDot]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hI : Integrable (fun x => cubeCutoff row n x * vecDot (v.grad x) (F x)) (volume.restrict U) := by
    have hs : Integrable (fun x => ∑ i, cubeCutoff row n x * v.grad x i * F x i) (volume.restrict U) :=
      integrable_finsetSum _ (fun i _ =>
        (continuous_mul_memL2 D.isDomain (v.gradMemL2 i) (cubeCutoff_contDiff row hO n).continuous).integrable_mul (hFL i))
    refine hs.congr (Filter.Eventually.of_forall fun x => ?_)
    change (∑ i, cubeCutoff row n x * v.grad x i * F x i) =
      cubeCutoff row n x * (∑ i, v.grad x i * F x i)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hJ : Integrable (fun x => vecDot (F x) (locTestField row n v.toFun x)) (volume.restrict U) :=
    integrable_finsetSum _ (fun i _ => (hFL i).integrable_mul (hG i))
  change (∫ x in U, vecDot (F x) (fun i => cubeCutoff row n x * w.grad x i +
    w.toFun x * (fderiv ℝ (cubeCutoff row n) x) (basisVec i))) = 0 at hz
  simp_rw [he] at hz
  rw [integral_add hI hJ] at hz
  unfold locEnergy
  rw [← average_cellAt_eq_cubeAverage Q, ← average_cellAt_eq_cubeAverage Q]
  unfold Ch02.average
  change (volume U).toReal⁻¹ * (∫ x in U, cubeCutoff row n x * vecDot (v.grad x) (F x)) =
    -((volume U).toReal⁻¹ * ∫ x in U, vecDot (F x) (locTestField row n v.toFun x))
  rw [eq_neg_of_add_eq_zero_left hz]
  ring

end GMCExplicitDelta.Localization.EnergyTest
