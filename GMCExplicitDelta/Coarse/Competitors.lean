module

public import GMCExplicitDelta.Coarse.Symmetric
public import GMCExplicitDelta.Coarse.Average

/-!
# C12: old competitors, identities for the maximizers `v_e`, `u_e`

For a coefficient `a` symmetric a.e., a unit vector `e`, `v` a response maximizer for `(e,0)` and
`u` a response maximizer for `(0,e)`:

* `average_cross`: `avg_U ∇u · a ∇v = -1`;
* `average_energy_v`: `avg_U ∇v · a ∇v = e·X_U e`;
* `average_energy_u`: `avg_U ∇u · a ∇u = e·Y_U e`;
* `half_average_energy_sum`: `½ avg_U (∇v+∇u) · a (∇v+∇u) = J(U,e,e;a)`.

Reused from CoarseGraining: `firstVariationValue_eq_zero`, `responseJ_eq_energy_of_isResponseMaximizer`,
`averageFlux_eq_of_isResponseMaximizer`, `gradient_add_of_isResponseMaximizer`,
`responseMaximizerExists`, `Solution.flux_memVectorL2`.
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

theorem symmPart_of_isSymm {A : Mat d} (h : A.IsSymm) : symmPart A = A := by
  ext i j
  show (A i j + A j i) / 2 = A i j
  rw [h.apply i j]; ring

section Symmetric

variable {a : CoeffOn U} (ha : CoeffOn.IsSymmetric a)
include ha

theorem symmPart_ae : ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)),
    symmPart (a.toCoeffField x) = a.toCoeffField x :=
  ha.mono fun _ hx => symmPart_of_isSymm hx

theorem variationEnergyValue_eq_average (w : Solution U a) :
    variationEnergyValue U a w =
      average U (fun x => vecDot (w.toH1.grad x) (matVecMul (a.toCoeffField x) (w.toH1.grad x))) := by
  unfold variationEnergyValue variationEnergyIntegrand average
  congr 1
  refine integral_congr_ae ((symmPart_ae ha).mono fun x hx => ?_)
  simp only [hx]

/-- C12: `avg_U ∇v · a ∇v = e·X_U e` for the maximizer `v` of `(e,0)`. -/
theorem average_energy_v {v : Solution U a} {e : Vec d} (hv : IsResponseMaximizer U a e 0 v) :
    average U (fun x => vecDot (v.toH1.grad x) (matVecMul (a.toCoeffField x) (v.toH1.grad x))) =
      qf (XU U a) e := by
  have h1 := responseJ_eq_energy_of_isResponseMaximizer hv
  rw [variationEnergyValue_eq_average ha, responseJ_eq_XY ha] at h1
  simp [qf] at h1
  have hq : qf (XU U a) e = e ⬝ᵥ XU U a *ᵥ e := rfl
  rw [hq]
  linarith

/-- C12: `avg_U ∇u · a ∇u = e·Y_U e` for the maximizer `u` of `(0,e)`. -/
theorem average_energy_u {u : Solution U a} {e : Vec d} (hu : IsResponseMaximizer U a 0 e u) :
    average U (fun x => vecDot (u.toH1.grad x) (matVecMul (a.toCoeffField x) (u.toH1.grad x))) =
      qf (YU U a) e := by
  have h1 := responseJ_eq_energy_of_isResponseMaximizer hu
  rw [variationEnergyValue_eq_average ha, responseJ_eq_XY ha] at h1
  simp [qf] at h1
  have hq : qf (YU U a) e = e ⬝ᵥ YU U a *ᵥ e := rfl
  rw [hq]
  linarith

/-- C12: `avg_U ∇u · a ∇v = -1`. -/
theorem average_cross {v u : Solution U a} {e : Vec d} (he : e ⬝ᵥ e = 1)
    (hv : IsResponseMaximizer U a e 0 v) (hu : IsResponseMaximizer U a 0 e u) :
    average U (fun x => vecDot (u.toH1.grad x) (matVecMul (a.toCoeffField x) (v.toH1.grad x))) =
      -1 := by
  have hFV := firstVariationValue_eq_zero hv u
  unfold firstVariationValue at hFV
  have hflux : averageFlux U a u = e := by
    have h := averageFlux_eq_of_isResponseMaximizer hu
    have hk : kappaCoarse U a = 0 := kappa_eq_zero ha
    rw [hk] at h
    have z1 : ∀ x : Vec d, matVecMul (0 : Mat d) x = 0 := fun x => by ext i; simp [matVecMul]
    have z2 : ∀ A : Mat d, matVecMul A (0 : Vec d) = 0 := fun A => by ext i; simp [matVecMul]
    have z3 : matTranspose (0 : Mat d) = 0 := by ext i j; simp [matTranspose]
    rw [z3, z1, z2] at h
    simpa using h
  have hI1 : Integrable (fun x => vecDot e (matVecMul (a.toCoeffField x) (u.toH1.grad x)))
      (volumeMeasureOn (U : Set (Vec d))) :=
    integrable_vecDot_const e (integrable_comp (Solution.flux_memVectorL2 u))
  have hI2 : Integrable (fun x => vecDot (u.toH1.grad x)
      (matVecMul (a.toCoeffField x) (v.toH1.grad x))) (volumeMeasureOn (U : Set (Vec d))) :=
    integrable_dot u.toH1.gradMemL2 (Solution.flux_memVectorL2 v)
  have e1 : firstVariationIntegrand U a e 0 v u =ᵐ[volumeMeasureOn (U : Set (Vec d))] fun x =>
      -(vecDot e (matVecMul (a.toCoeffField x) (u.toH1.grad x))) -
        vecDot (u.toH1.grad x) (matVecMul (a.toCoeffField x) (v.toH1.grad x)) :=
    (symmPart_ae ha).mono fun x hx => by
      simp [firstVariationIntegrand, hx, vecDot]
  have hI1' : Integrable (fun x => -vecDot e (matVecMul (a.toCoeffField x) (u.toH1.grad x)))
      (volumeMeasureOn (U : Set (Vec d))) := hI1.neg
  rw [average_congr_ae e1, average_sub' hI1' hI2, average_neg',
    average_vecDot_const e (integrable_comp (Solution.flux_memVectorL2 u))] at hFV
  have h3 : vecDot e (averageVec U fun x => matVecMul (a.toCoeffField x) (u.toH1.grad x)) = 1 := by
    have : averageVec U (fun x => matVecMul (a.toCoeffField x) (u.toH1.grad x)) = e := hflux
    rw [this]; exact he
  rw [h3] at hFV
  linarith

/-- C12: `½ avg_U (∇v+∇u) · a (∇v+∇u) = J(U,e,e;a)`. -/
theorem half_average_energy_sum {v u : Solution U a} {e : Vec d}
    (hv : IsResponseMaximizer U a e 0 v) (hu : IsResponseMaximizer U a 0 e u) :
    (1 / 2) * average U (fun x => vecDot (v.toH1.grad x + u.toH1.grad x)
        (matVecMul (a.toCoeffField x) (v.toH1.grad x + u.toH1.grad x))) =
      responseJ U a e e := by
  obtain ⟨v12, -, h12⟩ := responseMaximizerExists U a e e
  have h12' : IsResponseMaximizer U a (e + 0) (0 + e) v12 := by simpa using h12
  have hgrad := gradient_add_of_isResponseMaximizer h12' hv hu
  have h1 := responseJ_eq_energy_of_isResponseMaximizer h12
  rw [variationEnergyValue_eq_average ha] at h1
  rw [h1]
  congr 1
  refine (average_congr_ae ?_).symm
  exact hgrad.mono fun x hx => by simp only [hx]

end Symmetric

end GMCExplicitDelta.Coarse
