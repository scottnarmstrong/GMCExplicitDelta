module
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.CompactOpen

/-!
# Explicit cutoff-uniform coarse-graining cascade in dimensions two, three and four

Mathlib-only statement of the three main theorems of the library,
`GMCExplicitDelta.explicit_cascade_two`, `GMCExplicitDelta.explicit_cascade_three` and
`GMCExplicitDelta.explicit_cascade_four`. For `d ∈ {2, 3, 4}` and the explicit thresholds
`δ₀(2) = .36665`, `δ₀(3) = .18870`, `δ₀(4) = .15698`: for every model `M : GMCModel d` of
disorder `δ ≤ δ₀(d)`, every cutoff `m`, every cube `z + 𝒞ₙ = z + (−3ⁿ/2, 3ⁿ/2)ᵈ` with `n ≥ m` and
every Euclidean unit vector `e`,

* the normalized defect `J^max_m(z + 𝒞ₙ) = sup_{|e| = 1} J(z + 𝒞ₙ, ā_m^{-1/2} e, ā_m^{1/2} e; a_m)`
  and the directional response `J(z + 𝒞ₙ, ā_m^{-1/2} e, ā_m^{1/2} e; a_m)` are measurable
  functions of the environment;
* `‖J^max_m(z + 𝒞ₙ)‖_{L^32} ≤ C₃₂(d) δ²` and
  `E J(z + 𝒞ₙ, ā_m^{-1/2} e, ā_m^{1/2} e; a_m) ≤ C_mean(d) δ²`, with
  `C₃₂(2) = 23138371504/53772889`, `C_mean(2) = 230590996/53772889`,
  `C₃₂(3) = 89475125/1186923`, `C_mean(3) = 17849411/3560769`,
  `C₃₂(4) = 5918767600/61606801`, `C_mean(4) = 423596800/61606801`.

A model `M : GMCModel d` consists of independent layers `g_0, g_1, …` with `g_k` distributed as
`g_0(3^{−k}·)` and the assumptions (g1)–(g4), in dimension `d ≥ 2` and with disorder
`δ ∈ (0, 1/2]`; `a_m = exp(Σ_{k ≤ m} (g_k − τ²))` with `τ² = log E exp(g_0(0))`; `ā_m` (`ahom M m`)
is the effective diffusivity of `a_m`.

## Vocabulary

* `J(U, p, q; a) = sup_v ⨍_U (−½ ∇v·(sym a)∇v − p·a∇v + q·∇v)`, the supremum over the
  `a`-harmonic functions `v ∈ H¹(U)` (weak gradient fields of `H¹(U)` functions whose flux `a∇v`
  is orthogonal to `∇φ` for every `φ ∈ H¹₀(U)`), with `sym a = (a + aᵀ)/2` and `⨍_U` the
  volume-normalized integral.
* `ā_m` is the infimum over cube scales `n` of `(1/d) Σᵢ E[eᵢ·a_m(𝒞ₙ)eᵢ]`, where
  `eᵢ·a_m(𝒞ₙ)eᵢ = inf_{w ∈ H¹₀(𝒞ₙ)} ⨍_{𝒞ₙ} a_m |eᵢ + ∇w|²` is the cell-problem energy (the
  variational formula for the coarse-grained matrix of a symmetric coefficient). The values are
  nonincreasing in `n` (subadditivity), so the infimum is the limit over `n`.
* `‖X‖_{L^ξ} = (∫ X^ξ dP)^{1/ξ}` for an `[0, ∞]`-valued random variable `X`.
* `H¹(U)` is given by explicit witnesses: a function, a weak gradient, the `L²(U)` bounds and the
  integration-by-parts identities against smooth compactly supported test functions in `U`.
  `H¹₀(U)` adds an approximating sequence of smooth compactly supported functions in `U`
  converging in `H¹(U)`.

## How this differs from the encoding of the library

1. In the library `J` takes a domain packaged with the proof that it is a nonempty bounded open
   convex set, and a coefficient packaged with ellipticity bounds (chosen by `Classical.choice`
   for `a_m`). The value of `J` depends only on the set and on the coefficient field, so the
   challenge passes the translated open cube `z + 𝒞ₙ` as a set and `a_m` as the matrix field
   `x ↦ a_m(x) I`.
2. The library defines `ā_m` through the coarse-grained matrix `a(𝒞ₙ)`; the challenge writes its
   diagonal entries through the cell-problem formula above, as in the dependency's own
   Mathlib-only statement of Theorem B.

Only Mathlib is imported. The sole intentional `sorry` is the proof of the final theorem; the
separate Solution proves the same statement from the library.
-/

@[expose] public section
namespace GMCExplicitDeltaAudit
set_option autoImplicit false
set_option warn.classDefReducibility false
noncomputable section
open scoped BigOperators
namespace Homogenization
/-- The coordinate space ℝᵈ, with its sup-norm topology. -/
abbrev Vec (d : ℕ) :=
  Fin d → ℝ
/-- Real d-by-d matrices acting on the coordinate space. -/
abbrev Mat (d : ℕ) :=
  Matrix (Fin d) (Fin d) ℝ
/-- The Euclidean scalar product, expressed as a sum over coordinates. -/
def vecDot {d : ℕ} (x y : Homogenization.Vec d) : ℝ :=
  ∑ i, x i * y i
/-- The squared Euclidean norm. -/
def vecNormSq {d : ℕ} (x : Homogenization.Vec d) : ℝ :=
  vecDot x x
/-- Matrix multiplication of a coordinate vector. -/
def matVecMul {d : ℕ} (A : Mat d) (x : Homogenization.Vec d) : Homogenization.Vec d := fun i =>
  ∑ j, A i j * x j
/-- The Euclidean norm, as the square root of the scalar product. -/
noncomputable def euclideanNorm {d : ℕ} (x : Homogenization.Vec d) : ℝ :=
  Real.sqrt (vecNormSq x)
/-- The symmetric part `(A + Aᵀ)/2` of a matrix. -/
noncomputable def symmPart {d : ℕ} (A : Mat d) : Mat d :=
  fun i j => (A i j + A j i) / 2
end Homogenization
open _root_.GMCExplicitDeltaAudit.Homogenization Topology
/-- A scalar field with a continuous derivative and locally Lipschitz derivative. -/
def SubdiffusiveProcess.Model.PotentialField (d : ℕ) :=
  { p : C(Homogenization.Vec d, ℝ) × C(Homogenization.Vec d, Homogenization.Vec d →L[ℝ] ℝ) //
    (∀ x, HasFDerivAt p.1 (p.2 x) x) ∧
      ∀ K : Set (Homogenization.Vec d), IsCompact K → ∃ C : NNReal, LipschitzOnWith C p.2 K }
namespace Homogenization
/-- A spatially varying real matrix coefficient. -/
abbrev CoeffField (d : ℕ) :=
  Homogenization.Vec d → Mat d
/-- The scalar multiple of the identity matrix. -/
abbrev scalarMatrix {d : ℕ} (sigma : ℝ) : Mat d :=
  sigma • (1 : Mat d)
open MeasureTheory
/-- A matrix field whose entries are measurable and locally integrable. -/
structure RegCoeffField (d : ℕ) where
  toFun : Homogenization.Vec d → Mat d
  entry_measurable : ∀ i j, Measurable (fun x : Homogenization.Vec d => toFun x i j)
  entry_locInt : ∀ i j, LocallyIntegrable (fun x : Homogenization.Vec d => toFun x i j) volume
namespace RegCoeffField
variable {d : ℕ}
instance : CoeFun (RegCoeffField d) (fun _ => Homogenization.Vec d → Mat d) :=
  ⟨toFun⟩
end RegCoeffField
open MeasureTheory
variable {d : ℕ}
/-- A bounded measurable test function with compact support. -/
structure IsProbeR (φ : Homogenization.Vec d → ℝ) : Prop where
  measurable : Measurable φ
  bounded : ∃ C : ℝ, ∀ x, |φ x| ≤ C
  hasCompactSupport : HasCompactSupport φ
/-- The integral of one matrix entry against a scalar test function. -/
def entryTestR (i j : Fin d) (φ : Homogenization.Vec d → ℝ) (a : RegCoeffField d) : ℝ :=
  ∫ x, a x i j * φ x ∂volume
/-- The local coefficient σ-algebra generated by entry integrals against supported
probes. -/
def LocalSigmaR (U : Set (Homogenization.Vec d)) : MeasurableSpace (RegCoeffField d) :=
  MeasurableSpace.generateFrom
    {s |
      ∃ (i j : Fin d) (φ : Homogenization.Vec d → ℝ),
        IsProbeR φ ∧
          Function.support φ ⊆ U ∧ ∃ t : Set ℝ, MeasurableSet t ∧ s = entryTestR i j φ ⁻¹' t}
end Homogenization
namespace SubdiffusiveProcess.Model
open _root_.GMCExplicitDeltaAudit.Homogenization MeasureTheory Topology
noncomputable instance potentialFieldTopologicalSpace (d : ℕ) :
    TopologicalSpace (PotentialField d) :=
  TopologicalSpace.induced Subtype.val inferInstance
noncomputable instance potentialFieldMeasurableSpace (d : ℕ) : MeasurableSpace (PotentialField d) :=
  borel (PotentialField d)
namespace PotentialField
variable {d : ℕ}
instance : CoeFun (PotentialField d) (fun _ ↦ Homogenization.Vec d → ℝ) :=
  ⟨fun g ↦ g.1.1⟩
/-- The continuous derivative stored with a potential field. -/
def deriv (g : PotentialField d) : C(Homogenization.Vec d, Homogenization.Vec d →L[ℝ] ℝ) :=
  g.1.2
theorem hasFDerivAt (g : PotentialField d) (x : Homogenization.Vec d) :
    HasFDerivAt g (deriv g x) x :=
  g.2.1 x
theorem forgetPotential_entry_measurable (g : PotentialField d) (i k : Fin d) :
    Measurable (fun x : Homogenization.Vec d ↦ scalarMatrix (d := d) (g x) i k) := by
  have hmat : Continuous (fun x : Homogenization.Vec d ↦ scalarMatrix (d := d) (g x)) :=
    g.1.1.continuous.smul continuous_const
  exact ((continuous_apply k).comp ((continuous_apply i).comp hmat)).measurable
theorem forgetPotential_entry_locInt (g : PotentialField d) (i k : Fin d) :
    LocallyIntegrable (fun x : Homogenization.Vec d ↦ scalarMatrix (d := d) (g x) i k) volume := by
  have hmat : Continuous (fun x : Homogenization.Vec d ↦ scalarMatrix (d := d) (g x)) :=
    g.1.1.continuous.smul continuous_const
  exact ((continuous_apply k).comp ((continuous_apply i).comp hmat)).locallyIntegrable
/-- The regular matrix field g(x)·Id obtained by forgetting the derivative data of
a scalar potential. -/
def forgetPotential (g : PotentialField d) : RegCoeffField d
    where
  toFun x := scalarMatrix (d := d) (g x)
  entry_measurable := forgetPotential_entry_measurable g
  entry_locInt := forgetPotential_entry_locInt g
end PotentialField
end SubdiffusiveProcess.Model
namespace Homogenization
/-- An orthogonal coordinate permutation with independently chosen coordinate
signs. -/
def IsSignedPermutationMatrix {d : ℕ} (R : Mat d) : Prop :=
  ∃ σ : Equiv.Perm (Fin d),
    ∃ s : Fin d → ℝ, (∀ i, s i = 1 ∨ s i = -1) ∧ ∀ i j, R i j = if i = σ j then s j else 0
end Homogenization
namespace SubdiffusiveProcess.Model.PotentialField
variable {d : ℕ}
/-- Multiplication by a scalar, as a continuous map on potential values. -/
def valueScaleMap (c : ℝ) : C(ℝ, ℝ) :=
  ⟨fun y ↦ c * y, continuous_const.mul continuous_id⟩
/-- Multiplication by a scalar on the space of derivative linear maps. -/
def derivScaleCLM (c : ℝ) : (Homogenization.Vec d →L[ℝ] ℝ) →L[ℝ] (Homogenization.Vec d →L[ℝ] ℝ) :=
  c • ContinuousLinearMap.id ℝ (Homogenization.Vec d →L[ℝ] ℝ)
/-- The continuous-map form of scalar multiplication on derivatives. -/
def derivScaleMap (c : ℝ) : C(Homogenization.Vec d →L[ℝ] ℝ, Homogenization.Vec d →L[ℝ] ℝ) :=
  ⟨derivScaleCLM c, (derivScaleCLM c).continuous⟩
/-- Scalar multiplication of a field and its derivative before restricting to
regular fields. -/
def scaleAmbient (c : ℝ) :
    (C(Homogenization.Vec d, ℝ) × C(Homogenization.Vec d, Homogenization.Vec d →L[ℝ] ℝ)) →
      C(Homogenization.Vec d, ℝ) × C(Homogenization.Vec d, Homogenization.Vec d →L[ℝ] ℝ) :=
  fun p ↦ ((valueScaleMap c).comp p.1, (derivScaleMap c).comp p.2)
theorem scaleAmbient_regular (c : ℝ) (g : PotentialField d) :
    (∀ x, HasFDerivAt (scaleAmbient c g.1).1 ((scaleAmbient c g.1).2 x) x) ∧
      ∀ K : Set (Homogenization.Vec d), IsCompact K →
        ∃ C : NNReal, LipschitzOnWith C (scaleAmbient c g.1).2 K := by
  constructor
  · intro x
    simpa only [scaleAmbient, valueScaleMap, derivScaleMap, derivScaleCLM,
      ContinuousMap.comp_apply, ContinuousMap.coe_comp, ContinuousMap.coe_mk, deriv,
      ContinuousLinearMap.comp_id, id_eq, smul_apply, ContinuousLinearMap.id_apply] using!
      (g.hasFDerivAt x).const_smul c
  · intro K hK
    obtain ⟨C, hC⟩ := g.2.2 K hK
    refine ⟨‖derivScaleCLM (d := d) c‖₊ * C, ?_⟩
    simpa only [scaleAmbient, derivScaleMap, ContinuousMap.comp_apply, ContinuousMap.coe_comp,
      ContinuousMap.coe_mk, deriv, ContinuousLinearMap.comp_id, id_eq, smul_apply,
      ContinuousLinearMap.id_apply, Function.comp_def] using!
      (derivScaleCLM (d := d) c).lipschitzWith.comp_lipschitzOnWith hC
/-- Scalar multiplication of a regular potential field. -/
def scale (c : ℝ) (g : PotentialField d) : PotentialField d :=
  ⟨scaleAmbient c g.1, scaleAmbient_regular c g⟩
/-- The continuous spatial translation used to pull back a field. -/
def translateMap (z : Homogenization.Vec d) : C(Homogenization.Vec d, Homogenization.Vec d) :=
  ⟨fun x ↦ x + z, continuous_id.add continuous_const⟩
/-- Translation of a field together with its derivative. -/
def translateAmbient (z : Homogenization.Vec d) :
    (C(Homogenization.Vec d, ℝ) × C(Homogenization.Vec d, Homogenization.Vec d →L[ℝ] ℝ)) →
      C(Homogenization.Vec d, ℝ) × C(Homogenization.Vec d, Homogenization.Vec d →L[ℝ] ℝ) :=
  fun p ↦ (p.1.comp (translateMap z), p.2.comp (translateMap z))
theorem translateAmbient_regular (z : Homogenization.Vec d) (g : PotentialField d) :
    (∀ x, HasFDerivAt (translateAmbient z g.1).1 ((translateAmbient z g.1).2 x) x) ∧
      ∀ K : Set (Homogenization.Vec d), IsCompact K →
        ∃ C : NNReal, LipschitzOnWith C (translateAmbient z g.1).2 K := by
  constructor
  · intro x
    simpa only [translateAmbient, translateMap, ContinuousMap.comp_apply, ContinuousMap.coe_comp,
      ContinuousMap.coe_mk, deriv, ContinuousLinearMap.comp_id, id_eq, smul_apply,
      ContinuousLinearMap.id_apply, Function.comp_def] using!
      (g.hasFDerivAt (x + z)).comp x ((hasFDerivAt_id x).add_const z)
  · intro K hK
    let T : Homogenization.Vec d → Homogenization.Vec d := fun x ↦ x + z
    obtain ⟨C, hC⟩ := g.2.2 (T '' K) (hK.image (isometry_add_right z).continuous)
    refine ⟨C, ?_⟩
    simpa only [translateAmbient, translateMap, ContinuousMap.comp_apply, ContinuousMap.coe_comp,
      ContinuousMap.coe_mk, deriv, ContinuousLinearMap.comp_id, id_eq, smul_apply,
      ContinuousLinearMap.id_apply, Function.comp_def, T, mul_one] using!
      hC.comp (isometry_add_right z).lipschitzWith.lipschitzOnWith (Set.mapsTo_image T K)
/-- Translation of a regular potential field. -/
def translate (z : Homogenization.Vec d) (g : PotentialField d) : PotentialField d :=
  ⟨translateAmbient z g.1, translateAmbient_regular z g⟩
/-- The continuous linear spatial dilation x ↦ r x. -/
def spatialCLM (r : ℝ) : Homogenization.Vec d →L[ℝ] Homogenization.Vec d :=
  r • ContinuousLinearMap.id ℝ (Homogenization.Vec d)
/-- Spatial dilation regarded as a continuous map. -/
def spatialMap (r : ℝ) : C(Homogenization.Vec d, Homogenization.Vec d) :=
  ⟨spatialCLM r, (spatialCLM r).continuous⟩
/-- Pullback by spatial dilation, including the derivative chain-rule factor. -/
def spatialScaleAmbient (r : ℝ) :
    (C(Homogenization.Vec d, ℝ) × C(Homogenization.Vec d, Homogenization.Vec d →L[ℝ] ℝ)) →
      C(Homogenization.Vec d, ℝ) × C(Homogenization.Vec d, Homogenization.Vec d →L[ℝ] ℝ) :=
  fun p ↦ (p.1.comp (spatialMap r), (derivScaleMap r).comp (p.2.comp (spatialMap r)))
theorem spatialScaleAmbient_regular (r : ℝ) (g : PotentialField d) :
    (∀ x, HasFDerivAt (spatialScaleAmbient r g.1).1 ((spatialScaleAmbient r g.1).2 x) x) ∧
      ∀ K : Set (Homogenization.Vec d), IsCompact K →
        ∃ C : NNReal, LipschitzOnWith C (spatialScaleAmbient r g.1).2 K := by
  constructor
  · intro x
    simpa only [spatialScaleAmbient, spatialMap, spatialCLM, derivScaleMap, derivScaleCLM,
      ContinuousMap.comp_apply, ContinuousMap.coe_comp, ContinuousMap.coe_mk, deriv,
      ContinuousLinearMap.comp_id, id_eq, smul_apply, ContinuousLinearMap.id_apply,
      ContinuousMap.coe_mk, ContinuousMap.coe_comp, ContinuousLinearMap.comp_smul,
      ContinuousLinearMap.comp_id, Function.comp_def] using!
      (g.hasFDerivAt (r • x)).comp x ((hasFDerivAt_id x).const_smul r)
  · intro K hK
    let S : Homogenization.Vec d → Homogenization.Vec d := spatialCLM (d := d) r
    obtain ⟨C, hC⟩ := g.2.2 (S '' K) (hK.image (spatialCLM (d := d) r).continuous)
    have hinner :=
      hC.comp (spatialCLM (d := d) r).lipschitzWith.lipschitzOnWith (Set.mapsTo_image S K)
    refine ⟨‖derivScaleCLM (d := d) r‖₊ * (C * ‖spatialCLM (d := d) r‖₊), ?_⟩
    simpa only [spatialScaleAmbient, spatialMap, derivScaleMap, ContinuousMap.comp_apply,
      ContinuousMap.coe_comp, ContinuousMap.coe_mk, deriv, ContinuousLinearMap.comp_id, id_eq,
      smul_apply, ContinuousLinearMap.id_apply, Function.comp_def, S] using!
      (derivScaleCLM (d := d) r).lipschitzWith.comp_lipschitzOnWith hinner
/-- Spatial dilation of a regular potential field. -/
def spatialScale (r : ℝ) (g : PotentialField d) : PotentialField d :=
  ⟨spatialScaleAmbient r g.1, spatialScaleAmbient_regular r g⟩
/-- Pullback by the inverse triadic dilation x ↦ 3⁻ᵏ x. -/
def triadicScale (k : ℕ) (g : PotentialField d) : PotentialField d :=
  spatialScale (((3 : ℝ) ^ k)⁻¹) g
/-- Negation of a regular potential field. -/
def negate (g : PotentialField d) : PotentialField d :=
  scale (-1) g
/-- Matrix action on vectors as a continuous linear map. -/
def matVecContinuousLinearMap (R : Mat d) : Homogenization.Vec d →L[ℝ] Homogenization.Vec d :=
  ⟨Matrix.toLin' R, (Matrix.toLin' R).continuous_of_finiteDimensional⟩
/-- The derivative transformation under a signed coordinate permutation. -/
def rotateDerivativeMap (R : Mat d) :
    (Homogenization.Vec d →L[ℝ] ℝ) →L[ℝ] (Homogenization.Vec d →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ (Homogenization.Vec d) (Homogenization.Vec d) ℝ).flip
    (matVecContinuousLinearMap R)
/-- The spatial signed-coordinate permutation as a continuous map. -/
def rotateDomainMap (R : Mat d) : C(Homogenization.Vec d, Homogenization.Vec d) :=
  ⟨matVecContinuousLinearMap R, (matVecContinuousLinearMap R).continuous⟩
/-- The continuous-map form of the derivative transformation under rotation. -/
def rotateDerivativeContinuousMap (R : Mat d) :
    C(Homogenization.Vec d →L[ℝ] ℝ, Homogenization.Vec d →L[ℝ] ℝ) :=
  ⟨rotateDerivativeMap R, (rotateDerivativeMap R).continuous⟩
/-- Pullback of a field and its derivative under a signed coordinate permutation. -/
def rotateAmbient (R : Mat d) :
    (C(Homogenization.Vec d, ℝ) × C(Homogenization.Vec d, Homogenization.Vec d →L[ℝ] ℝ)) →
      C(Homogenization.Vec d, ℝ) × C(Homogenization.Vec d, Homogenization.Vec d →L[ℝ] ℝ) :=
  fun p ↦
  (p.1.comp (rotateDomainMap R),
    (rotateDerivativeContinuousMap R).comp (p.2.comp (rotateDomainMap R)))
theorem rotateAmbient_regular (R : Mat d) (g : PotentialField d) :
    (∀ x, HasFDerivAt (rotateAmbient R g.1).1 ((rotateAmbient R g.1).2 x) x) ∧
      ∀ K : Set (Homogenization.Vec d), IsCompact K →
        ∃ C : NNReal, LipschitzOnWith C (rotateAmbient R g.1).2 K := by
  constructor
  · intro x
    simpa only [rotateAmbient, rotateDomainMap, rotateDerivativeContinuousMap,
      ContinuousMap.comp_apply, ContinuousMap.coe_comp, ContinuousMap.coe_mk, deriv,
      ContinuousLinearMap.comp_id, id_eq, smul_apply, ContinuousLinearMap.id_apply,
      rotateDerivativeMap] using!
      (g.hasFDerivAt (matVecMul R x)).comp x (matVecContinuousLinearMap R).hasFDerivAt
  · intro K hK
    let S : Homogenization.Vec d → Homogenization.Vec d := matVecContinuousLinearMap R
    obtain ⟨C, hC⟩ := g.2.2 (S '' K) (hK.image (matVecContinuousLinearMap R).continuous)
    have hinner :=
      hC.comp (matVecContinuousLinearMap R).lipschitzWith.lipschitzOnWith (Set.mapsTo_image S K)
    refine ⟨‖rotateDerivativeMap R‖₊ * (C * ‖matVecContinuousLinearMap R‖₊), ?_⟩
    simpa only [rotateAmbient, rotateDomainMap, rotateDerivativeContinuousMap,
      ContinuousMap.comp_apply, ContinuousMap.coe_comp, ContinuousMap.coe_mk, deriv,
      ContinuousLinearMap.comp_id, id_eq, smul_apply, ContinuousLinearMap.id_apply,
      Function.comp_def, S] using!
      (rotateDerivativeMap R).lipschitzWith.comp_lipschitzOnWith hinner
/-- The regular potential field obtained by a signed coordinate permutation. -/
def rotate (R : Mat d) (_hR : IsSignedPermutationMatrix R) (g : PotentialField d) :
    PotentialField d :=
  ⟨rotateAmbient R g.1, rotateAmbient_regular R g⟩
end SubdiffusiveProcess.Model.PotentialField
/-- A sequence of regular potential layers indexed by nonnegative integers. -/
abbrev SubdiffusiveProcess.Model.PotentialSample (d : ℕ) :=
  ℕ → SubdiffusiveProcess.Model.PotentialField d
open MeasureTheory ProbabilityTheory
/-- The marginal probability law of one potential layer. -/
noncomputable def SubdiffusiveProcess.Model.potentialMarginalLaw {d : ℕ}
    (P : ProbabilityMeasure (SubdiffusiveProcess.Model.PotentialSample d)) (k : ℕ) :
    ProbabilityMeasure (SubdiffusiveProcess.Model.PotentialField d) :=
  P.map (fun omega => omega k)
/-- The probability law of the layer at scale zero. -/
noncomputable def SubdiffusiveProcess.Model.zeroPotentialLaw {d : ℕ}
    (P : ProbabilityMeasure (SubdiffusiveProcess.Model.PotentialSample d)) :
    ProbabilityMeasure (SubdiffusiveProcess.Model.PotentialField d) :=
  SubdiffusiveProcess.Model.potentialMarginalLaw P 0
/-- Dimension and disorder bounds, layer independence and exact triadic marginal
scaling. -/
structure SubdiffusiveProcess.Model.ShellLawPrefix (d : ℕ) (delta : ℝ)
    (P : ProbabilityMeasure (SubdiffusiveProcess.Model.PotentialSample d)) : Prop where
  dimension : 2 ≤ d
  delta_pos : 0 < delta
  delta_le_half : delta ≤ (1 : ℝ) / 2
  independent :
    iIndepFun (fun k : ℕ ↦ fun ω : SubdiffusiveProcess.Model.PotentialSample d ↦ ω k)
      P.toMeasure
  marginal_scaling :
    ∀ k : ℕ,
      SubdiffusiveProcess.Model.potentialMarginalLaw P k =
        (SubdiffusiveProcess.Model.zeroPotentialLaw P).map
          (SubdiffusiveProcess.Model.PotentialField.triadicScale k)
/-- The local σ-algebra generated by supported integral probes of the scalar field
represented as g(x)·Id. -/
def SubdiffusiveProcess.Model.PotentialField.localSigma {d : ℕ}
    (U : Set (Homogenization.Vec d)) :
    MeasurableSpace (SubdiffusiveProcess.Model.PotentialField d) :=
  MeasurableSpace.comap SubdiffusiveProcess.Model.PotentialField.forgetPotential
    (LocalSigmaR U)
/-- Assumption (g1): integrability, mean zero, stationarity and finite-range
independence. -/
structure SubdiffusiveProcess.Model.ShellLawG1 (d : ℕ)
    (P : ProbabilityMeasure (SubdiffusiveProcess.Model.PotentialSample d)) : Prop where
  integrable :
    ∀ x : Homogenization.Vec d,
      Integrable (fun ω : SubdiffusiveProcess.Model.PotentialSample d ↦ ω 0 x)
        P.toMeasure
  mean_zero :
    ∀ x : Homogenization.Vec d,
      ∫ ω : SubdiffusiveProcess.Model.PotentialSample d, ω 0 x ∂P.toMeasure = 0
  stationary :
    ∀ z : Homogenization.Vec d,
      Measure.map (SubdiffusiveProcess.Model.PotentialField.translate z)
          (SubdiffusiveProcess.Model.zeroPotentialLaw P).toMeasure =
        (SubdiffusiveProcess.Model.zeroPotentialLaw P).toMeasure
  range_dependence :
    ∀ (U V : Set (Homogenization.Vec d)),
      MeasurableSet U →
        MeasurableSet V →
          (∀ ⦃x y : Homogenization.Vec d⦄,
              x ∈ U → y ∈ V → Real.sqrt (d : ℝ) ≤ euclideanNorm (x - y)) →
            Indep (SubdiffusiveProcess.Model.PotentialField.localSigma U)
              (SubdiffusiveProcess.Model.PotentialField.localSigma V)
              (SubdiffusiveProcess.Model.zeroPotentialLaw P).toMeasure
namespace Homogenization
/-- A triadic cube specified by its integer scale and lattice center. -/
structure TriadicCube (d : ℕ) where
  scale : ℤ
  index : Fin d → ℤ
/-- The side-length factor 3 to the cube's integer scale. -/
noncomputable def cubeScaleFactor {d : ℕ} (Q : TriadicCube d) : ℝ :=
  (3 : ℝ) ^ Q.scale
/-- The open cube with the specified triadic center and side length. -/
def openCubeSet {d : ℕ} (Q : TriadicCube d) : Set (Homogenization.Vec d) :=
  {x |
    ∀ i,
      (((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q < x i) ∧
        (x i < (((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q))}
/-- The triadic cube centered at the origin at the specified scale. -/
def originCube (d : ℕ) (m : ℤ) : TriadicCube d :=
  { scale := m
    index := 0 }
/-- The translate `z + U = {y + z : y ∈ U}` of a set. -/
def translateSet {d : ℕ} (z : Homogenization.Vec d) (U : Set (Homogenization.Vec d)) :
    Set (Homogenization.Vec d) :=
  { x | ∃ y ∈ U, x = y + z }
end Homogenization
/-- The supremum of the absolute potential on the open unit cube, with zero
included in the supremum set. -/
noncomputable def SubdiffusiveProcess.Model.PotentialField.unitCubeValueNorm {d : ℕ}
    (g : SubdiffusiveProcess.Model.PotentialField d) : ℝ :=
  sSup
    (Set.range fun o : Option { x : Homogenization.Vec d // x ∈ openCubeSet (originCube d 0) } ↦
      match o with
      | none => 0
      | some x => |g x.1|)
/-- The supremum of the derivative operator norm on the open unit cube, with zero
included. -/
noncomputable def SubdiffusiveProcess.Model.PotentialField.unitCubeDerivNorm {d : ℕ}
    (g : SubdiffusiveProcess.Model.PotentialField d) : ℝ :=
  sSup
    (Set.range fun o : Option { x : Homogenization.Vec d // x ∈ openCubeSet (originCube d 0) } ↦
      match o with
      | none => 0
      | some x => ‖SubdiffusiveProcess.Model.PotentialField.deriv g x.1‖)
/-- The Lipschitz seminorm of the derivative on the open unit cube. -/
noncomputable def
  SubdiffusiveProcess.Model.PotentialField.unitCubeDerivLipschitzSeminorm {d : ℕ}
    (g : SubdiffusiveProcess.Model.PotentialField d) : ℝ :=
  sSup
    (Set.range
      fun o :
        Option
          { p :
            ({ x : Homogenization.Vec d // x ∈ openCubeSet (originCube d 0) } ×
              { x : Homogenization.Vec d // x ∈ openCubeSet (originCube d 0) }) //
            p.1 ≠ p.2 } ↦
      match o with
      | none => 0
      | some p =>
        dist (SubdiffusiveProcess.Model.PotentialField.deriv g p.1.1.1)
            (SubdiffusiveProcess.Model.PotentialField.deriv g p.1.2.1) /
          dist p.1.1.1 p.1.2.1)
/-- The sum of the unit-cube value, derivative and derivative-Lipschitz sizes. -/
noncomputable def SubdiffusiveProcess.Model.PotentialField.g2Observable {d : ℕ}
    (g : SubdiffusiveProcess.Model.PotentialField d) : ℝ :=
  SubdiffusiveProcess.Model.PotentialField.unitCubeValueNorm g +
      SubdiffusiveProcess.Model.PotentialField.unitCubeDerivNorm g +
    SubdiffusiveProcess.Model.PotentialField.unitCubeDerivLipschitzSeminorm g
/-- The moment condition `E exp((max(X,0)/A)^σ) ≤ 2`, with the integrand integrable
(`σ = 2` is the sub-Gaussian case). -/
def SubdiffusiveProcess.OGammaLE {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (σ A : ℝ)
    (X : Ω → ℝ) : Prop :=
  Integrable (fun ω ↦ Real.exp ((A⁻¹ * max (X ω) 0) ^ σ)) μ ∧
    ∫ ω, Real.exp ((A⁻¹ * max (X ω) 0) ^ σ) ∂μ ≤ 2
/-- Assumption (g2): the disorder-scaled exponential moment of the unit-cube C¹,¹
size. -/
structure SubdiffusiveProcess.Model.ShellLawG2 (d : ℕ) (delta : ℝ)
    (P : ProbabilityMeasure (SubdiffusiveProcess.Model.PotentialSample d)) : Prop where
  regularity_expectation :
    SubdiffusiveProcess.OGammaLE
      (SubdiffusiveProcess.Model.zeroPotentialLaw P).toMeasure 2 delta
      SubdiffusiveProcess.Model.PotentialField.g2Observable
/-- Assumption (g3): invariance under signed coordinate permutations and field
negation. -/
structure SubdiffusiveProcess.Model.ShellLawG3 (d : ℕ)
    (P : ProbabilityMeasure (SubdiffusiveProcess.Model.PotentialSample d)) : Prop where
  signed_coordinate_permutations :
    ∀ (R : Mat d) (hR : IsSignedPermutationMatrix R),
      (SubdiffusiveProcess.Model.zeroPotentialLaw P).map
          (SubdiffusiveProcess.Model.PotentialField.rotate R hR) =
        SubdiffusiveProcess.Model.zeroPotentialLaw P
  negation :
    (SubdiffusiveProcess.Model.zeroPotentialLaw P).map
        SubdiffusiveProcess.Model.PotentialField.negate =
      SubdiffusiveProcess.Model.zeroPotentialLaw P
/-- The logarithm of the zero-layer exponential moment at the origin, denoted τ²
in the paper. -/
noncomputable def SubdiffusiveProcess.Model.tauSq {d : ℕ}
    (P : ProbabilityMeasure (SubdiffusiveProcess.Model.PotentialSample d)) : ℝ :=
  Real.log
    (∫ g : SubdiffusiveProcess.Model.PotentialField d,
      Real.exp (g 0) ∂(SubdiffusiveProcess.Model.zeroPotentialLaw P).toMeasure)
/-- Assumption (g4): integrability of the exponential at the origin and positivity
of τ². -/
structure SubdiffusiveProcess.Model.ShellLawG4 (d : ℕ)
    (P : ProbabilityMeasure (SubdiffusiveProcess.Model.PotentialSample d)) : Prop where
  exponential_integrable :
    Integrable (fun g : SubdiffusiveProcess.Model.PotentialField d ↦ Real.exp (g 0))
      (SubdiffusiveProcess.Model.zeroPotentialLaw P).toMeasure
  tauSq_pos : 0 < SubdiffusiveProcess.Model.tauSq P
/-- A supplied layer probability law and positive disorder satisfying the standing
assumptions (g1)–(g4). -/
structure SubdiffusiveProcess.Model.GMCModel (d : ℕ) where
  delta : ℝ
  P : ProbabilityMeasure (SubdiffusiveProcess.Model.PotentialSample d)
  shellPrefix : SubdiffusiveProcess.Model.ShellLawPrefix d delta P
  G1 : SubdiffusiveProcess.Model.ShellLawG1 d P
  G2 : SubdiffusiveProcess.Model.ShellLawG2 d delta P
  G3 : SubdiffusiveProcess.Model.ShellLawG3 d P
  G4 : SubdiffusiveProcess.Model.ShellLawG4 d P
/-- The exponential of the layer sum through cutoff L, centered by (L+1)τ². -/
noncomputable def SubdiffusiveProcess.Model.aCutoff {d : ℕ}
    (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) (x : Homogenization.Vec d) : ℝ :=
  Real.exp (∑ k ∈ Finset.range (L + 1), (ω k x - SubdiffusiveProcess.Model.tauSq M.P))
namespace Homogenization
/-- The coordinate basis vector with value one in the specified coordinate. -/
def basisVec {d : ℕ} (i : Fin d) : Homogenization.Vec d :=
  Pi.single i (1 : ℝ)
/-- The distributional integration-by-parts identity for one partial derivative. -/
def HasWeakPartialDerivOn {d : ℕ} (U : Set (Homogenization.Vec d)) (i : Fin d)
    (u gi : Homogenization.Vec d → ℝ) : Prop :=
  ∀ φ : Homogenization.Vec d → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ →
        tsupport φ ⊆ U →
          ∫ x in U, u x * (fderiv ℝ φ x) (basisVec i) ∂MeasureTheory.volume =
            -∫ x in U, gi x * φ x ∂MeasureTheory.volume
/-- The distributional integration-by-parts identities for all gradient
components. -/
def HasWeakGradientOn {d : ℕ} (U : Set (Homogenization.Vec d)) (u : Homogenization.Vec d → ℝ)
    (Du : Homogenization.Vec d → Homogenization.Vec d) : Prop :=
  ∀ i : Fin d, HasWeakPartialDerivOn U i u (fun x => Du x i)
/-- Square integrability on the specified domain with restricted Lebesgue measure. -/
abbrev MemL2On {d : ℕ} (U : Set (Homogenization.Vec d)) (u : Homogenization.Vec d → ℝ) : Prop :=
  MeasureTheory.MemLp u 2 (MeasureTheory.volume.restrict U)
/-- Square integrability of each weak gradient component on the domain. -/
def GradMemL2On {d : ℕ} (U : Set (Homogenization.Vec d))
    (Du : Homogenization.Vec d → Homogenization.Vec d) : Prop :=
  ∀ i : Fin d, MemL2On U (fun x => Du x i)
/-- A function and weak gradient with the L² certificates defining H¹ on a domain. -/
structure H1Function {d : ℕ} (U : Set (Homogenization.Vec d)) where
  toFun : Homogenization.Vec d → ℝ
  grad : Homogenization.Vec d → Homogenization.Vec d
  memL2 : MemL2On U toFun
  gradMemL2 : GradMemL2On U grad
  hasWeakGradient : HasWeakGradientOn U toFun grad
instance {d : ℕ} {U : Set (Homogenization.Vec d)} :
    CoeFun (H1Function U) (fun _ => Homogenization.Vec d → ℝ) where coe u := u.toFun
/-- An H¹ function approximable by compactly supported smooth functions in H¹,
encoding zero trace. -/
structure H10Function {d : ℕ} (U : Set (Homogenization.Vec d)) extends H1Function U where
  approx : ℕ → Homogenization.Vec d → ℝ
  approx_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (approx n)
  approx_hasCompactSupport : ∀ n, HasCompactSupport (approx n)
  approx_support_subset : ∀ n, tsupport (approx n) ⊆ U
  tendsto_approx :
    Filter.Tendsto
      (fun n =>
        MeasureTheory.eLpNorm (fun x => approx n x - toH1Function.toFun x) 2
          (MeasureTheory.volume.restrict U))
      Filter.atTop (nhds 0)
  tendsto_approx_grad :
    ∀ i : Fin d,
      Filter.Tendsto
        (fun n =>
          MeasureTheory.eLpNorm
            (fun x => (fderiv ℝ (approx n) x) (basisVec i) - toH1Function.grad x i) 2
            (MeasureTheory.volume.restrict U))
        Filter.atTop (nhds 0)
instance {d : ℕ} {U : Set (Homogenization.Vec d)} :
    CoeFun (H10Function U) (fun _ => Homogenization.Vec d → ℝ) where coe u := u.toH1Function.toFun
/-- The vector field `f` is the weak gradient of an `H¹(U)` function. -/
def IsPotentialOn {d : ℕ} (U : Set (Homogenization.Vec d))
    (f : Homogenization.Vec d → Homogenization.Vec d) : Prop :=
  ∃ u : H1Function U, u.grad = f
/-- The vector field `g` is weakly divergence free in `U`: it is orthogonal to the gradient of
every `H¹₀(U)` function. -/
def IsSolenoidalOn {d : ℕ} (U : Set (Homogenization.Vec d))
    (g : Homogenization.Vec d → Homogenization.Vec d) : Prop :=
  ∀ φ : H10Function U,
    ∫ x in U, vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume = 0
/-- `f` is a gradient field whose flux `a f` is weakly divergence free: `−∇·(a f) = 0` in `U`. -/
def IsAHarmonicGradient {d : ℕ} (a : CoeffField d) (U : Set (Homogenization.Vec d))
    (f : Homogenization.Vec d → Homogenization.Vec d) : Prop :=
  IsPotentialOn U f ∧ IsSolenoidalOn U (fun x => matVecMul (a x) (f x))
/-- The `a`-harmonic functions in `H¹(U)`: weak solutions of `−∇·(a∇v) = 0` in `U`. -/
structure AHarmonicFunction {d : ℕ} (a : CoeffField d) (U : Set (Homogenization.Vec d)) where
  toH1 : H1Function U
  isHarmonic : IsAHarmonicGradient a U toH1.grad
end Homogenization
namespace SubdiffusiveProcess.CoarseGrainingVocab
/-- A scalar coefficient represented as its multiple of the identity matrix. -/
def scalarCoeffField {d : ℕ} (a : Homogenization.Vec d → ℝ) : Homogenization.CoeffField d :=
  fun x => Homogenization.scalarMatrix (a x)
/-- The Lebesgue-volume-normalized average on a spatial set. -/
noncomputable def volumeAverage {d : ℕ} (U : Set (Homogenization.Vec d))
    (f : Homogenization.Vec d → ℝ) : ℝ :=
  (volume U).toReal⁻¹ * ∫ x in U, f x ∂volume
/-- The cell-problem energy of direction `eᵢ` on the triadic cube `Q` for the scalar coefficient
`a`: `inf_{w ∈ H¹₀(Q)} ⨍_Q a |eᵢ + ∇w|²`. For a symmetric coefficient this is `eᵢ·a(Q)eᵢ`, where
`a(Q)` is the coarse-grained matrix. -/
noncomputable def cellEnergy {d : ℕ} (a : Homogenization.Vec d → ℝ)
    (Q : Homogenization.TriadicCube d) (i : Fin d) : ℝ :=
  sInf
    {E |
      ∃ w : Homogenization.H10Function (Homogenization.openCubeSet Q),
        E =
          volumeAverage (Homogenization.openCubeSet Q)
            (fun x => a x * Homogenization.vecNormSq (Homogenization.basisVec i + w.grad x))}
/-- The effective diffusivity `ahom_m` of the cutoff coefficient `a_m`: the infimum over cube
scales `n` of `(1/d) Σᵢ E[eᵢ·a_m(𝒞ₙ)eᵢ]`. These values are nonincreasing in `n` (subadditivity),
so the infimum is the limit `lim_n ahom_m(𝒞ₙ)`. -/
noncomputable def ahom {d : ℕ} (M : SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) : ℝ :=
  sInf
    (Set.range fun n : ℕ =>
      (∑ i : Fin d,
          ∫ ω,
            cellEnergy (SubdiffusiveProcess.Model.aCutoff M m ω)
              (Homogenization.originCube d n) i ∂M.P.toMeasure) /
        (d : ℝ))
/-- The integrand `−½ ∇v·(sym a)∇v − p·a∇v + q·∇v` of the response functional. -/
noncomputable def responseIntegrand {d : ℕ} (U : Set (Homogenization.Vec d))
    (a : Homogenization.CoeffField d) (p q : Homogenization.Vec d)
    (v : Homogenization.AHarmonicFunction a U) : Homogenization.Vec d → ℝ :=
  fun x =>
    -((1 / 2 : ℝ) *
        Homogenization.vecDot (v.toH1.grad x)
          (Homogenization.matVecMul (Homogenization.symmPart (a x)) (v.toH1.grad x)))
      - Homogenization.vecDot p (Homogenization.matVecMul (a x) (v.toH1.grad x))
      + Homogenization.vecDot q (v.toH1.grad x)
/-- The response functional
`J(U, p, q; a) = sup {⨍_U (−½ ∇v·(sym a)∇v − p·a∇v + q·∇v) : v ∈ H¹(U), −∇·(a∇v) = 0}`. -/
noncomputable def J {d : ℕ} (U : Set (Homogenization.Vec d)) (a : Homogenization.CoeffField d)
    (p q : Homogenization.Vec d) : ℝ :=
  sSup {r | ∃ v : Homogenization.AHarmonicFunction a U, r = volumeAverage U (responseIntegrand U a p q v)}
open scoped ENNReal
/-- The normalized defect `J^max_m(U) = sup_{|e| = 1} J(U, ā_m^{-1/2} e, ā_m^{1/2} e; a_m)` of the
cutoff coefficient `a_m = aCutoff M m ω`, with `ā_m = ahom M m`. -/
noncomputable def normalizedDefect {d : ℕ} (M : SubdiffusiveProcess.Model.GMCModel d) (m : ℕ)
    (U : Set (Homogenization.Vec d)) (ω : SubdiffusiveProcess.Model.PotentialSample d) : ℝ≥0∞ :=
  ⨆ e : {e : Homogenization.Vec d // Homogenization.vecNormSq e = 1},
    ENNReal.ofReal
      (J U (scalarCoeffField (SubdiffusiveProcess.Model.aCutoff M m ω))
        ((Real.sqrt (ahom M m))⁻¹ • e.1) (Real.sqrt (ahom M m) • e.1))
/-- The `L^ξ` norm `(∫ X^ξ dμ)^{1/ξ}` of an `[0, ∞]`-valued random variable. -/
noncomputable def paperENNRealLpNorm {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (ξ : ℝ) (X : Ω → ℝ≥0∞) : ℝ≥0∞ :=
  (∫⁻ ω, (X ω) ^ ξ ∂μ) ^ ξ⁻¹
end SubdiffusiveProcess.CoarseGrainingVocab
/-- The translated open cube `z + P`. -/
def SubdiffusiveProcess.LambdaStability.translatedDomain {d : ℕ} (w : Homogenization.Vec d)
    (P : Homogenization.TriadicCube d) : Set (Homogenization.Vec d) :=
  Homogenization.translateSet w (Homogenization.openCubeSet P)
open _root_.GMCExplicitDeltaAudit.SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal
/-- The explicit cascade in dimension `d` with disorder threshold `delta0` and constants
`C32` (for the `L^32` norm of the normalized defect) and `Cmean` (for the mean directional
response): for every model of disorder `δ ≤ delta0`, every cutoff `m`, every cube `z + 𝒞ₙ` with
`n ≥ m` and every Euclidean unit vector `e`, the normalized defect `J^max_m(z + 𝒞ₙ)` and the
directional response `J(z + 𝒞ₙ, ā_m^{-1/2} e, ā_m^{1/2} e; a_m)` are measurable,
`‖J^max_m(z + 𝒞ₙ)‖_{L^32} ≤ C32 δ²` and `E J(z + 𝒞ₙ, ā_m^{-1/2} e, ā_m^{1/2} e; a_m) ≤ Cmean δ²`. -/
def ExplicitCascade (d : ℕ) (delta0 C32 Cmean : ℝ) : Prop :=
  ∀ M : SubdiffusiveProcess.Model.GMCModel d, M.delta ≤ delta0 →
    ∀ m n : ℕ, m ≤ n → ∀ z : Homogenization.Vec d,
      Measurable (normalizedDefect M m
          (SubdiffusiveProcess.LambdaStability.translatedDomain z
            (Homogenization.originCube d (n : ℤ)))) ∧
      paperENNRealLpNorm M.P.toMeasure 32
          (normalizedDefect M m
            (SubdiffusiveProcess.LambdaStability.translatedDomain z
              (Homogenization.originCube d (n : ℤ)))) ≤
        ENNReal.ofReal (C32 * M.delta ^ 2) ∧
      ∀ e : Homogenization.Vec d, Homogenization.vecNormSq e = 1 →
        Measurable (fun ω =>
          J (SubdiffusiveProcess.LambdaStability.translatedDomain z
              (Homogenization.originCube d (n : ℤ)))
            (scalarCoeffField (SubdiffusiveProcess.Model.aCutoff M m ω))
            ((Real.sqrt (ahom M m))⁻¹ • e) (Real.sqrt (ahom M m) • e)) ∧
        ∫⁻ ω, ENNReal.ofReal
            (J (SubdiffusiveProcess.LambdaStability.translatedDomain z
                (Homogenization.originCube d (n : ℤ)))
              (scalarCoeffField (SubdiffusiveProcess.Model.aCutoff M m ω))
              ((Real.sqrt (ahom M m))⁻¹ • e) (Real.sqrt (ahom M m) • e)) ∂M.P.toMeasure ≤
          ENNReal.ofReal (Cmean * M.delta ^ 2)
/-- **The explicit cascade** in dimensions two, three and four, with the thresholds
`δ₀(2) = .36665`, `δ₀(3) = .18870`, `δ₀(4) = .15698` and the explicit constants `C₃₂(d)` and
`C_mean(d)` (library: `GMCExplicitDelta.explicit_cascade_two`, `_three`, `_four`). -/
theorem explicit_cascade :
    ExplicitCascade 2 (36665 / 100000) (23138371504 / 53772889) (230590996 / 53772889) ∧
    ExplicitCascade 3 (18870 / 100000) (89475125 / 1186923) (17849411 / 3560769) ∧
    ExplicitCascade 4 (15698 / 100000) (5918767600 / 61606801) (423596800 / 61606801) := by
  sorry
end
end GMCExplicitDeltaAudit
