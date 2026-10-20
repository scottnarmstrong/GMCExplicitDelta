module

public import GMCExplicitDelta.Proofs.GridMax.Grid
public import GMCExplicitDelta.Proofs.GridMax.Norms
public import GMCExplicitDelta.Proofs.FineSensitivity.SubGaussian
public import GMCExplicitDelta.Proofs.FineSensitivity.Moments
public import GMCExplicitDelta.Insertion.FreshBandSource
public import GMCExplicitDelta.Insertion.FreshExponential

/-! # Sub-Gaussian grid maxima for the entire layerPrefix of layers -/

@[expose] public section

open Homogenization MeasureTheory ProbabilityTheory Real
open SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal

namespace GMCExplicitDelta.Assembly.GridMax

variable {d : ℕ}

/-- Exact variance proxy for the whole layerPrefix. -/
noncomputable def prefixProxy (M : GMCModel d) (L : ℕ) : ℝ≥0 :=
  ⟨((L : ℝ) + 1) * (Contract.proxyA : ℝ) * M.delta ^ 2, by
    have : (0 : ℝ) < (Contract.proxyA : ℝ) := by norm_num [Contract.proxyA]
    positivity⟩

/-- The layerPrefix inherits the exact Gaussian even-moment proxy. -/
theorem prefix_subGaussian (M : GMCModel d) (L : ℕ) (x : Homogenization.Vec d) :
    HasSubgaussianMGF (fun ω : PotentialSample d => layerPrefix L ω x) (prefixProxy M L) M.P.toMeasure := by
  change HasSubgaussianMGF (fun ω : PotentialSample d => ∑ i ∈ Finset.range (L + 1), ω i x) _ _
  refine fine_hasSubgaussianMGF_of_even
    (Insertion.layer_sum_symm M (Finset.range (L + 1)) x)
    (fun n => (Insertion.layer_sum_band_moments M (Finset.range (L + 1)) x).1 (2 * n)) ?_
  intro n
  change (∫ ω : PotentialSample d, (∑ i ∈ Finset.range (L + 1), ω i x) ^ (2 * n) ∂M.P.toMeasure) ≤
    ((2 * n - 1).doubleFactorial : ℝ) * (((L : ℝ) + 1) * (Contract.proxyA : ℝ) * M.delta ^ 2) ^ n
  simpa only [Finset.card_range, Nat.cast_add, Nat.cast_one] using
    Insertion.layer_sum_gaussian_moments M (Finset.range (L + 1)) x n

/-- Prefix values are measurable in the sample. -/
theorem prefix_measurable (L : ℕ) (x : Homogenization.Vec d) :
    Measurable (fun ω : PotentialSample d => layerPrefix L ω x) := by
  exact Finset.measurable_sum _ fun i _ =>
    (PotentialField.measurable_eval x).comp (measurable_pi_apply i)

/-- The absolute maximum over the grid. -/
noncomputable def maximum (N : ℕ) [NeZero N] (L : ℕ) (z : Homogenization.Vec d)
    (ω : PotentialSample d) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j : Fin d → Fin N => |layerPrefix L ω (gridPoint N j + z)|)

/-- Measurability of the finite absolute maximum. -/
theorem maximum_measurable (N : ℕ) [NeZero N] (L : ℕ) (z : Homogenization.Vec d) :
    Measurable (maximum N L z) := by
  have h := Finset.univ.measurable_sup' Finset.univ_nonempty
    (fun (j : Fin d → Fin N) _ => (prefix_measurable L (gridPoint N j + z)).norm)
  convert! h using 1
  funext ω
  simp only [maximum, Finset.sup'_apply, Real.norm_eq_abs]

/-- Nonnegativity of the absolute grid maximum. -/
theorem maximum_nonneg (N : ℕ) [NeZero N] (L : ℕ) (z : Homogenization.Vec d) (ω : PotentialSample d) :
    0 ≤ maximum N L z ω := by
  classical
  obtain ⟨j, _, he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun j : Fin d → Fin N => |layerPrefix L ω (gridPoint N j + z)|)
  change 0 ≤ Finset.univ.sup' Finset.univ_nonempty (fun j : Fin d → Fin N => |layerPrefix L ω (gridPoint N j + z)|)
  rw [he]
  exact abs_nonneg _

/-- Every layerPrefix value is bounded by the absolute grid maximum and the geometric remainder. -/
theorem prefix_le_maximum_remainder (N : ℕ) [NeZero N] (L : ℕ) (z : Homogenization.Vec d)
    (ω : PotentialSample d) {x : Homogenization.Vec d}
    (hx : x ∈ openCubeSet (originCube d 0)) :
    |layerPrefix L ω (x + z)| ≤ maximum N L z ω + remainder N L z ω := by
  classical
  obtain ⟨j, hj⟩ := prefix_grid_bound (Nat.pos_of_neZero N) L z ω hx
  exact hj.trans (add_le_add (Finset.le_sup' (fun j : Fin d → Fin N =>
    |layerPrefix L ω (gridPoint N j + z)|) (Finset.mem_univ j)) le_rfl)

/-- A finite absolute maximum has integrable linear exponentials at every rate. -/
theorem maximum_exp_integrable (M : GMCModel d) (N : ℕ) [NeZero N] (L : ℕ)
    (z : Homogenization.Vec d) (t : ℝ) :
    Integrable (fun ω => exp (t * maximum N L z ω)) M.P.toMeasure := by
  classical
  have hi (j : Fin d → Fin N) : Integrable (fun ω => exp (t * |layerPrefix L ω (gridPoint N j + z)|)) M.P.toMeasure :=
    Source.integrable_exp_mul_abs_of_subgaussian (prefix_subGaussian M L _) t
  refine (integrable_finsetSum Finset.univ (fun j _ => hi j)).mono'
    (((maximum_measurable N L z).const_mul t).exp.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  obtain ⟨j, hj, he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun j : Fin d → Fin N => |layerPrefix L ω (gridPoint N j + z)|)
  change exp (t * (Finset.univ.sup' Finset.univ_nonempty _)) ≤ _
  rw [he]
  exact Finset.single_le_sum
    (f := fun j : Fin d → Fin N => exp (t * |layerPrefix L ω (gridPoint N j + z)|))
    (fun j _ => (exp_pos _).le) hj

/-- Strict positivity of the whole-layerPrefix proxy. -/
theorem prefixProxy_pos (M : GMCModel d) (L : ℕ) : 0 < (prefixProxy M L : ℝ) := by
  have ha : (0 : ℝ) < (Contract.proxyA : ℝ) := by norm_num [Contract.proxyA]
  have hδ := M.shellPrefix.delta_pos
  change 0 < ((L : ℝ) + 1) * (Contract.proxyA : ℝ) * M.delta ^ 2
  positivity

/-- S8's exact grid-cardinality factor in the L128 norm. -/
theorem maximum_lnorm128 (M : GMCModel d) (N : ℕ) [NeZero N] (L : ℕ) (z : Homogenization.Vec d) :
    paperENNRealLpNorm M.P.toMeasure 128 (fun ω => ENNReal.ofReal (maximum N L z ω)) ≤
      ENNReal.ofReal (((N ^ d : ℕ) : ℝ) ^ (1 / 128 : ℝ) *
        (sqrt (2 * (prefixProxy M L : ℝ)) * sqrt Contract.P32)) := by
  have h := lnorm_max_le (μ := M.P.toMeasure)
    (fun (j : Fin d → Fin N) ω => layerPrefix L ω (gridPoint N j + z))
    (fun j => prefix_measurable L (gridPoint N j + z)) (by norm_num : (0 : ℝ) < 128)
    (fun j => fine_lnorm_abs128_le (prefix_subGaussian M L _) (prefixProxy_pos M L))
  simpa only [maximum, Fintype.card_fun, Fintype.card_fin] using h

/-- S8's exponential bound in paper norm form, retaining the exact factor two. -/
theorem maximum_exp128_norm (M : GMCModel d) (N : ℕ) [NeZero N] (L : ℕ) (z : Homogenization.Vec d) :
    paperENNRealLpNorm M.P.toMeasure 128 (fun ω => ENNReal.ofReal (exp (maximum N L z ω))) ≤
      ENNReal.ofReal ((2 * ((N ^ d : ℕ) : ℝ)) ^ (1 / 128 : ℝ) *
        exp (64 * (prefixProxy M L : ℝ))) := by
  have hb := integral_exp_finset_max_le (μ := M.P.toMeasure)
    (Finset.univ : Finset (Fin d → Fin N)) Finset.univ_nonempty
    (fun j ω => layerPrefix L ω (gridPoint N j + z))
    (fun j _ => prefix_measurable L _) (fun j _ => prefix_subGaussian M L _) 32
  have hb' : (∫ ω, exp (128 * maximum N L z ω) ∂M.P.toMeasure) ≤
      2 * ((N ^ d : ℕ) : ℝ) * exp (8192 * (prefixProxy M L : ℝ)) := by
    norm_num [maximum, Fintype.card_fun] at hb ⊢
    exact hb
  refine (lnorm_exp_of_moment (by norm_num : (0 : ℝ) < 128)
    (maximum_exp_integrable M N L z 128) hb').trans_eq ?_
  congr 1
  simp only [one_div]
  rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2 * ((N ^ d : ℕ) : ℝ)) (exp_pos _).le,
    ← exp_mul]
  congr 1
  congr 1
  ring

end GMCExplicitDelta.Assembly.GridMax
