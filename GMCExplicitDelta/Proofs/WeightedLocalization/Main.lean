module

public import GMCExplicitDelta.Localization.L3Cell

/-!
# Proof of `loc_L3` (L3 with Young's inequality), statement v2

`loc_L3_proof` proves the target `GMCExplicitDelta.Localization.loc_L3` of
`Targets/LocalizationPieces.lean` in its v2 form (with `hφm : Measurable φ` and `φ ≤ 1` on `Q_n`).

Proof (pointwise Young on each cell, then averages): with `A = a_L(ω)`, `v_Q`, `v_R` the frozen
maximizers,
`A|∇v_R|² ≤ (1+ε)A|∇v_Q|² + (1+ε⁻¹)A|∇v_R - ∇v_Q|²`; average over each cell `R`, multiply by
`0 ≤ w_R ≤ 1`, use `w_R ≤ φ` on `R`, the additivity of `⨍φA|∇v_Q|²` over the cells, and the second
variation `½⨍_R A|∇v_R - ∇v_Q|² = J(R) - ⨍_R ρ` with `avg_R ⨍_R ρ = J(Q_n)`.
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open scoped ENNReal

namespace GMCExplicitDelta.Localization

open Assembly Contract

variable {d : ℕ}

theorem integrableOn_cubeSet_of_open {R : Homogenization.TriadicCube d}
    {f : Homogenization.Vec d → ℝ} (h : Integrable f (volume.restrict (openCubeSet R))) :
    IntegrableOn f (cubeSet R) volume :=
  IntegrableOn.congr_set_ae h (cubeSet_ae_eq_openCubeSet R)

theorem cubeAverage_mono_on {R : Homogenization.TriadicCube d} {f g : Homogenization.Vec d → ℝ}
    (hf : IntegrableOn f (cubeSet R) volume) (hg : IntegrableOn g (cubeSet R) volume)
    (h : ∀ x ∈ cubeSet R, f x ≤ g x) : cubeAverage R f ≤ cubeAverage R g := by
  unfold cubeAverage
  exact mul_le_mul_of_nonneg_left (setIntegral_mono_on hf hg (measurableSet_cubeSet R) h)
    (inv_nonneg.mpr (cubeVolume_nonneg R))

theorem cubeAverage_add_on {R : Homogenization.TriadicCube d} {f g : Homogenization.Vec d → ℝ}
    (hf : IntegrableOn f (cubeSet R) volume) (hg : IntegrableOn g (cubeSet R) volume) :
    cubeAverage R (fun x => f x + g x) = cubeAverage R f + cubeAverage R g := by
  unfold cubeAverage
  rw [integral_add hf hg]
  ring

theorem cubeAverage_nonneg_on {R : Homogenization.TriadicCube d} {f : Homogenization.Vec d → ℝ}
    (h : ∀ x ∈ cubeSet R, 0 ≤ f x) : 0 ≤ cubeAverage R f := by
  unfold cubeAverage
  exact mul_nonneg (inv_nonneg.mpr (cubeVolume_nonneg R))
    (setIntegral_nonneg (measurableSet_cubeSet R) h)

theorem sq_add_le_young {ε a b : ℝ} (hε : 0 < ε) :
    (a + b) ^ 2 ≤ (1 + ε) * a ^ 2 + (1 + ε⁻¹) * b ^ 2 := by
  have key : (1 + ε) * a ^ 2 + (1 + ε⁻¹) * b ^ 2 - (a + b) ^ 2 = (ε * a - b) ^ 2 / ε := by
    field_simp
    ring
  have : 0 ≤ (ε * a - b) ^ 2 / ε := div_nonneg (sq_nonneg _) hε.le
  linarith

theorem vecNormSq_add_le_young {ε : ℝ} (hε : 0 < ε) (a b : Homogenization.Vec d) :
    vecNormSq (a + b) ≤ (1 + ε) * vecNormSq a + (1 + ε⁻¹) * vecNormSq b := by
  simp only [vecNormSq, vecDot, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have := sq_add_le_young (a := a i) (b := b i) hε
  nlinarith [this]

section

variable (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
  (ω : SubdiffusiveProcess.Model.PotentialSample d)

theorem aCutoff_nonneg' (x : Homogenization.Vec d) :
    0 ≤ SubdiffusiveProcess.Model.aCutoff M L ω x :=
  (SubdiffusiveProcess.Model.aCutoff_pos M L ω x).le

/-- **L3 (weighted localization) with Young's inequality**, v2 (`φ` measurable, `φ ≤ 1` on `Q_n`). -/
theorem loc_L3_proof (n k : ℕ) (p q : Homogenization.Vec d) {ε : ℝ}
    (hε : 0 < ε) (φ : Homogenization.Vec d → ℝ) (hφm : Measurable φ)
    (hφ1 : ∀ x ∈ cubeSet (originCube d (n : ℤ)), φ x ≤ 1) (w : Homogenization.TriadicCube d → ℝ)
    (hw : ∀ R, 0 ≤ w R ∧ w R ≤ 1)
    (hwφ : ∀ R ∈ descendantsAtDepth (originCube d (n : ℤ)) k, ∀ x ∈ cubeSet R, w R ≤ φ x) :
    cellJw M L n k w p q ω ≤
      (1 + ε) / 2 * cubeAverage (originCube d (n : ℤ)) (fun x =>
          φ x * vecDot ((frozenH1 M L (cubeAt 0 n) p q ω).grad x)
            (frozenFlux M L (cubeAt 0 n) p q ω x)) +
        (1 + ε⁻¹) * (cellJ M L n k p q ω - frozenJ M L (cubeAt 0 n) p q ω) := by
  classical
  set Q := originCube d (n : ℤ) with hQ
  set D := descendantsAtDepth Q k with hD
  set A := SubdiffusiveProcess.Model.aCutoff M L ω with hA
  set gQ := (frozenSol M L (cubeAt 0 n) p q ω).toH1.grad with hgQ
  set gR : Homogenization.TriadicCube d → Homogenization.Vec d → Homogenization.Vec d :=
    fun R => (frozenSol M L (cellAt 0 R) p q ω).toH1.grad with hgR
  set eQ : Homogenization.Vec d → ℝ := fun x => A x * vecNormSq (gQ x) with heQ
  set dR : Homogenization.TriadicCube d → Homogenization.Vec d → ℝ :=
    fun R x => A x * vecNormSq (gR R x - gQ x) with hdR
  set eR : Homogenization.TriadicCube d → Homogenization.Vec d → ℝ :=
    fun R x => A x * vecNormSq (gR R x) with heR
  have hA0 : ∀ x, 0 ≤ A x := aCutoff_nonneg' M L ω
  -- the integrand of the statement is `φ eQ`
  have hint : (fun x => φ x * vecDot ((frozenH1 M L (cubeAt 0 n) p q ω).grad x)
      (frozenFlux M L (cubeAt 0 n) p q ω x)) = fun x => φ x * eQ x := by
    funext x
    rw [frozen_density]
  rw [hint]
  -- integrability on the cells and on the cube
  have hRQ : ∀ R ∈ D, openCubeSet R ⊆ openCubeSet Q := fun R hR =>
    openCubeSet_subset_of_mem_descendantsAtDepth hR
  have hgQR : ∀ R ∈ D, ∀ i, MemLp (fun x => gQ x i) 2 (volume.restrict (openCubeSet R)) :=
    fun R hR i => grad_memLp_sub M L ω (Q := Q) (hRQ R hR) p q i
  have hgRR : ∀ R, ∀ i, MemLp (fun x => gR R x i) 2 (volume.restrict (openCubeSet R)) :=
    fun R i => grad_memLp_sub M L ω (Q := R) (R := R) subset_rfl p q i
  have heQ_R : ∀ R ∈ D, IntegrableOn eQ (cubeSet R) volume := fun R hR =>
    integrableOn_cubeSet_of_open (integrable_aCutoff_vecDot M L ω (measurableSet_openCubeSet R)
      (isBounded_openCubeSet R) (hgQR R hR) (hgQR R hR))
  have heR_R : ∀ R, IntegrableOn (eR R) (cubeSet R) volume := fun R =>
    integrableOn_cubeSet_of_open (integrable_aCutoff_vecDot M L ω (measurableSet_openCubeSet R)
      (isBounded_openCubeSet R) (hgRR R) (hgRR R))
  have hdR_R : ∀ R ∈ D, IntegrableOn (dR R) (cubeSet R) volume := fun R hR => by
    have hsub : ∀ i, MemLp (fun x => (gR R x - gQ x) i) 2 (volume.restrict (openCubeSet R)) :=
      fun i => (hgRR R i).sub (hgQR R hR i)
    exact integrableOn_cubeSet_of_open (integrable_aCutoff_vecDot M L ω
      (measurableSet_openCubeSet R) (isBounded_openCubeSet R) hsub hsub)
  -- `0 ≤ φ ≤ 1` on the cube (every point lies in a cell)
  have hφ0 : ∀ x ∈ cubeSet Q, 0 ≤ φ x := fun x hx => by
    obtain ⟨R, hR, hxR⟩ := exists_mem_descendantsAtDepth_of_mem_cubeSet k hx
    exact (hw R).1.trans (hwφ R hR x hxR)
  have hφeQ_Q : IntegrableOn (fun x => φ x * eQ x) (cubeSet Q) volume := by
    have heQ_Q : IntegrableOn eQ (cubeSet Q) volume :=
      integrableOn_cubeSet_of_open (integrable_aCutoff_vecDot M L ω (measurableSet_openCubeSet Q)
        (isBounded_openCubeSet Q) (fun i => grad_memLp_sub M L ω (Q := Q) (R := Q) subset_rfl p q i)
        (fun i => grad_memLp_sub M L ω (Q := Q) (R := Q) subset_rfl p q i))
    refine Integrable.mono' heQ_Q.norm (hφm.aestronglyMeasurable.mul heQ_Q.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem (measurableSet_cubeSet Q)] with x hx
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hφ0 x hx)]
    exact mul_le_of_le_one_left (norm_nonneg _) (hφ1 x hx)
  have hφeQ_R : ∀ R ∈ D, IntegrableOn (fun x => φ x * eQ x) (cubeSet R) volume := fun R hR =>
    hφeQ_Q.mono_set (cubeSet_subset_of_mem_descendantsAtDepth hR)
  -- per-cell inequality
  have hcell : ∀ R ∈ D, w R * frozenJ M L (cellAt 0 R) p q ω ≤
      (1 + ε) / 2 * cubeAverage R (fun x => φ x * eQ x) +
        (1 + ε⁻¹) * (frozenJ M L (cellAt 0 R) p q ω - cubeAverage R (rhoQ M L ω n p q)) := by
    intro R hR
    obtain ⟨hw0, hw1⟩ := hw R
    have hJ := frozenJ_cell_energy M L ω p q R
    have hsv := frozenJ_cell_sub M L ω n p q k hR
    -- Young on the cell
    have hY : cubeAverage R (eR R) ≤ (1 + ε) * cubeAverage R eQ + (1 + ε⁻¹) * cubeAverage R (dR R) := by
      have hpt : ∀ x ∈ cubeSet R, eR R x ≤ (1 + ε) * eQ x + (1 + ε⁻¹) * dR R x := by
        intro x _
        have h := vecNormSq_add_le_young hε (gQ x) (gR R x - gQ x)
        rw [add_sub_cancel] at h
        have := mul_le_mul_of_nonneg_left h (hA0 x)
        simp only [heR, heQ, hdR]
        nlinarith [this]
      have hlin : cubeAverage R (fun x => (1 + ε) * eQ x + (1 + ε⁻¹) * dR R x) =
          (1 + ε) * cubeAverage R eQ + (1 + ε⁻¹) * cubeAverage R (dR R) := by
        rw [cubeAverage_add_on ((heQ_R R hR).const_mul _) ((hdR_R R hR).const_mul _),
          cubeAverage_const_mul', cubeAverage_const_mul']
      rw [← hlin]
      exact cubeAverage_mono_on (heR_R R) (((heQ_R R hR).const_mul _).add
        ((hdR_R R hR).const_mul _)) hpt
    -- `w_R ⨍_R eQ ≤ ⨍_R φ eQ`
    have hW : w R * cubeAverage R eQ ≤ cubeAverage R (fun x => φ x * eQ x) := by
      rw [← cubeAverage_const_mul']
      refine cubeAverage_mono_on ((heQ_R R hR).const_mul _) (hφeQ_R R hR) fun x hx => ?_
      exact mul_le_mul_of_nonneg_right (hwφ R hR x hx) (mul_nonneg (hA0 x) (vecNormSq_nonneg _))
    have hd0 : 0 ≤ cubeAverage R (dR R) :=
      cubeAverage_nonneg_on fun x _ => mul_nonneg (hA0 x) (vecNormSq_nonneg _)
    have heQ0 : 0 ≤ cubeAverage R eQ :=
      cubeAverage_nonneg_on fun x _ => mul_nonneg (hA0 x) (vecNormSq_nonneg _)
    have hε1 : 0 ≤ 1 + ε⁻¹ := by positivity
    -- combine
    have hsv' : frozenJ M L (cellAt 0 R) p q ω - cubeAverage R (rhoQ M L ω n p q) =
        (1 / 2) * cubeAverage R (dR R) := hsv
    have hJ' : frozenJ M L (cellAt 0 R) p q ω = (1 / 2) * cubeAverage R (eR R) := hJ
    rw [hsv', hJ']
    have h1 : w R * ((1 / 2) * cubeAverage R (eR R)) ≤
        w R * ((1 / 2) * ((1 + ε) * cubeAverage R eQ + (1 + ε⁻¹) * cubeAverage R (dR R))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hY (by norm_num)) hw0
    have h2 : w R * ((1 + ε⁻¹) * cubeAverage R (dR R)) ≤ (1 + ε⁻¹) * cubeAverage R (dR R) :=
      mul_le_of_le_one_left (mul_nonneg hε1 hd0) hw1
    have h3 : (1 + ε) * (w R * cubeAverage R eQ) ≤
        (1 + ε) * cubeAverage R (fun x => φ x * eQ x) :=
      mul_le_mul_of_nonneg_left hW (by linarith)
    nlinarith [h1, h2, h3]
  -- average over the cells
  have havg := descendantsAverage_le_descendantsAverage Q k hcell
  have hsplit : descendantsAverage Q k (fun R =>
      (1 + ε) / 2 * cubeAverage R (fun x => φ x * eQ x) +
        (1 + ε⁻¹) * (frozenJ M L (cellAt 0 R) p q ω - cubeAverage R (rhoQ M L ω n p q))) =
      (1 + ε) / 2 * descendantsAverage Q k (fun R => cubeAverage R (fun x => φ x * eQ x)) +
        (1 + ε⁻¹) * (descendantsAverage Q k (fun R => frozenJ M L (cellAt 0 R) p q ω) -
          descendantsAverage Q k (fun R => cubeAverage R (rhoQ M L ω n p q))) := by
    unfold descendantsAverage
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  have hφadd : descendantsAverage Q k (fun R => cubeAverage R (fun x => φ x * eQ x)) =
      cubeAverage Q (fun x => φ x * eQ x) :=
    (cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q k _ hφeQ_Q).symm
  have hrho := frozenJ_cube_eq_avg_rho M L ω n p q k
  rw [hsplit, hφadd, ← hrho] at havg
  exact havg

end

end GMCExplicitDelta.Localization
