module

public import GMCExplicitDelta.Proofs.FluxBound.G1
public import GMCExplicitDelta.Localization.L3Basic

/-!
# Localization pieces: `loc_G1flux`

On the good event `K_s(b_L∇v)² ≤ 2R J(Q_n)`: Abel summation of the dual Haar norm
(`K_s² = (1-w)∑ w^k ‖E_k G‖²`), C5 for fluxes on each depth-`k` cell, and the concavity bound
`(1-w)∑ w^k 𝗑(e_k) ≤ R` (G1(b)).
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open scoped ENNReal

namespace GMCExplicitDelta.Localization.FluxBound

open Assembly Contract GMCExplicitDelta.Haar

variable {d : ℕ}

theorem frozenJ_nonneg' (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    (p q : Homogenization.Vec d) (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    0 ≤ frozenJ M L (cubeAt 0 n) p q ω := by
  have h := twoJ_eq_cubeAverage M L n p q ω
  have : 0 ≤ cubeAverage (originCube d (n : ℤ)) (fun x =>
      SubdiffusiveProcess.Model.aCutoff M L ω x *
        vecNormSq ((frozenSol M L (cubeAt 0 n) p q ω).toH1.grad x)) :=
    cubeAverage_nonneg_of_nonneg_on fun x _ =>
      mul_nonneg (SubdiffusiveProcess.Model.aCutoff_pos M L ω x).le (Homogenization.vecNormSq_nonneg _)
  linarith

theorem memLp_frozenFlux (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    (p q : Homogenization.Vec d) (ω : SubdiffusiveProcess.Model.PotentialSample d) (i : Fin d) :
    MemLp (fun x => frozenFlux M L (cubeAt 0 n) p q ω x i) 2
      (normalizedCubeMeasure (originCube d (n : ℤ))) := by
  have hg := memLp_frozenGrad M L n p q ω i
  have hg' : MemLp (fun x => (frozenH1 M L (cubeAt 0 n) p q ω).grad x i) 2
      (volume.restrict (cubeSet (originCube d (n : ℤ)))) :=
    Homogenization.memLp_cubeMeasure_of_memLp_normalizedCubeMeasure _ hg
  have h2 := (memLp_aCutoff_mul M L ω (measurableSet_cubeSet (originCube d (n : ℤ)))
    (isBounded_cubeSet (originCube d (n : ℤ))) hg').const_mul (ahom M L)⁻¹
  have e : (fun x => frozenFlux M L (cubeAt 0 n) p q ω x i) = fun x =>
      (ahom M L)⁻¹ * (SubdiffusiveProcess.Model.aCutoff M L ω x *
        (frozenH1 M L (cubeAt 0 n) p q ω).grad x i) := by
    funext x
    simp only [frozenFlux, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e]
  simpa only [normalizedCubeMeasure, cubeMeasure] using
    (h2.smul_measure (c := ENNReal.ofReal ((cubeVolume (originCube d (n : ℤ)))⁻¹))
      ENNReal.ofReal_ne_top)

theorem haarDual_eq_tsum (Q : Homogenization.TriadicCube d) {q : ℝ} (hq : 1 < q)
    {G : Homogenization.Vec d → Homogenization.Vec d}
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q)) :
    Summable (fun k => (q⁻¹) ^ k *
        descendantsAverage Q k (fun R => vecNormSq (cubeAverageVec R G))) ∧
      haarDual Q q G = ENNReal.ofReal ((1 - q⁻¹) * ∑' k, (q⁻¹) ^ k *
        descendantsAverage Q k (fun R => vecNormSq (cubeAverageVec R G))) := by
  have hq0 : 0 ≤ q⁻¹ := inv_nonneg.mpr (by linarith)
  have hsi (i : Fin d) : Summable (fun k => q⁻¹ ^ k *
      Haar.energy Q (cubeIncrement Q k (fun x => G x i))) :=
    (summable_nat_add_iff 1).1 (summable_dual_increments Q hq (hG i))
  have htotal : Summable (fun k => q⁻¹ ^ k *
      ∑ i, Haar.energy Q (cubeIncrement Q k (fun x => G x i))) := by
    simp_rw [Finset.mul_sum]
    exact summable_sum (fun i _ => hsi i)
  have hfull : (∑' k, q⁻¹ ^ k * ∑ i, Haar.energy Q (cubeIncrement Q k (fun x => G x i))) =
      ∑ i, primalEnergy Q q⁻¹ (fun x => G x i) := by
    simp_rw [Finset.mul_sum]
    rw [Summable.tsum_finsetSum (fun i _ => hsi i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [(hsi i).tsum_eq_zero_add]
    simp only [pow_zero, one_mul, primalEnergy]
  have hproj (i : Fin d) := summable_weighted_projections Q hq (hG i)
  have hE (k : ℕ) : ∑ i, Haar.energy Q (cubeProjection Q k fun x => G x i) =
      descendantsAverage Q k (fun R => vecNormSq (cubeAverageVec R G)) :=
    sum_energy_projection Q k hG
  have hsp : Summable (fun k => q⁻¹ ^ k *
      ∑ i, Haar.energy Q (cubeProjection Q k fun x => G x i)) := by
    simp_rw [Finset.mul_sum]
    exact summable_sum (fun i _ => hproj i)
  refine ⟨hsp.congr (fun k => by rw [hE k]), ?_⟩
  unfold haarDual haarPrimal
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k =>
    mul_nonneg (pow_nonneg hq0 k) (Finset.sum_nonneg (fun _ _ => Haar.energy_nonneg _ _))) htotal,
    hfull]
  congr 1
  have h1 (i : Fin d) : primalEnergy Q q⁻¹ (fun x => G x i) = (1 - q⁻¹) *
      ∑' k, q⁻¹ ^ k * Haar.energy Q (cubeProjection Q k fun x => G x i) :=
    dualEnergy_eq Q hq (hG i)
  simp_rw [h1, ← Finset.mul_sum]
  congr 1
  rw [← Summable.tsum_finsetSum (fun i _ => hproj i)]
  exact tsum_congr fun k => by rw [← hE k, Finset.mul_sum]

theorem cubeAverageVec_frozenFlux (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (U : Ch02.Domain d) (p q : Homogenization.Vec d)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) (R : Homogenization.TriadicCube d) :
    cubeAverageVec R (frozenFlux M L U p q ω) = (Real.sqrt (ahom M L))⁻¹ •
      cubeAverageVec R (fun x => SubdiffusiveProcess.Model.aCutoff M L ω x •
        (frozenSol M L U p q ω).toH1.grad x) := by
  have hs := ahom_pos' M L
  funext i
  show cubeAverage R (fun x => frozenFlux M L U p q ω x i) =
    (Real.sqrt (ahom M L))⁻¹ * cubeAverage R (fun x => (SubdiffusiveProcess.Model.aCutoff M L ω x •
        (frozenSol M L U p q ω).toH1.grad x) i)
  rw [← cubeAverage_const_mul R]
  congr 1
  funext x
  have hpos := Real.sqrt_pos.mpr hs
  have e : ahom M L = Real.sqrt (ahom M L) * Real.sqrt (ahom M L) :=
    (Real.mul_self_sqrt hs.le).symm
  simp only [frozenFlux, frozenH1, H1Function.smul_grad, Pi.smul_apply, smul_eq_mul]
  generalize Real.sqrt (ahom M L) = s at e hpos ⊢
  rw [e]
  field_simp


end GMCExplicitDelta.Localization.FluxBound

namespace GMCExplicitDelta.Localization

open Assembly Contract GMCExplicitDelta.Haar FluxBound

variable {d : ℕ}

theorem loc_G1flux_proof (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    (ω : SubdiffusiveProcess.Model.PotentialSample d) (hω : ω ∈ goodEvent row M L 0 n)
    (p q : Homogenization.Vec d) :
    haarDual (originCube d (n : ℤ)) row.qs (frozenFlux M L (cubeAt 0 n) p q ω) ≤
      ENNReal.ofReal (2 * (row.R : ℝ) * frozenJ M L (cubeAt 0 n) p q ω) := by
  have hd0 := pos_of_mem_234 hd
  have hs := ahom_pos' M L
  have hw0 := wHaar_pos row
  have hw1 := wHaar_lt_one row hO
  have hqinv : row.qs⁻¹ = row.wHaar := inv_eq_of_mul_eq_one_right (qs_mul_wHaar row)
  have hq1 : 1 < row.qs := by
    have : row.qs = row.wHaar⁻¹ := by rw [← hqinv, inv_inv]
    rw [this]
    exact (one_lt_inv₀ hw0).2 hw1
  set w := row.wHaar with hw
  set J := frozenJ M L (cubeAt 0 n) p q ω with hJ
  have hJ0 : 0 ≤ J := frozenJ_nonneg' M L n p q ω
  obtain ⟨hsum, heq⟩ := haarDual_eq_tsum (originCube d (n : ℤ)) hq1
    (memLp_frozenFlux M L n p q ω)
  rw [hqinv] at hsum heq
  rw [heq]
  -- depth maxima
  set t : ℕ → ℝ := fun k => (depthMax M L 0 n k ω).toReal with ht
  have hfin : ∀ k, depthMax M L 0 n k ω ≠ ⊤ := by
    intro k
    refine ne_top_of_le_ne_top
      (show ENNReal.ofReal (row.thetaR * row.qs ^ k) ≠ ⊤ from ENNReal.ofReal_ne_top)
      (Finset.sup_le fun R hR => ?_)
    exact goodEvent_cell_bound_proof row hO M L n ω hω k R hR
  have ht0 : ∀ k, 0 ≤ t k := fun k => ENNReal.toReal_nonneg
  have hdef : ∀ k, ∀ R ∈ descendantsAtDepth (originCube d (n : ℤ)) k,
      ∀ e : Homogenization.Vec d, e ⬝ᵥ e = 1 → frozenJ M L (cellAt 0 R) e e ω ≤ t k := by
    intro k R hR e he
    have h1 : ENNReal.ofReal (frozenJ M L (cellAt 0 R) e e ω) ≤ depthMax M L 0 n k ω := by
      refine le_trans ?_ (Finset.le_sup (f := fun R => normalizedDefect M L (cellAt 0 R) ω) hR)
      rw [normalizedDefect_eq_iSup]
      exact le_iSup (fun e : {e : Homogenization.Vec d // vecNormSq e = 1} =>
        ENNReal.ofReal (frozenJ M L (cellAt 0 R) e.1 e.1 ω)) ⟨e, he⟩
    exact (ENNReal.ofReal_le_iff_le_toReal (hfin k)).1 h1
  -- the statistic
  have hst : haarStat row M L 0 n ω ≤ ENNReal.ofReal row.thetaR := hω
  have hne : haarStat row M L 0 n ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hst
  have hterm : ∀ j, ENNReal.ofReal ((1 - w) * w ^ j) * depthMax M L 0 n j ω ≠ ⊤ :=
    fun j => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin j)
  have hterm_real : ∀ j, (ENNReal.ofReal ((1 - w) * w ^ j) * depthMax M L 0 n j ω).toReal =
      (1 - w) * (w ^ j * t j) := by
    intro j
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg (by linarith) (pow_nonneg hw0.le j))]
    simp only [ht]
    ring
  have hsm : Summable (fun j => (1 - w) * (w ^ j * t j)) := by
    have := ENNReal.summable_toReal hne
    exact this.congr (fun j => hterm_real j)
  have hs' : Summable (fun j => w ^ j * t j) :=
    (summable_mul_left_iff (by linarith : (1 - w) ≠ 0)).1 hsm
  have hT : (1 - w) * ∑' j, w ^ j * t j ≤ ((row.R : ℝ) + (row.R : ℝ)⁻¹ - 2) / 2 := by
    have h1 : (haarStat row M L 0 n ω).toReal = (1 - w) * ∑' j, w ^ j * t j := by
      unfold haarStat
      rw [ENNReal.tsum_toReal_eq hterm, tsum_congr hterm_real, tsum_mul_left]
    have h2 : (haarStat row M L 0 n ω).toReal ≤ row.thetaR := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hst
      rwa [ENNReal.toReal_ofReal (thetaR_nonneg row hO)] at this
    rw [← h1]
    exact h2
  have hR1 : (1 : ℝ) < (row.R : ℝ) := by exact_mod_cast hO.par2.1
  obtain ⟨hxs, hxT⟩ := weighted_xfun_le hR1 hw0 hw1 ht0 hs' hT
  -- cell bounds
  have hE : ∀ k, descendantsAverage (originCube d (n : ℤ)) k
      (fun R => vecNormSq (cubeAverageVec R (frozenFlux M L (cubeAt 0 n) p q ω))) ≤
        Coarse.xfun (t k) * (2 * J) := by
    intro k
    have hcell : ∀ R ∈ descendantsAtDepth (originCube d (n : ℤ)) k,
        vecNormSq (cubeAverageVec R (frozenFlux M L (cubeAt 0 n) p q ω)) ≤
          Coarse.xfun (t k) * cubeAverage R (fun x => SubdiffusiveProcess.Model.aCutoff M L ω x *
            vecNormSq ((frozenSol M L (cubeAt 0 n) p q ω).toH1.grad x)) := by
      intro R hR
      have hb := cell_flux_bound M L ω n k p q hR (ht0 k) (hdef k R hR)
      rw [cubeAverageVec_frozenFlux, vecNormSq_smul', inv_pow, Real.sq_sqrt hs.le]
      exact hb
    calc _ ≤ descendantsAverage (originCube d (n : ℤ)) k (fun R => Coarse.xfun (t k) *
          cubeAverage R (fun x => SubdiffusiveProcess.Model.aCutoff M L ω x *
            vecNormSq ((frozenSol M L (cubeAt 0 n) p q ω).toH1.grad x))) :=
          descendantsAverage_le_descendantsAverage _ k hcell
      _ = _ := by rw [descendantsAverage_mul_left, avg_cells_energy M L n hd0 k p q ω]
  have hrs : Summable (fun k => w ^ k * (Coarse.xfun (t k) * (2 * J))) := by
    simpa [mul_assoc] using hxs.mul_right (2 * J)
  have hle : ∑' k, w ^ k * descendantsAverage (originCube d (n : ℤ)) k
      (fun R => vecNormSq (cubeAverageVec R (frozenFlux M L (cubeAt 0 n) p q ω))) ≤
        ∑' k, w ^ k * (Coarse.xfun (t k) * (2 * J)) :=
    hsum.tsum_le_tsum (fun k => mul_le_mul_of_nonneg_left (hE k) (pow_nonneg hw0.le k)) hrs
  have h1w : 0 ≤ 1 - w := by linarith
  have hfin2 : (1 - w) * ∑' k, w ^ k * descendantsAverage (originCube d (n : ℤ)) k
      (fun R => vecNormSq (cubeAverageVec R (frozenFlux M L (cubeAt 0 n) p q ω))) ≤
        2 * (row.R : ℝ) * J := by
    have hm : ∑' k, w ^ k * (Coarse.xfun (t k) * (2 * J)) =
        (∑' k, w ^ k * Coarse.xfun (t k)) * (2 * J) := by
      rw [← tsum_mul_right]
      exact tsum_congr fun k => by ring
    calc _ ≤ (1 - w) * ((∑' k, w ^ k * Coarse.xfun (t k)) * (2 * J)) := by
          rw [← hm]; exact mul_le_mul_of_nonneg_left hle h1w
      _ = ((1 - w) * ∑' k, w ^ k * Coarse.xfun (t k)) * (2 * J) := by ring
      _ ≤ (row.R : ℝ) * (2 * J) := mul_le_mul_of_nonneg_right hxT (by linarith)
      _ = _ := by ring
  exact ENNReal.ofReal_le_ofReal hfin2

end GMCExplicitDelta.Localization
