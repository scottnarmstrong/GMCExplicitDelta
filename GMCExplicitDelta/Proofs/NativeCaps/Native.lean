module

public import GMCExplicitDelta.Proofs.NativeCaps.Budget
public import GMCExplicitDelta.Proofs.NativeCaps.Loewner
public import GMCExplicitDelta.Averaging.MatrixAverageFiniteProbe

/-! # Native caps from the sharp modulo-3 matrix average -/

@[expose] public section

open Homogenization Homogenization.Book MeasureTheory Matrix ProbabilityTheory
open SubdiffusiveProcess.CoarseGrainingVocab
open GMCExplicitDelta.Averaging GMCExplicitDelta.Insertion
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace GMCExplicitDelta.Assembly

noncomputable local instance {d : ℕ} : ContinuousENorm (Matrix (Fin d) (Fin d) ℝ) :=
  SeminormedAddGroup.toContinuousENorm

open Contract

variable {d : ℕ}

/-- Real L32 form of the native cap, before ENNReal conversion. -/
theorem native_matrix_caps_origin [NeZero d] {row : Row d}
    (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (M : SubdiffusiveProcess.Model.GMCModel d) {D F : ℝ} (hD : 0 < D) (hF : 0 < F)
    (L j : ℕ) (hP : InductionP M L D F) :
    lpNorm (frozenDefect M L (cubeAt 0 (L + (j + 1)))) 32 M.P.toMeasure ≤
        nativeCap d (j + 1) D F ∧
      lpNorm (fun ω => max 0
        (‖Matrix.toEuclideanCLM (𝕜 := ℝ)
          (frozenDefect M L (cubeAt 0 (L + (j + 1))) ω)‖ - F))
        32 M.P.toMeasure ≤ D * frakU d (j + 1) D F := by
  simp only [cubeAt, cellAt_zero]
  classical
  let Q := originCube d ((L + (j + 1) : ℕ) : ℤ)
  let S := descendantsAtDepth Q j
  let I := {R : Homogenization.TriadicCube d // R ∈ S}
  let C := Fin d → Fin 3
  let B : C → I → SubdiffusiveProcess.Model.PotentialSample d → Matrix (Fin d) (Fin d) ℝ :=
    fun c R => frozenDefect M L (Ch02.cubeDomain (nativeChild R.val c))
  let A := frozenDefect M L (Ch02.cubeDomain Q)
  let H := finiteMatrixAverage M.P.toMeasure B
  have hSpos : S.Nonempty := descendantsAtDepth_nonempty Q j
  let : Nonempty I := ⟨⟨hSpos.choose, hSpos.choose_spec⟩⟩
  have hscale (R : I) : R.val.scale = (L : ℤ) + 1 := by
    have hh := scale_eq_sub_of_mem_descendantsAtDepth R.property
    dsimp only [Q, originCube] at hh
    omega
  have hchild (c : C) (R : I) : (nativeChild R.val c).scale = (L : ℤ) := by
    rw [nativeChild_scale, hscale]
    omega
  have hbudget c R := inductionP_cell_matrix_budget M L hD hF hP (nativeChild R.val c) (hchild c R)
  have hm c R : MemLp (B c R) 32 M.P.toMeasure := (hbudget c R).1
  have hmean c R u hu := (hbudget c R).2.2.2 u hu
  have hmoment c R := (hbudget c R).2.2.1
  have hmeas c R : Measurable (B c R) := measurable_frozenDefect M L _
  have hPSD c R ω : (B c R ω).PosSemidef := frozenDefect_posSemidef M L _ ω
  have hd2 : 2 ≤ d := by simp only [Finset.mem_insert, Finset.mem_singleton] at hd; omega
  have hd4 : d ≤ 4 := by simp only [Finset.mem_insert, Finset.mem_singleton] at hd; omega
  have hind c : iIndepFun (B c) M.P.toMeasure := by
    apply iIndepFun_frozenDefect_cells M L (fun R : I => nativeChild R.val c)
    intro R T hRT x y hx hy
    exact nativeChild_rangeSeparation hd4 (hscale R) (hscale T)
      (fun h => hRT (Subtype.ext h)) c hx hy
  have hIcard : Fintype.card I = 3 ^ (d * j) := by
    change Fintype.card S = _
    rw [Fintype.card_coe, descendantsAtDepth_card, ← pow_mul]
  have hcount : (descendantsAtDepth Q (j + 1)).card = Fintype.card C * Fintype.card I := by
    rw [descendantsAtDepth_card_succ]
    simp only [C, Fintype.card_fun, Fintype.card_fin, I, Fintype.card_coe]
    exact Nat.mul_comm _ _
  have hH : lpNorm H 32 M.P.toMeasure ≤
      (sigmaNorm d : ℝ) * D * Bbar32 (3 ^ (d * j)) D F := by
    have hh := finiteMatrixAverage_le hd2 B hD hF hmeas hm hPSD hind hmean hmoment
      hO.avg1.1 hO.avg1.2
    simpa only [H, hIcard] using hh
  have hparent := inductionP_matrix_budget M L hD hF hP (L + (j + 1)) (by omega) 0
  simp only [cubeAt, cellAt_zero] at hparent
  have hmA : MemLp A 32 M.P.toMeasure := hparent.1
  have hprobe (ω : SubdiffusiveProcess.Model.PotentialSample d)
      (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) : sphereQuadratic (A ω) u ≤ F + sphereQuadratic (H ω) u := by
    apply finiteMatrixAverage_probe_upper hm hmean ω u hu
    have hs := frozenDefect_subadd_translated M L 0 Q (j + 1) ω u
    simp only [cellAt_zero] at hs
    rw [sum_nativeChild, hcount] at hs
    simpa only [A, B, I, S, ← Finset.sum_coe_sort (s := descendantsAtDepth Q j)] using hs
  have hc := matrix_average_caps (fun ω => frozenDefect_posSemidef M L _ ω)
    hmA (finiteMatrixAverage_memLp hm) hF.le hprobe hparent.2.1 hH
  have hEx : min D ((sigmaNorm d : ℝ) * D * Bbar32 (3 ^ (d * j)) D F) =
      D * frakU d (j + 1) D F := by
    unfold frakU
    rw [ite_eq_right (by omega), mul_min_of_nonneg _ _ hD.le]
    simp only [mul_one, Nat.add_sub_cancel]
    congr 1
    ring
  constructor
  · simpa only [nativeCap, Nat.add_sub_cancel, A, Q] using hc.1
  · simpa only [hEx, A, Q] using hc.2

/-- ENNReal form of the native bound on the origin cube. -/
theorem native_caps_origin [NeZero d] {row : Row d}
    (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (M : SubdiffusiveProcess.Model.GMCModel d) {D F : ℝ} (hD : 0 < D) (hF : 0 < F)
    (L j : ℕ) (hP : InductionP M L D F) :
    paperENNRealLpNorm M.P.toMeasure 32 (normalizedDefect M L (cubeAt 0 (L + (j + 1)))) ≤
        ENNReal.ofReal (nativeCap d (j + 1) D F) ∧
      paperENNRealLpNorm M.P.toMeasure 32
        (fun ω => normalizedDefect M L (cubeAt 0 (L + (j + 1))) ω - ENNReal.ofReal F) ≤
        ENNReal.ofReal (D * frakU d (j + 1) D F) := by
  let U := Ch02.cubeDomain (originCube d ((L + (j + 1) : ℕ) : ℤ))
  let A := frozenDefect M L U
  have hc := native_matrix_caps_origin hd hO M hD hF L j hP
  simp only [cubeAt, cellAt_zero] at hc
  have hb := inductionP_matrix_budget M L hD hF hP (L + (j + 1)) (by omega) 0
  simp only [cubeAt, cellAt_zero] at hb ⊢
  have hm : MemLp A 32 M.P.toMeasure := hb.1
  have hA : Measurable A := measurable_frozenDefect M L U
  have heq : normalizedDefect M L U =
      fun ω => ENNReal.ofReal (‖Matrix.toEuclideanCLM (𝕜 := ℝ) (A ω)‖) :=
    funext (normalizedDefect_eq_ofReal_opNorm M L U)
  constructor
  · change paperENNRealLpNorm M.P.toMeasure 32 (normalizedDefect M L U) ≤ _
    rw [heq, paperNorm_matrix_eq hA, ← ofReal_lpNorm hm]
    exact ENNReal.ofReal_le_ofReal hc.1
  · let E : SubdiffusiveProcess.Model.PotentialSample d → ℝ :=
      fun ω => max 0 (‖Matrix.toEuclideanCLM (𝕜 := ℝ) (A ω)‖ - F)
    have hmE : MemLp E 32 M.P.toMeasure := by
      simpa only [E, ← Matrix.cstar_norm_def, max_comm, Pi.sub_apply] using
        (hm.norm.sub (memLp_const F)).pos_part
    have he : (fun ω => normalizedDefect M L U ω - ENNReal.ofReal F) =
        fun ω => ENNReal.ofReal (E ω) := by
      funext ω
      rw [normalizedDefect_eq_ofReal_opNorm, ← ENNReal.ofReal_sub _ hF.le]
      simp [E, A, ENNReal.ofReal_max]
    change paperENNRealLpNorm M.P.toMeasure 32
      (fun ω => normalizedDefect M L U ω - ENNReal.ofReal F) ≤ _
    rw [he, paperNorm_ofReal_eq_eLpNorm hmE.aestronglyMeasurable (fun _ => le_max_left _ _),
      ← ofReal_lpNorm hmE]
    exact ENNReal.ofReal_le_ofReal hc.2

/-- Exact target statement (A6). -/
theorem nativeCap_bound_proof {row : Row d} (hd : d ∈ ({2, 3, 4} : Finset ℕ)) (hO : row.Obligations)
    (M : SubdiffusiveProcess.Model.GMCModel d) {D F : ℝ} (hD : 0 < D) (hF : 0 < F) (hFD : F ≤ D)
    (L : ℕ) (hP : InductionP M L D F) :
    ∀ k, 1 ≤ k → ∀ z : Homogenization.Vec d,
      paperENNRealLpNorm M.P.toMeasure 32 (normalizedDefect M L (cubeAt z (L + k))) ≤
          ENNReal.ofReal (nativeCap d k D F) ∧
        paperENNRealLpNorm M.P.toMeasure 32
            (fun ω => normalizedDefect M L (cubeAt z (L + k)) ω - ENNReal.ofReal F) ≤
          ENNReal.ofReal (D * frakU d k D F) := by
  have hDmax : 0 < max D F := hD.trans_le (le_max_left D F)
  have hDcap : 0 < D := by simpa only [max_eq_left hFD] using hDmax
  have hd0 : d ≠ 0 := by simp only [Finset.mem_insert, Finset.mem_singleton] at hd; omega
  let : NeZero d := ⟨hd0⟩
  intro k hk z
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have ho := native_caps_origin hd hO M hDcap hF L j hP
  let X := normalizedDefect M L (Ch02.cubeDomain (originCube d ((L + (j + 1) : ℕ) : ℤ)))
  have hXm : Measurable X := by
    simpa only [cubeAt, cellAt_zero] using (hP (L + (j + 1)) (by omega) 0).1
  have hT : MeasurePreserving (translatePotentialSequence z) M.P.toMeasure M.P.toMeasure :=
    ⟨measurable_translatePotentialSequence z, potentialSequenceLaw_stationary M z⟩
  have heq : normalizedDefect M L (cubeAt z (L + (j + 1))) =
      fun ω => X (translatePotentialSequence z ω) :=
    funext (normalizedDefect_cellAt_translate M L z _)
  have hnorm : paperENNRealLpNorm M.P.toMeasure 32
      (normalizedDefect M L (cubeAt z (L + (j + 1)))) =
      paperENNRealLpNorm M.P.toMeasure 32 X := by
    rw [heq]
    unfold paperENNRealLpNorm
    rw [hT.lintegral_comp (hXm.pow_const (32 : ℝ))]
  have hex : paperENNRealLpNorm M.P.toMeasure 32
      (fun ω => normalizedDefect M L (cubeAt z (L + (j + 1))) ω - ENNReal.ofReal F) =
      paperENNRealLpNorm M.P.toMeasure 32 (fun ω => X ω - ENNReal.ofReal F) := by
    simp only [heq]
    unfold paperENNRealLpNorm
    rw [hT.lintegral_comp ((hXm.sub_const _).pow_const (32 : ℝ))]
  rw [hnorm, hex]
  simpa only [cubeAt, cellAt_zero, X] using ho

end GMCExplicitDelta.Assembly
