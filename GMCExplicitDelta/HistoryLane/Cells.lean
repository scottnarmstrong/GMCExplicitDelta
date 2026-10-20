module

public import GMCExplicitDelta.Assembly.ModelEvents

/-!
# History lane: geometry of depth-`j` cells

Depth-`j` cells of `z + Q_n` with `j ≤ n` are translates of `Q_{n-j}` (`cellAt_eq_cubeAt`), and a
cell of depth `j ≥ n` lies below a depth-`n` cell (`exists_descendant_of_depth_ge`).
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book

namespace GMCExplicitDelta.Assembly

variable {d : ℕ}

theorem cellAt_eq_cubeAt (z : Homogenization.Vec d) (R : Homogenization.TriadicCube d) (s : ℕ)
    (hs : R.scale = (s : ℤ)) :
    cellAt z R = cubeAt (z + fun i => (R.index i : ℝ) * (3 : ℝ) ^ s) s := by
  unfold cellAt cubeAt SubdiffusiveProcess.LambdaStability.translatedDomain
  simp only [Ch02.Domain.mk.injEq]
  ext x
  simp only [mem_translateSet_iff_sub_mem, openCubeSet, cubeScaleFactor, hs, originCube,
    Set.mem_ofPred_eq, zpow_natCast, Pi.sub_apply, Pi.add_apply, Pi.zero_apply, Int.cast_zero]
  refine forall_congr' fun i => ?_
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> nlinarith [h1, h2]

theorem exists_descendant_of_depth_add {Q R : Homogenization.TriadicCube d} {n : ℕ} :
    ∀ {m : ℕ}, R ∈ descendantsAtDepth Q (n + m) →
      ∃ S ∈ descendantsAtDepth Q n, R ∈ descendantsAtDepth S m
  | 0, h => ⟨R, by simpa using h, by simp⟩
  | m + 1, h => by
    rw [← add_assoc, mem_descendantsAtDepth_succ_iff] at h
    obtain ⟨T, hT, hRT⟩ := h
    obtain ⟨S, hS, hTS⟩ := exists_descendant_of_depth_add hT
    exact ⟨S, hS, mem_descendantsAtDepth_succ_iff.mpr ⟨T, hTS, hRT⟩⟩

end GMCExplicitDelta.Assembly
