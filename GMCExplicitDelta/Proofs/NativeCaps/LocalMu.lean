module

public import SubdiffusiveProcess.CoarseGrainingVocab.ACutoffRestrictionLaw
public import Homogenization.Book.Ch04.Theorems.Mu
public import Homogenization.Book.Ch04.Theorems.CoarseObservables

/-! # Exact open-cell locality without thickening

The local Mu representative retains the stronger intermediate conclusion of the
upstream Chapter 4 slice-and-cover proof. Removing the null cube boundary then
allows the literal modulo-3 separation, including the equality case d = 4.
-/

@[expose] public section

open MeasureTheory Homogenization Homogenization.Book Homogenization.Book.Ch04
open SubdiffusiveProcess.CoarseGrainingVocab Filter
open scoped ENNReal BigOperators

namespace GMCExplicitDelta.Assembly

theorem exists_localMu_ae_eq
    {d : ℕ} {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : Homogenization.TriadicCube d) (P0 : BlockVec d) :
    ∃ Y : RegCoeffField d → ℝ,
      @Measurable (RegCoeffField d) ℝ (LocalSigmaR (cubeSet Q)) _ Y ∧
        (fun a : RegCoeffField d => Mu (cubeSet Q) P0 a.toFun) =ᵐ[P] Y := by
  classical
  let slice : ℕ → Set (RegCoeffField d) :=
    fun k => {a : RegCoeffField d | AEEQuantitativeEllipticSlice (cubeSet Q) k a.toFun}
  let covered : Set (RegCoeffField d) := ⋃ k : ℕ, slice k
  let cover : Option ℕ → Set (RegCoeffField d)
    | none => coveredᶜ
    | some k => slice k
  let f : (i : Option ℕ) → cover i → ℝ
    | none, _ => 0
    | some _k, a => Mu (cubeSet Q) P0 a.1.toFun
  have hagree :
      ∀ (i j : Option ℕ) (a : RegCoeffField d)
        (hai : a ∈ cover i) (haj : a ∈ cover j),
          f i ⟨a, hai⟩ = f j ⟨a, haj⟩ := by
    intro i j a hai haj
    cases i with
    | none =>
        cases j with
        | none => rfl
        | some k =>
            exact absurd (Set.mem_iUnion.mpr ⟨k, haj⟩) hai
    | some k =>
        cases j with
        | none =>
            exact absurd (Set.mem_iUnion.mpr ⟨k, hai⟩) haj
        | some _ => rfl
  have hcover : ⋃ i : Option ℕ, cover i = Set.univ := by
    ext a
    refine ⟨fun _ => Set.mem_univ a, fun _ => ?_⟩
    by_cases ha : a ∈ covered
    · rcases Set.mem_iUnion.mp ha with ⟨k, hk⟩
      exact Set.mem_iUnion.mpr ⟨some k, by simpa [cover] using hk⟩
    · exact Set.mem_iUnion.mpr ⟨none, by simpa [cover] using ha⟩
  let Y : RegCoeffField d → ℝ := Set.liftCover cover f hagree hcover
  refine ⟨Y, ?_, ?_⟩
  · -- `Y` is `LocalSigmaR (cubeSet Q)`-measurable, hence restriction-local.
    have hY_localSigma :
        @Measurable (RegCoeffField d) ℝ (LocalSigmaR (cubeSet Q)) _ Y := by
      let : MeasurableSpace (RegCoeffField d) := LocalSigmaR (cubeSet Q)
      have hcover_meas : ∀ i : Option ℕ, MeasurableSet (cover i) := by
        intro i
        cases i with
        | none =>
            exact (MeasurableSet.iUnion fun k =>
              measurableSet_localSigmaR_aeeQuantitativeEllipticSlice Q k).compl
        | some k => exact measurableSet_localSigmaR_aeeQuantitativeEllipticSlice Q k
      have hfm : ∀ i : Option ℕ, Measurable (f i) := by
        intro i
        cases i with
        | none => exact measurable_const
        | some k =>
            have hEntry :
                ∀ (i' j' : Fin d) {φ : Homogenization.Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) φ →
                  HasCompactSupport φ → tsupport φ ⊆ cubeSet Q →
                  @Measurable (cover (some k)) ℝ _ _
                    (fun x => entryTestR i' j' φ (x : RegCoeffField d)) := by
              intro i' j' φ hφ_cont hφ_compact hφ_support
              have hφ_probe : IsProbeR φ := IsProbeR.of_smooth hφ_cont hφ_compact
              have hφ_support' : Function.support φ ⊆ cubeSet Q :=
                (Function.support_subset_iff.2 fun x hx => subset_tsupport φ hx).trans hφ_support
              exact (measurable_entryTestR_localSigmaR i' j' hφ_probe hφ_support').comp
                measurable_subtype_coe
            simpa [f] using
              measurable_Mu_comp_aeeSlice_of_measurable_entryTest Q
                (A := fun x : cover (some k) => (x : RegCoeffField d))
                (fun x => x.2) hEntry P0
      exact measurable_liftCover cover hcover_meas f hfm hagree hcover
    exact hY_localSigma
  · -- `Y` agrees with `Mu ∘ toFun` on the a.s.-full elliptic locus.
    have hcovered_ae : ∀ᵐ a ∂P, a ∈ covered := by
      filter_upwards
          [hP.ae_locally_uniformly_elliptic.ae_exists_aeeQuantitativeEllipticSlice_cubeSet Q]
        with a ha
      exact Set.mem_iUnion.mpr ha
    filter_upwards [hcovered_ae] with a ha
    rcases Set.mem_iUnion.mp ha with ⟨k, hak⟩
    have ha_cover : a ∈ cover (some k) := hak
    change Mu (cubeSet Q) P0 a.toFun = Set.liftCover cover f hagree hcover a
    rw [Set.liftCover_of_mem
      (S := cover) (f := f) (hf := hagree) (hS := hcover) (i := some k) ha_cover]

/-- Integral-local information is unchanged by deleting the null cell boundary. -/
theorem localSigmaR_cube_le_open {d : ℕ} (Q : Homogenization.TriadicCube d) :
    LocalSigmaR (cubeSet Q) ≤ LocalSigmaR (openCubeSet Q) := by
  apply MeasurableSpace.generateFrom_le
  rintro s ⟨i, j, φ, hφ, hsupp, t, ht, rfl⟩
  let ψ := (openCubeSet Q).indicator φ
  have hψ : IsProbeR ψ := hφ.indicator (isOpen_openCubeSet Q).measurableSet
  have hsψ : Function.support ψ ⊆ openCubeSet Q := by
    intro x hx
    by_contra hx'
    exact hx (Set.indicator_of_notMem hx' φ)
  have he : entryTestR i j φ = entryTestR i j ψ := by
    funext a
    apply integral_congr_ae
    filter_upwards [cubeSet_ae_eq_openCubeSet Q] with x hx
    by_cases hxU : x ∈ openCubeSet Q
    · simp only [ψ, Set.indicator_of_mem hxU]
    · have hxQ : x ∉ cubeSet Q := by simpa only [hx] using hxU
      have hzero : φ x = 0 := by
        by_contra hz
        exact hxQ (hsupp hz)
      simp only [ψ, Set.indicator_of_notMem hxU, hzero, mul_zero]
  rw [he]
  exact measurable_entryTestR_localSigmaR i j hψ hsψ ht

/-- The cutoff response on a cell, with canonical coefficient certificates. -/
noncomputable def nativeResponse {d : ℕ}
    (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (p q : Homogenization.Vec d)
    (R : Homogenization.TriadicCube d) (ω : SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  J (Ch02.cubeDomain R) (aCutoffCoeffOnData M L ω (Ch02.cubeDomain R)).toCoeffOn p q

/-- An actual cutoff response has an a.e. representative local to the open cell. -/
theorem cutoffResponse_local_rep {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (p q : Homogenization.Vec d) (R : Homogenization.TriadicCube d) :
    ∃ Y : SubdiffusiveProcess.Model.PotentialSample d → ℝ,
      @Measurable _ ℝ ((LocalSigmaR (openCubeSet R)).comap (aCutoffRegCoeffField M L)) _ Y ∧
      nativeResponse M L p q R =ᵐ[M.P.toMeasure] Y := by
  let P := aCutoffRestrictionLaw M L
  let A := aCutoffRegCoeffField M L
  obtain ⟨Y0, hlocal, heq⟩ := exists_localMu_ae_eq (aCutoffRestrictionLaw_lawCarrier M L) R (-p, q)
  let Z : RegCoeffField d → ℝ := fun a => Y0 a - vecDot p q
  refine ⟨Z ∘ A, ?_, ?_⟩
  · exact ((hlocal.sub_const _).mono (localSigmaR_cube_le_open R) le_rfl).comp
      (Measurable.of_comap_le le_rfl)
  · have hresp : (fun a : RegCoeffField d => ResponseJ (cubeSet R) p q a.toFun) =ᵐ[P] Z :=
      ((aCutoffRestrictionLaw_lawCarrier M L).ResponseJ_cubeSet_eq_Mu_neg_left_sub_vecDot_ae R p q).trans
        (heq.sub Filter.EventuallyEq.rfl)
    have hpull := ae_eq_comp (measurable_aCutoffRegCoeffField M L).aemeasurable
      (by simpa only [P, aCutoffRestrictionLaw_eq_map] using hresp)
    filter_upwards [hpull] with ω hω
    change nativeResponse M L p q R ω = Z (A ω)
    change ResponseJ (cubeSet R) p q (A ω).toFun = Z (A ω) at hω
    rw [← hω]
    exact (responseJ_cubeSet_eq_openCubeSet_of_triadicCube R p q (A ω).toFun).symm

end GMCExplicitDelta.Assembly
