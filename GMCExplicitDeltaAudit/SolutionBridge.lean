module
public import GMCExplicitDeltaAudit.SolutionBasic
public import SubdiffusiveProcess.Vocab.NormalizedDefect
public import SubdiffusiveProcess.LambdaStability.ScalarCarriers
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DirichletMatrixBridge
import SubdiffusiveProcess.CoarseGrainingVocab.AnnealedProviders

/-!
# Translation between the challenge vocabulary and the library

Each object of `GMCExplicitDeltaAudit.SolutionBasic` (a verbatim copy of the challenge
vocabulary) is identified with the corresponding object of the library: the model, the
effective diffusivity, the response functional `J`, the translated cube and the normalized
defect. The final lemma `transfer` turns the library form of the explicit cascade into the
challenge form. None of these statements adds a hypothesis to the challenge theorem.
-/

@[expose] public section
noncomputable section
namespace GMCExplicitDeltaAudit
open MeasureTheory
namespace Conversion
variable {d : ℕ} {U : Set (Fin d → ℝ)}
open _root_.GMCExplicitDeltaAudit.SubdiffusiveProcess.Model

theorem localSigma_eq (W : Set (Homogenization.Vec d)) :
    PotentialField.localSigma W = _root_.SubdiffusiveProcess.Model.PotentialField.localSigma W := by
  unfold PotentialField.localSigma _root_.SubdiffusiveProcess.Model.PotentialField.localSigma
    Homogenization.LocalSigmaR _root_.Homogenization.LocalSigmaR
  rw [MeasurableSpace.comap_generateFrom, MeasurableSpace.comap_generateFrom]
  congr 1
  ext s
  constructor
  · rintro ⟨t, ⟨i, j, phi, hphi, hsupp, r, hr, rfl⟩, rfl⟩
    exact ⟨_root_.Homogenization.entryTestR i j phi ⁻¹' r,
      ⟨i, j, phi, ⟨hphi.measurable, hphi.bounded, hphi.hasCompactSupport⟩, hsupp, r, hr, rfl⟩, rfl⟩
  · rintro ⟨t, ⟨i, j, phi, hphi, hsupp, r, hr, rfl⟩, rfl⟩
    exact ⟨Homogenization.entryTestR i j phi ⁻¹' r,
      ⟨i, j, phi, ⟨hphi.measurable, hphi.bounded, hphi.hasCompactSupport⟩, hsupp, r, hr, rfl⟩, rfl⟩

/-- The library model with the same law, disorder and assumptions. -/
def toModel (M : GMCModel d) : _root_.SubdiffusiveProcess.Model.GMCModel d where
  delta := M.delta
  P := M.P
  shellPrefix := ⟨M.shellPrefix.dimension, M.shellPrefix.delta_pos,
    M.shellPrefix.delta_le_half, M.shellPrefix.independent, M.shellPrefix.marginal_scaling⟩
  G1 := ⟨M.G1.integrable, M.G1.mean_zero, M.G1.stationary, by
    intro W V hW hV hWV
    rw [← localSigma_eq W, ← localSigma_eq V]
    exact M.G1.range_dependence W V hW hV hWV⟩
  G2 := ⟨M.G2.regularity_expectation⟩
  G3 := ⟨M.G3.signed_coordinate_permutations, M.G3.negation⟩
  G4 := ⟨M.G4.exponential_integrable, M.G4.tauSq_pos⟩

def h1To (u : Homogenization.H1Function U) : _root_.Homogenization.H1Function U :=
  ⟨u.toFun, u.grad, u.memL2, u.gradMemL2, u.hasWeakGradient⟩
def h1From (u : _root_.Homogenization.H1Function U) : Homogenization.H1Function U :=
  ⟨u.toFun, u.grad, u.memL2, u.gradMemL2, u.hasWeakGradient⟩
def h10To (u : Homogenization.H10Function U) : _root_.Homogenization.H10Function U :=
  ⟨h1To u.toH1Function, u.approx, u.approx_smooth, u.approx_hasCompactSupport,
    u.approx_support_subset, u.tendsto_approx, u.tendsto_approx_grad⟩
def h10From (u : _root_.Homogenization.H10Function U) : Homogenization.H10Function U :=
  ⟨h1From u.toH1Function, u.approx, u.approx_smooth, u.approx_hasCompactSupport,
    u.approx_support_subset, u.tendsto_approx, u.tendsto_approx_grad⟩

open scoped Pointwise in
/-- The cell energy of the challenge is the diagonal entry of the library's coarse matrix. -/
theorem cellEnergy_eq (M : GMCModel d) (L n : ℕ) (omega : PotentialSample d) (i : Fin d) :
    SubdiffusiveProcess.CoarseGrainingVocab.cellEnergy (aCutoff M L omega)
        (Homogenization.originCube d n) i =
      _root_.SubdiffusiveProcess.CoarseGrainingVocab.randomAMatrix (toModel M) L
        (_root_.Homogenization.Book.Ch02.cubeDomain (_root_.Homogenization.originCube d n))
        omega i i := by
  let U := _root_.Homogenization.Book.Ch02.cubeDomain (_root_.Homogenization.originCube d n)
  have hdata := _root_.SubdiffusiveProcess.CoarseGrainingVocab.aCutoffCoeffOnData (toModel M) L omega U
  have ha0 : ∀ x, 0 ≤ _root_.SubdiffusiveProcess.Model.aCutoff (toModel M) L omega x :=
    fun x => (Real.exp_pos _).le
  have h := _root_.SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.vecDot_aMatrix_eq_dirichletInfOn
    hdata ha0 (Pi.single i 1)
  have hdiag : _root_.Homogenization.vecDot (Pi.single i (1 : ℝ))
      (_root_.Homogenization.matVecMul
        (_root_.SubdiffusiveProcess.CoarseGrainingVocab.aMatrix U hdata.toCoeffOn) (Pi.single i 1)) =
      _root_.SubdiffusiveProcess.CoarseGrainingVocab.aMatrix U hdata.toCoeffOn i i := by
    simp [_root_.Homogenization.vecDot, _root_.Homogenization.matVecMul, Pi.single_apply]
  show _ = _root_.SubdiffusiveProcess.CoarseGrainingVocab.aMatrix U hdata.toCoeffOn i i
  rw [← hdiag, h, _root_.SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.dirichletInfOn]
  unfold SubdiffusiveProcess.CoarseGrainingVocab.cellEnergy
  have hset : {E | ∃ w : Homogenization.H10Function
        (Homogenization.openCubeSet (Homogenization.originCube d n)),
      E = SubdiffusiveProcess.CoarseGrainingVocab.volumeAverage
        (Homogenization.openCubeSet (Homogenization.originCube d n))
        (fun x => aCutoff M L omega x *
          Homogenization.vecNormSq (Homogenization.basisVec i + w.grad x))} =
      (MeasureTheory.volume (U : Set (Fin d → ℝ))).toReal⁻¹ •
        _root_.SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.dirichletEnergySet
          (_root_.SubdiffusiveProcess.Model.aCutoff (toModel M) L omega)
          (U : Set (Fin d → ℝ)) (Pi.single i 1) := by
    ext E
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨_, ⟨h10To w, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
      exact ⟨h10From w, rfl⟩
  rw [hset, Real.sInf_smul_of_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)]
  rfl

/-- The effective diffusivity of the challenge is the library's. -/
theorem ahom_eq (M : GMCModel d) (L : ℕ) :
    SubdiffusiveProcess.CoarseGrainingVocab.ahom M L =
      _root_.SubdiffusiveProcess.CoarseGrainingVocab.ahom (toModel M) L := by
  unfold SubdiffusiveProcess.CoarseGrainingVocab.ahom _root_.SubdiffusiveProcess.CoarseGrainingVocab.ahom
  apply congrArg sInf
  apply congrArg Set.range
  funext n
  unfold _root_.SubdiffusiveProcess.CoarseGrainingVocab.abarScalarReadout
    _root_.SubdiffusiveProcess.CoarseGrainingVocab.abar
  congr 1
  rw [Matrix.trace]
  simp only [Matrix.diag]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [_root_.Homogenization.integral_matrix_apply
    (_root_.SubdiffusiveProcess.CoarseGrainingVocab.integrable_randomAMatrix (toModel M) L _) i i]
  congr 1
  funext omega
  exact cellEnergy_eq M L n omega i

theorem isPotentialOn_iff (f : (Fin d → ℝ) → (Fin d → ℝ)) :
    Homogenization.IsPotentialOn U f ↔ _root_.Homogenization.IsPotentialOn U f :=
  ⟨fun ⟨u, hu⟩ => ⟨h1To u, hu⟩, fun ⟨u, hu⟩ => ⟨h1From u, hu⟩⟩

theorem isSolenoidalOn_iff (g : (Fin d → ℝ) → (Fin d → ℝ)) :
    Homogenization.IsSolenoidalOn U g ↔ _root_.Homogenization.IsSolenoidalOn U g :=
  ⟨fun h φ => h (h10From φ), fun h φ => h (h10To φ)⟩

/-- An `a`-harmonic function of the challenge, as one of the library. -/
def ahfTo {a : _root_.Homogenization.CoeffField d} (v : Homogenization.AHarmonicFunction a U) :
    _root_.Homogenization.AHarmonicFunction a U :=
  ⟨h1To v.toH1, (isPotentialOn_iff _).1 v.isHarmonic.1, (isSolenoidalOn_iff _).1 v.isHarmonic.2⟩

/-- An `a`-harmonic function of the library, as one of the challenge. -/
def ahfFrom {a : _root_.Homogenization.CoeffField d} (v : _root_.Homogenization.AHarmonicFunction a U) :
    Homogenization.AHarmonicFunction a U :=
  ⟨h1From v.toH1, (isPotentialOn_iff _).2 v.isHarmonic.1, (isSolenoidalOn_iff _).2 v.isHarmonic.2⟩

/-- The response functional of the challenge, evaluated on the carrier and the coefficient field
of a library domain and coefficient, is the library's `J`. -/
theorem J_eq (W : _root_.Homogenization.Book.Ch02.Domain d)
    (a : _root_.Homogenization.Book.Ch02.CoeffOn W) (p q : Fin d → ℝ) :
    SubdiffusiveProcess.CoarseGrainingVocab.J W.carrier a.toCoeffField p q =
      _root_.SubdiffusiveProcess.CoarseGrainingVocab.J W a p q := by
  unfold SubdiffusiveProcess.CoarseGrainingVocab.J _root_.SubdiffusiveProcess.CoarseGrainingVocab.J
    _root_.Homogenization.Book.Ch02.responseJ _root_.Homogenization.Book.Ch02.responseValueSet
  congr 1
  ext r
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨ahfTo v, rfl⟩
  · rintro ⟨v, rfl⟩
    exact ⟨ahfFrom v, rfl⟩

/-- The response of the cutoff coefficient on a translated cube. -/
theorem J_cutoff_eq (M : GMCModel d) (m : ℕ) (omega : PotentialSample d) (z : Fin d → ℝ)
    (n : ℤ) (p q : Fin d → ℝ) :
    SubdiffusiveProcess.CoarseGrainingVocab.J
        (SubdiffusiveProcess.LambdaStability.translatedDomain z (Homogenization.originCube d n))
        (SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField (aCutoff M m omega)) p q =
      _root_.SubdiffusiveProcess.CoarseGrainingVocab.J
        (_root_.SubdiffusiveProcess.LambdaStability.translatedDomain z
          (_root_.Homogenization.originCube d n))
        (_root_.SubdiffusiveProcess.CoarseGrainingVocab.aCutoffCoeffOnData (toModel M) m omega
          (_root_.SubdiffusiveProcess.LambdaStability.translatedDomain z
            (_root_.Homogenization.originCube d n))).toCoeffOn p q :=
  J_eq (_root_.SubdiffusiveProcess.LambdaStability.translatedDomain z
      (_root_.Homogenization.originCube d n))
    (_root_.SubdiffusiveProcess.CoarseGrainingVocab.aCutoffCoeffOnData (toModel M) m omega
      (_root_.SubdiffusiveProcess.LambdaStability.translatedDomain z
        (_root_.Homogenization.originCube d n))).toCoeffOn p q

/-- The normalized defect of the challenge on a translated cube is the library's. -/
theorem normalizedDefect_eq (M : GMCModel d) (m : ℕ) (z : Fin d → ℝ) (n : ℤ) :
    SubdiffusiveProcess.CoarseGrainingVocab.normalizedDefect M m
        (SubdiffusiveProcess.LambdaStability.translatedDomain z (Homogenization.originCube d n)) =
      _root_.SubdiffusiveProcess.CoarseGrainingVocab.normalizedDefect (toModel M) m
        (_root_.SubdiffusiveProcess.LambdaStability.translatedDomain z
          (_root_.Homogenization.originCube d n)) := by
  funext omega
  unfold SubdiffusiveProcess.CoarseGrainingVocab.normalizedDefect
    _root_.SubdiffusiveProcess.CoarseGrainingVocab.normalizedDefect
    _root_.SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMaxOn
  rw [ahom_eq]
  refine iSup_congr fun e => ?_
  rw [J_cutoff_eq]

/-- The conclusion of the library's explicit cascade for one model, cutoff and cube. -/
def LibraryConclusion (d : ℕ) (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m n : ℕ)
    (z : Fin d → ℝ) (C32 Cmean : ℝ) : Prop :=
  Measurable (_root_.SubdiffusiveProcess.CoarseGrainingVocab.normalizedDefect M m
      (_root_.SubdiffusiveProcess.LambdaStability.translatedDomain z
        (_root_.Homogenization.originCube d (n : ℤ)))) ∧
    _root_.SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm M.P.toMeasure 32
        (_root_.SubdiffusiveProcess.CoarseGrainingVocab.normalizedDefect M m
          (_root_.SubdiffusiveProcess.LambdaStability.translatedDomain z
            (_root_.Homogenization.originCube d (n : ℤ)))) ≤
      ENNReal.ofReal (C32 * M.delta ^ 2) ∧
    ∀ e : Fin d → ℝ, _root_.Homogenization.vecNormSq e = 1 →
      Measurable (fun ω => _root_.SubdiffusiveProcess.CoarseGrainingVocab.J
          (_root_.SubdiffusiveProcess.LambdaStability.translatedDomain z
            (_root_.Homogenization.originCube d (n : ℤ)))
          (_root_.SubdiffusiveProcess.CoarseGrainingVocab.aCutoffCoeffOnData M m ω
            (_root_.SubdiffusiveProcess.LambdaStability.translatedDomain z
              (_root_.Homogenization.originCube d (n : ℤ)))).toCoeffOn
          ((Real.sqrt (_root_.SubdiffusiveProcess.CoarseGrainingVocab.ahom M m))⁻¹ • e)
          (Real.sqrt (_root_.SubdiffusiveProcess.CoarseGrainingVocab.ahom M m) • e)) ∧
      ∫⁻ ω, ENNReal.ofReal
          (_root_.SubdiffusiveProcess.CoarseGrainingVocab.J
            (_root_.SubdiffusiveProcess.LambdaStability.translatedDomain z
              (_root_.Homogenization.originCube d (n : ℤ)))
            (_root_.SubdiffusiveProcess.CoarseGrainingVocab.aCutoffCoeffOnData M m ω
              (_root_.SubdiffusiveProcess.LambdaStability.translatedDomain z
                (_root_.Homogenization.originCube d (n : ℤ)))).toCoeffOn
            ((Real.sqrt (_root_.SubdiffusiveProcess.CoarseGrainingVocab.ahom M m))⁻¹ • e)
            (Real.sqrt (_root_.SubdiffusiveProcess.CoarseGrainingVocab.ahom M m) • e))
          ∂M.P.toMeasure ≤
        ENNReal.ofReal (Cmean * M.delta ^ 2)

/-- The library form of the explicit cascade, for every challenge model below the threshold,
gives the challenge form. -/
theorem transfer {delta0 C32 Cmean : ℝ}
    (h : ∀ M : GMCModel d, M.delta ≤ delta0 → ∀ m n : ℕ, m ≤ n → ∀ z : Fin d → ℝ,
      LibraryConclusion d (toModel M) m n z C32 Cmean) :
    ExplicitCascade d delta0 C32 Cmean := by
  intro M hδ m n hmn z
  obtain ⟨h1, h2, h3⟩ := h M hδ m n hmn z
  simp only [normalizedDefect_eq, J_cutoff_eq, ahom_eq]
  exact ⟨h1, h2, fun e he => h3 e he⟩

end Conversion
end GMCExplicitDeltaAudit
