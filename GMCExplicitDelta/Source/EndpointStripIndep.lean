module

public import GMCExplicitDelta.Source.EndpointStripField
public import GMCExplicitDelta.Source.EndpointStripAverage

/-!
# Independence of the two endpoints

`(X, P)` is measurable for the local sigma-field of the open orthant `{x i < -1/2}` and `Y` for the
one of `{y i > 1/2}`; these sets are at Euclidean distance at least `√d`.
-/

@[expose] public section

namespace GMCExplicitDelta.Source

open Homogenization MeasureTheory ProbabilityTheory
open SubdiffusiveProcess.Model SubdiffusiveProcess.Model.PotentialField

variable {d : ℕ}

/-- The open orthant to the left of the cube. -/
def leftOrthant (d : ℕ) : Set (Vec d) := {x | ∀ i, x i < -1 / 2}

/-- The open orthant to the right of the cube. -/
def rightOrthant (d : ℕ) : Set (Vec d) := {x | ∀ i, 1 / 2 < x i}

theorem isOpen_leftOrthant : IsOpen (leftOrthant d) := by
  have : leftOrthant d = ⋂ i, {x : Vec d | x i < -1 / 2} := by ext x; simp [leftOrthant]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i) continuous_const

theorem isOpen_rightOrthant : IsOpen (rightOrthant d) := by
  have : rightOrthant d = ⋂ i, {x : Vec d | 1 / 2 < x i} := by ext x; simp [rightOrthant]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)

theorem sqrt_le_euclideanNorm_orthants {x y : Vec d} (hx : x ∈ leftOrthant d)
    (hy : y ∈ rightOrthant d) : Real.sqrt (d : ℝ) ≤ euclideanNorm (x - y) := by
  unfold euclideanNorm
  apply Real.sqrt_le_sqrt
  unfold vecNormSq vecDot
  have : ∀ i, (1:ℝ) ≤ (x - y) i * (x - y) i := fun i => by
    have h1 := hx i
    have h2 := hy i
    simp only [Pi.sub_apply]
    nlinarith
  calc (d : ℝ) = ∑ _i : Fin d, (1:ℝ) := by simp
    _ ≤ _ := Finset.sum_le_sum fun i _ => this i

theorem leftOrthant_segment (t : ℝ) (ht : 0 < t) :
    diagPt d 0 + t • (-(diagDir d)) ∈ leftOrthant d := by
  intro i; simp [diagPt, diagDir]; linarith

theorem rightOrthant_segment (t : ℝ) (ht : 0 < t) :
    diagPt d 1 + t • (diagDir d) ∈ rightOrthant d := by
  intro i; simp [diagPt, diagDir]; linarith

/-- Independence of the two endpoints, from the range-one dependence. -/
theorem indep_endpoints (hd : 0 < d) {μ : Measure (PotentialField d)}
    (hI : ∀ (U V : Set (Vec d)), MeasurableSet U → MeasurableSet V →
      (∀ ⦃x y : Vec d⦄, x ∈ U → y ∈ V → Real.sqrt (d : ℝ) ≤ euclideanNorm (x - y)) →
      Indep (PotentialField.localSigma U) (PotentialField.localSigma V) μ) :
    IndepFun (fun g : PotentialField d => (epX g, epP g)) epY μ ∧
    IndepFun (fun g : PotentialField d => (epY g, epQ g)) epX μ := by
  have hind : Indep (PotentialField.localSigma (leftOrthant d))
      (PotentialField.localSigma (rightOrthant d)) μ :=
    hI _ _ isOpen_leftOrthant.measurableSet isOpen_rightOrthant.measurableSet
      (fun x y hx hy => sqrt_le_euclideanNorm_orthants hx hy)
  obtain ⟨hXL, hDL⟩ := measurable_localSigma_of_segment hd isOpen_leftOrthant
    (a := diagPt d 0) (v := -(diagDir d)) (ε := 1) one_pos (fun t ht _ => leftOrthant_segment t ht)
  obtain ⟨hYR, hQR⟩ := measurable_localSigma_of_segment hd isOpen_rightOrthant
    (a := diagPt d 1) (v := diagDir d) (ε := 1) one_pos (fun t ht _ => rightOrthant_segment t ht)
  have hPL : Measurable[PotentialField.localSigma (leftOrthant d)] (fun g : PotentialField d => epP g) := by
    have : (fun g : PotentialField d => epP g) =
        fun g => -(deriv g (diagPt d 0) (-(diagDir d))) := by
      ext g; simp [epP, diagG']
    rw [this]
    exact hDL.neg
  have hPair : Measurable[PotentialField.localSigma (leftOrthant d)]
      (fun g : PotentialField d => (epX g, epP g)) := by
    let _ : MeasurableSpace (PotentialField d) := PotentialField.localSigma (leftOrthant d)
    exact (show Measurable (fun g : PotentialField d => epX g) from hXL).prodMk hPL
  have hPair' : Measurable[PotentialField.localSigma (rightOrthant d)]
      (fun g : PotentialField d => (epY g, epQ g)) := by
    let _ : MeasurableSpace (PotentialField d) := PotentialField.localSigma (rightOrthant d)
    exact (show Measurable (fun g : PotentialField d => epY g) from hYR).prodMk
      (show Measurable (fun g : PotentialField d => epQ g) from hQR)
  have hXL' : Measurable[PotentialField.localSigma (leftOrthant d)] (fun g : PotentialField d => epX g) := hXL
  have hYR' : Measurable[PotentialField.localSigma (rightOrthant d)] (fun g : PotentialField d => epY g) := hYR
  constructor
  · exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hind hPair.comap_le) hYR'.comap_le
  · exact (indep_of_indep_of_le_right (indep_of_indep_of_le_left hind hXL'.comap_le) hPair'.comap_le).symm

end GMCExplicitDelta.Source
