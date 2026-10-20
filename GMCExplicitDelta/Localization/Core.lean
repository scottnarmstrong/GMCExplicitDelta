module

public import GMCExplicitDelta.Steps.LocalizationPieces
public import GMCExplicitDelta.Steps.LocalizationModel
public import GMCExplicitDelta.Localization.Basic
public import GMCExplicitDelta.Proofs.Contraction.Haar

/-!
# The pointwise localized inequality from its pieces

`loc_pointwise_assembled` proves the statement of the target `loc_pointwise`
(`Targets/LocalizationCore.lean`) from the deterministic pieces of `Targets/LocalizationPieces.lean`,
the model facts C2, C4 and the Haar tail bound of H12 (`Haar.Tg_le`, via `Assembly.haar_majorants`):

1. `loc_weights`: weights `w_R ≤ φ` on the depth-`ν` cells with average `≥ c_ν`;
2. `loc_L3`: `avg_R w_R J(R) ≤ (1+ε)/2 𝒲 + (1+ε⁻¹)(J_ν - J_0)`;
3. `loc_L1`, `loc_G1flux`, `loc_H11`: `𝒲² ≤ K_s(b∇v)²P_s((v-v̄)𝐠)² ≤ 2RJ_0 (∑_k b_k‖D_k∇v‖)²`;
4. `loc_L2_mean`, `loc_L2_drop` for `k ≤ K`, `loc_L2_tail` (with `y_k ≤ Rq_s^k`) for `k > K ≥ g`:
   `∑_k b_k‖D_k∇v‖ ≤ X + √(2RJ_0) T_g` (`tsum_haar_le`), `X = haarSum`;
5. hence `𝒲 ≤ √(2RJ_0) X + 2RT_g J_0`, and the claim.
-/

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

namespace GMCExplicitDelta.Localization

open Assembly Contract

variable {d : ℕ}

/-- The shifted tail `∑_i b_{i+K+1}u_s^{i+K+1}` is at most `T_g` for `K ≥ g` (as `ℝ≥0∞` series). -/
theorem tsum_tail_le_Tg (row : Row d) (hO : row.Obligations) {K : ℕ} (hK : row.g ≤ K) :
    ∑' i, ENNReal.ofReal (row.haarB (i + (K + 1)) * row.us ^ (i + (K + 1))) ≤
      ENNReal.ofReal row.Tg := by
  obtain ⟨⟨hq1, hq9, _⟩, hL, hH⟩ := haar_majorants row hO
  obtain ⟨hsum, -⟩ := Haar.Tg_le row hq1 hq9 hO.geo2.2 hL hH
  have hus : 0 ≤ row.us := (Haar.us_pos row).le
  let f : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal (row.haarB (row.g + 1 + j) * row.us ^ (row.g + 1 + j))
  have hinj : Function.Injective (fun i : ℕ => i + (K - row.g)) :=
    fun i j hij => by simpa using hij
  have heq : ∀ i, ENNReal.ofReal (row.haarB (i + (K + 1)) * row.us ^ (i + (K + 1))) =
      f (i + (K - row.g)) := by
    intro i
    have : row.g + 1 + (i + (K - row.g)) = i + (K + 1) := by omega
    simp only [f, this]
  have hT : ∑' j, f j = ENNReal.ofReal row.Tg := by
    show ∑' j, f j = ENNReal.ofReal
      (∑' k : ℕ, row.haarB (row.g + 1 + k) * row.us ^ (row.g + 1 + k))
    rw [ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg (haarB_nonneg' row _)
      (pow_nonneg hus _)) hsum]
  calc ∑' i, ENNReal.ofReal (row.haarB (i + (K + 1)) * row.us ^ (i + (K + 1))) =
      ∑' i, f (i + (K - row.g)) := tsum_congr heq
    _ ≤ ∑' j, f j := ENNReal.tsum_comp_le_tsum_of_injective hinj f
    _ = ENNReal.ofReal row.Tg := hT

/-- One summand of the tail of the Haar series. -/
theorem haar_tail_term_le (row : Row d) {N : ℕ → ℝ} {A : ℝ} (hA : 0 ≤ A) {K : ℕ}
    (hhigh : ∀ k, K < k → N k ≤ row.us ^ k * A) (i : ℕ) :
    ENNReal.ofReal (row.haarB (i + (K + 1)) * N (i + (K + 1))) ≤
      ENNReal.ofReal A * ENNReal.ofReal (row.haarB (i + (K + 1)) * row.us ^ (i + (K + 1))) := by
  rw [← ENNReal.ofReal_mul hA]
  refine ENNReal.ofReal_le_ofReal ?_
  have h := hhigh (i + (K + 1)) (by omega)
  calc row.haarB (i + (K + 1)) * N (i + (K + 1)) ≤
      row.haarB (i + (K + 1)) * (row.us ^ (i + (K + 1)) * A) :=
        mul_le_mul_of_nonneg_left h (haarB_nonneg' row _)
    _ = A * (row.haarB (i + (K + 1)) * row.us ^ (i + (K + 1))) := by ring

/-- The tail of the Haar series beyond `K ≥ g`. -/
theorem haar_tail_le (row : Row d) (hO : row.Obligations) {K : ℕ} (hK : row.g ≤ K)
    {N : ℕ → ℝ} {A : ℝ} (hA : 0 ≤ A) (hhigh : ∀ k, K < k → N k ≤ row.us ^ k * A) :
    ∑' i, ENNReal.ofReal (row.haarB (i + (K + 1)) * N (i + (K + 1))) ≤
      ENNReal.ofReal (A * row.Tg) := by
  calc ∑' i, ENNReal.ofReal (row.haarB (i + (K + 1)) * N (i + (K + 1))) ≤
      ∑' i, ENNReal.ofReal A *
        ENNReal.ofReal (row.haarB (i + (K + 1)) * row.us ^ (i + (K + 1))) :=
        ENNReal.tsum_le_tsum (haar_tail_term_le row hA hhigh)
    _ = ENNReal.ofReal A *
        ∑' i, ENNReal.ofReal (row.haarB (i + (K + 1)) * row.us ^ (i + (K + 1))) :=
        ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal A * ENNReal.ofReal row.Tg := by
        gcongr
        exact tsum_tail_le_Tg row hO hK
    _ = ENNReal.ofReal (A * row.Tg) := (ENNReal.ofReal_mul hA).symm

/-- **Splitting the Haar series at `K ≥ g`.** If `N_k ≤ B_k` for `k ≤ K` and `N_k ≤ u_s^k A` for
`k > K`, then `∑_k b_k N_k ≤ ∑_{k≤K} b_k B_k + A T_g` (as `ℝ≥0∞` series). -/
theorem tsum_haar_le (row : Row d) (hO : row.Obligations) {K : ℕ} (hK : row.g ≤ K)
    {N B : ℕ → ℝ} {A : ℝ} (hA : 0 ≤ A) (hN0 : ∀ k, 0 ≤ N k)
    (hlow : ∀ k ≤ K, N k ≤ B k) (hhigh : ∀ k, K < k → N k ≤ row.us ^ k * A) :
    ∑' k, ENNReal.ofReal (row.haarB k * N k) ≤
      ENNReal.ofReal (∑ k ∈ Finset.range (K + 1), row.haarB k * B k + A * row.Tg) := by
  have hmem : ∀ k ∈ Finset.range (K + 1), k ≤ K := fun k hk =>
    Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hB0 : ∀ k ∈ Finset.range (K + 1), 0 ≤ row.haarB k * B k := fun k hk =>
    mul_nonneg (haarB_nonneg' row k) ((hN0 k).trans (hlow k (hmem k hk)))
  have hsplit : ∑ k ∈ Finset.range (K + 1), ENNReal.ofReal (row.haarB k * N k) +
      ∑' i, ENNReal.ofReal (row.haarB (i + (K + 1)) * N (i + (K + 1))) =
      ∑' k, ENNReal.ofReal (row.haarB k * N k) :=
    ENNReal.summable.sum_add_tsum_nat_add'
  have hfirst : ∑ k ∈ Finset.range (K + 1), ENNReal.ofReal (row.haarB k * N k) ≤
      ENNReal.ofReal (∑ k ∈ Finset.range (K + 1), row.haarB k * B k) := by
    rw [ENNReal.ofReal_sum_of_nonneg hB0]
    exact Finset.sum_le_sum fun k hk => ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (hlow k (hmem k hk)) (haarB_nonneg' row k))
  calc ∑' k, ENNReal.ofReal (row.haarB k * N k) =
      ∑ k ∈ Finset.range (K + 1), ENNReal.ofReal (row.haarB k * N k) +
        ∑' i, ENNReal.ofReal (row.haarB (i + (K + 1)) * N (i + (K + 1))) := hsplit.symm
    _ ≤ ENNReal.ofReal (∑ k ∈ Finset.range (K + 1), row.haarB k * B k) +
        ENNReal.ofReal (A * row.Tg) := add_le_add hfirst (haar_tail_le row hO hK hA hhigh)
    _ = _ := (ENNReal.ofReal_add (Finset.sum_nonneg hB0) (mul_nonneg hA (Tg_nonneg row))).symm

theorem incNorm_nonneg (Q : Homogenization.TriadicCube d) (k : ℕ)
    (G : Homogenization.Vec d → Homogenization.Vec d) : 0 ≤ incNorm Q k G :=
  Real.sqrt_nonneg _

/-- `cellRes` at depth `0` with centre `0` is `|-p + Y_{Q_n}q|²`. -/
theorem cellRes_zero (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    (p q : Homogenization.Vec d) (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    cellRes M L n 0 p q 0 ω = vecNormSq (-p + (frozenY M L (cubeAt 0 n) ω).mulVec q) := by
  rw [cellRes, descendantsAverage_eq]
  simp [descendantsAtDepth, cubeAt, cellAt]

/-- `cellJ` at depth `0` is `J(Q_n)`. -/
theorem cellJ_zero (M : SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    (p q : Homogenization.Vec d) (ω : SubdiffusiveProcess.Model.PotentialSample d) :
    cellJ M L n 0 p q ω = frozenJ M L (cubeAt 0 n) p q ω := by
  rw [cellJ, descendantsAverage_eq]
  simp [descendantsAtDepth, cubeAt, cellAt]

/-- The cube cutoff is continuous (`φ_ω` is `C¹`). -/
theorem continuous_cubeCutoff (row : Row d) (hO : row.Obligations) (n : ℕ) :
    Continuous (cubeCutoff row n) := by
  have hp := (Haar.cutoffProfile_contDiff (omegaEff_le row hO)).continuous
  have e : cubeCutoff row n =
      fun x => ∏ i, Haar.cutoffProfile row.omegaEff (x i / (3 : ℝ) ^ n) := rfl
  rw [e]
  exact continuous_finsetProd _ fun j _ => hp.comp ((continuous_apply j).div_const _)

/-- `φ ≤ 1` on `Q_n`. -/
theorem cubeCutoff_le_one (row : Row d) (hO : row.Obligations) (n : ℕ)
    {x : Homogenization.Vec d} (hx : x ∈ cubeSet (originCube d (n : ℤ))) :
    cubeCutoff row n x ≤ 1 := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hy : ∀ j, |x j / (3 : ℝ) ^ n| ≤ 1 / 2 := by
    intro j
    have hj := (mem_cubeSet_originCube_iff.mp hx) j
    rw [abs_div, abs_of_pos h3, div_le_iff₀ h3, abs_le]
    simp only [zpow_natCast] at hj
    constructor <;> linarith [hj.1, hj.2]
  exact (Haar.cutoffProduct_bounds (omegaEff_pos row hO) (omegaEff_le row hO) _ hy).2

/-- **The pointwise localized inequality**, assembled from the deterministic pieces. -/
theorem loc_pointwise_assembled (row : Row d) (hd : d ∈ ({2, 3, 4} : Finset ℕ))
    (hO : row.Obligations) (M : SubdiffusiveProcess.Model.GMCModel d) (L n K : ℕ)
    (hK : row.g ≤ K) :
    ∃ w : Homogenization.TriadicCube d → ℝ, (∀ R, 0 ≤ w R ∧ w R ≤ 1) ∧
      row.cNu ≤ descendantsAverage (originCube d (n : ℤ)) row.nu w ∧
      ∀ ω ∈ goodEvent row M L 0 n, ∀ p q : Homogenization.Vec d, ∀ c : ℕ → Homogenization.Vec d,
        c 0 = 0 →
        cellJw M L n row.nu w p q ω ≤
          locBound row (frozenJ M L (cubeAt 0 n) p q ω) (cellJ M L n row.nu p q ω)
            (haarSum row M L n K p q c ω) := by
  obtain ⟨w, hw, hcw, hwφ⟩ := loc_weights row hd hO n
  refine ⟨w, hw, hcw, fun ω hω p q c hc0 => ?_⟩
  have hRpos := R_pos row hO
  have hεpos := epsilon_pos row hO
  set Q := originCube d (n : ℤ) with hQ
  set J0 := frozenJ M L (cubeAt 0 n) p q ω with hJ0
  have hJ0nn : 0 ≤ J0 := frozenJ_nonneg M L _ p q ω
  set v := frozenH1 M L (cubeAt 0 n) p q ω with hv
  set N : ℕ → ℝ := fun k => incNorm Q k v.grad with hN
  set A := Real.sqrt (2 * (row.R : ℝ) * J0) with hA
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hAsq : A ^ 2 = 2 * (row.R : ℝ) * J0 := Real.sq_sqrt (by positivity)
  set X := haarSum row M L n K p q c ω with hX
  set B : ℕ → ℝ := fun k => Real.sqrt (2 * row.yk k * (cellJ M L n k p q ω - J0)) +
    Real.sqrt (cellRes M L n k p q (c k) ω) with hB
  have hXB : X = ∑ k ∈ Finset.range (K + 1), row.haarB k * B k := rfl
  -- (1) L3 with the weights below the cutoff
  have h3 := loc_L3 M L n row.nu ω p q hεpos (cubeCutoff row n)
    (continuous_cubeCutoff row hO n).measurable (fun x hx => cubeCutoff_le_one row hO n hx)
    w hw hwφ
  -- (2) the Haar series of the gradient
  have hlow : ∀ k ≤ K, N k ≤ B k := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · have hm := loc_L2_mean M L n ω p q
      have e0 : N 0 = Real.sqrt (cellRes M L n 0 p q (c 0) ω) := by
        rw [hc0, cellRes_zero, ← hm, Real.sqrt_sq (incNorm_nonneg _ _ _)]
      rw [e0]
      exact le_add_of_nonneg_left (Real.sqrt_nonneg _)
    · exact loc_L2_drop row hd hO M L n ω hω p q (c k) k hk1
  have hhigh : ∀ k, K < k → N k ≤ row.us ^ k * A := by
    intro k hk
    have ht := loc_L2_tail row hd hO M L n ω hω p q k (by omega)
    have hR1 : (1 : ℝ) ≤ (row.R : ℝ) := by exact_mod_cast hO.par2.1.le
    have hy := Haar.yk_le row hR1 (haar_majorants row hO).1.1.le k
    have hsq : N k ^ 2 ≤ (row.us ^ k * A) ^ 2 := by
      rw [mul_pow, hAsq, ← pow_mul, mul_comm k 2, pow_mul, ← Haar.qs_eq_us_sq]
      calc N k ^ 2 ≤ 2 * row.yk k * J0 := ht
        _ ≤ 2 * ((row.R : ℝ) * row.qs ^ k) * J0 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hy (by norm_num)) hJ0nn
        _ = _ := by ring
    exact (pow_le_pow_iff_left₀ (Real.sqrt_nonneg _)
      (mul_nonneg (pow_nonneg (Haar.us_pos row).le k) hA0) (by norm_num)).mp hsq
  have hT := tsum_haar_le row hO hK hA0 (fun k => Real.sqrt_nonneg _) hlow hhigh
  -- (3) L1, G1(c), H11
  have h1 := loc_L1 row hd hO M L n ω p q
  have hG := loc_G1flux row hd hO M L n ω hω p q
  have hsub : openCubeSet Q ⊆ ((cubeAt 0 n : Ch02.Domain d) : Set (Homogenization.Vec d)) := by
    intro x hx
    show x ∈ translateSet 0 (openCubeSet Q)
    simpa using hx
  have hH := loc_H11 row hd hO n (v.restrict (isOpen_openCubeSet Q) hsub)
  have hW2 : ENNReal.ofReal (locEnergy row M L n p q ω) ^ 2 ≤
      ENNReal.ofReal ((A * (X + A * row.Tg)) ^ 2) := by
    calc ENNReal.ofReal (locEnergy row M L n p q ω) ^ 2 ≤
        ENNReal.ofReal (2 * (row.R : ℝ) * J0) *
          (∑' k, ENNReal.ofReal (row.haarB k * N k)) ^ 2 := h1.trans (mul_le_mul' hG hH)
      _ ≤ ENNReal.ofReal (2 * (row.R : ℝ) * J0) *
          ENNReal.ofReal (X + A * row.Tg) ^ 2 := by
          gcongr
          rw [hXB]
          exact hT
      _ = ENNReal.ofReal ((A * (X + A * row.Tg)) ^ 2) := by
          have hX0 : 0 ≤ X + A * row.Tg := add_nonneg
            (Finset.sum_nonneg fun k _ => mul_nonneg (haarB_nonneg' row k) (by positivity))
            (mul_nonneg hA0 (Tg_nonneg row))
          rw [← ENNReal.ofReal_pow hX0, ← ENNReal.ofReal_mul (by positivity), mul_pow, hAsq]
  have hW : locEnergy row M L n p q ω ≤ A * (X + A * row.Tg) := by
    have hrhs : 0 ≤ A * (X + A * row.Tg) := mul_nonneg hA0 (add_nonneg
      (Finset.sum_nonneg fun k _ => mul_nonneg (haarB_nonneg' row k) (by positivity))
      (mul_nonneg hA0 (Tg_nonneg row)))
    rcases le_or_gt (locEnergy row M L n p q ω) 0 with hle | hpos
    · exact hle.trans hrhs
    · rw [← ENNReal.ofReal_pow hpos.le, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hW2
      exact (pow_le_pow_iff_left₀ hpos.le hrhs (by norm_num)).mp hW2
  -- (4) conclude
  have hε' : 0 ≤ (1 + (row.epsilon : ℝ)) / 2 := by positivity
  calc cellJw M L n row.nu w p q ω ≤
      (1 + (row.epsilon : ℝ)) / 2 * locEnergy row M L n p q ω +
        (1 + (row.epsilon : ℝ)⁻¹) * (cellJ M L n row.nu p q ω - J0) := h3
    _ ≤ (1 + (row.epsilon : ℝ)) / 2 * (A * (X + A * row.Tg)) +
        (1 + (row.epsilon : ℝ)⁻¹) * (cellJ M L n row.nu p q ω - J0) := by
        gcongr
    _ = locBound row J0 (cellJ M L n row.nu p q ω) X := by
        rw [locBound, ← hA]
        have : A * (X + A * row.Tg) = A * X + 2 * (row.R : ℝ) * row.Tg * J0 := by
          rw [mul_add, ← mul_assoc, ← pow_two, hAsq]
          ring
        rw [this]

end GMCExplicitDelta.Localization
