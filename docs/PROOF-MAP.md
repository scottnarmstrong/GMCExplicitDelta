# Proof map

The proof of the main theorems is organized in numbered steps. This page lists them, section by
section. Labels such as `G7` or `H5` in the docstrings of the library refer to this list. The
*Lean* column names the declaration of each step that is stated as a separate intermediate
statement (in `GMCExplicitDelta/Steps/`); the other steps are lemmas in the directories listed for
their section.


## §5. Source lemmas (S1–S10)

Lean files (under `GMCExplicitDelta/`): Source/, Statements/Source*.lean

| Step | Statement | Lean |
|---|---|---|
| S1 | Elementary consequences of the assumptions |  |
| S2 | Endpoint-strip exponential-square bound |  |
| S3 | All-even one-point proxy |  |
| S4 | Fourth and higher moment ratios |  |
| S5 | Diagonal covariance: $r\ge\pi^2s$ |  |
| S6 | Variance bound |  |
| S7 | $q=1$ moment generating function and $\tau^2$ |  |
| S8 | One-point band sums and grid maxima |  |
| S9 | Coefficientwise majorant for $h$ bands |  |
| S10 | Orlicz convexity for spatial remainders |  |

## §6. Coarse-graining identities (C1–C13)

Lean files (under `GMCExplicitDelta/`): Coarse/

| Step | Statement | Lean |
|---|---|---|
| C1 | Variational formulas and maximizers | `GMCExplicitDelta.Localization.frozenJ_eq_energy` |
| C2 | Subadditivity | `GMCExplicitDelta.Localization.frozenJ_le_cellJ` |
| C3 | Homogeneity and scaling of the pair |  |
| C4 | Order bounds, positivity, affine trial | `GMCExplicitDelta.Localization.frozenJ_nonneg`, `GMCExplicitDelta.Localization.integrable_cell` |
| C5 | Energy-to-mean inequalities |  |
| C6 | Spectral bound by the defect |  |
| C7 | Rescaled pairs and the map $\Phi$ |  |
| C8 | Isotropy of means and variances | `GMCExplicitDelta.Assembly.lintegral_frozenJ_eq_fMean`, `GMCExplicitDelta.Localization.integral_frozenJ_cell`, `GMCExplicitDelta.Localization.integral_cellRes_le` |
| C9 | Annealed normalization facts | `GMCExplicitDelta.Assembly.fMean_nonneg_antitone`, `GMCExplicitDelta.Localization.alphaBeta_ge_one_antitone` |
| C10 | Planar duality | `GMCExplicitDelta.Localization.alpha_eq_beta_planar` |
| C11 | Extension to translates, larger cubes, and monotone depth maxima |  |
| C12 | Old competitors for fresh comparisons |  |
| C13 | Positive quadratic forms and the PSD sphere inequality |  |

## §7. Normalization drift (N1–N3)

Lean files (under `GMCExplicitDelta/`): Proofs/Normalization/

| Step | Statement | Lean |
|---|---|---|
| N1 | Drift of the actual normalization | `GMCExplicitDelta.Assembly.normShift_drift` |
| N2 | Multiplicative decomposition with explicit drift |  |
| N3 | Fresh $q=1$ costs |  |

## §8. Haar norms, Neumann primitive, cutoff geometry (H1–H14)

Lean files (under `GMCExplicitDelta/`): Haar/, Proofs/HaarBlocks/, Proofs/ProjPoincare/, Proofs/PlanarBlock/, Proofs/Multiplier/, Proofs/HaarMode/

| Step | Statement | Lean |
|---|---|---|
| H1 | Triadic Haar decomposition and dual norms | `GMCExplicitDelta.Localization.haarPrimal_add_le`, `GMCExplicitDelta.Localization.energy_sub_projection_tendsto` |
| H2 | Neumann primitive | `GMCExplicitDelta.Localization.neumann_exists` |
| H3 | Neumann $H^2$ identity on the cube |  |
| H4 | Projected triadic Poincaré inequality, constant $5/54$ | `GMCExplicitDelta.Localization.projected_poincare` |
| H5 | Primitive on Haar blocks | `GMCExplicitDelta.Localization.neumann_block_bound` |
| H6 | Planar first Haar block | `GMCExplicitDelta.Localization.planar_first_block` |
| H7 | Plateau-cosine cutoff |  |
| H8 | Cell Poincaré inequality | `GMCExplicitDelta.Localization.cell_poincare` |
| H9 | Multiplier coefficients of the Haar blocks | `GMCExplicitDelta.Localization.haar_multiplier` |
| H10 | Exact constant mode | `GMCExplicitDelta.Localization.haar_constant_mode` |
| H11 | Haar summation of the localized test field | `GMCExplicitDelta.Localization.loc_H11` |
| H12 | Geometric tails and the Haar sums | `GMCExplicitDelta.Assembly.haarB_sums` |
| H13 | Localization weights | `GMCExplicitDelta.Localization.loc_weights` |
| H14 | Closed form of the geometric minimum series |  |

## §9. Mean-sensitive averaging and native caps (A1–A6)

Lean files (under `GMCExplicitDelta/`): Averaging/, Proofs/NativeCaps/

| Step | Statement | Lean |
|---|---|---|
| A1 | Centered moments and interpolation |  |
| A2 | Associated Stirling numbers |  |
| A3 | Mean-sensitive moment bound for averages |  |
| A4 | Norming constant for signed symmetric matrices |  |
| A5 | PSD matrix averaging with colors |  |
| A6 | Native caps of the frozen coefficient | `GMCExplicitDelta.Assembly.nativeCap_bound` |

## §10. Good event, descendant ellipticity, source history, bad charge (G1–G9)

Lean files (under `GMCExplicitDelta/`): HistoryLane/, Proofs/Observables/, Proofs/FineSensitivity/, Proofs/GridMax/, Proofs/BadResponse/

| Step | Statement | Lean |
|---|---|---|
| G1 | Descendant ellipticity on the good event | `GMCExplicitDelta.Localization.goodEvent_cell_bound`, `GMCExplicitDelta.Localization.loc_G1flux` |
| G2 | Splitting the statistic |  |
| G3 | Weighted sensitivity for transferred fine scales | `GMCExplicitDelta.Assembly.fineSensitivity` |
| G4 | Shifted one-point norms | `GMCExplicitDelta.Assembly.fineRatioNorms` |
| G5 | Fine source history |  |
| G6 | Whole-sum grid bound for subunit cells | `GMCExplicitDelta.Assembly.gridMax_norm_le` |
| G7 | Complete excess, uniform over later targets | `GMCExplicitDelta.Assembly.excess_bound` |
| G8 | Probability of the bad event | `GMCExplicitDelta.Assembly.badEvent_prob_le` |
| G9 | Bad response of the matched pairs | `GMCExplicitDelta.Assembly.badResponseBound_holds` |

## §11. Variance recurrence and budgets (V1–V5)

Lean files (under `GMCExplicitDelta/`): Contraction/, Proofs/Variance/

| Step | Statement | Lean |
|---|---|---|
| V1 | Initial variance bound (any finite $D$) | `GMCExplicitDelta.Assembly.varV_le_initial` |
| V2 | Centered decrement recurrence | `GMCExplicitDelta.Assembly.varV_le_centeredDecrement` |
| V3 | Parity colouring above the cutoff | `GMCExplicitDelta.Assembly.cellAvgVar_le_parity` |
| V4 | Finite-window variance budgets |  |
| V5 | Variance term of the summed inequality |  |

## §12. Localization and the per-scale contraction inequality (L1–L6)

Lean files (under `GMCExplicitDelta/`): Localization/, Proofs/LocWeights/, Proofs/WeightedLocalization/, Proofs/GradPieces/, Proofs/FluxBound/, Proofs/EnergyTest/, Proofs/CellMoments/, Proofs/AnnealedMeans/

| Step | Statement | Lean |
|---|---|---|
| L1 | Harmonic energy test | `GMCExplicitDelta.Localization.loc_pointwise`, `GMCExplicitDelta.Localization.loc_L1` |
| L2 | Gradient pieces on the good event | `GMCExplicitDelta.Localization.loc_L2_mean`, `GMCExplicitDelta.Localization.loc_L2_drop`, `GMCExplicitDelta.Localization.loc_L2_tail` |
| L3 | Weighted localization | `GMCExplicitDelta.Localization.loc_L3` |
| L4 | Localized first-moment inequality |  |
| L5 | Matched pairs |  |
| L6 | Normalized per-scale inequality | `GMCExplicitDelta.Assembly.perScaleIneq_holds` |

## §13. Terminal barrier and the all-λ planar test (T1–T4)

Lean files (under `GMCExplicitDelta/`): Contraction/, Proofs/Contraction/, Proofs/Scaling/

| Step | Statement | Lean |
|---|---|---|
| T1 | Finite-window telescopes | `GMCExplicitDelta.Assembly.terminal_lt_of_perScale` |
| T2 | Summed inequality under the terminal hypothesis |  |
| T3 | Barrier contradiction: terminal mean |  |
| T4 | Planar all-λ derivative test |  |

## §14. Fresh insertion and the band operator (I1–I10)

Lean files (under `GMCExplicitDelta/`): Insertion/, Proofs/FreshInsertion/, Proofs/FreshMean/

| Step | Statement | Lean |
|---|---|---|
| I1 | Old-competitor matrix |  |
| I2 | Hyperbolic generator |  |
| I3 | Conditional moment transfer with the band majorant |  |
| I4 | Properties and enclosure of the band operator | `GMCExplicitDelta.Contract.bandRow_eq_bandSeriesCoeff`, `GMCExplicitDelta.Contract.bandSeriesEval_eq_sum` |
| I5 | Old moment profile |  |
| I6 | Fresh norm return (unshifted) | `GMCExplicitDelta.Assembly.freshNorm_return` |
| I7 | Deterministic shift | `GMCExplicitDelta.Assembly.scaledDefect_shift_le` |
| I8 | Fresh mean return | `GMCExplicitDelta.Assembly.freshMean_return` |
| I9 | Application to the induction step |  |
| I10 | Proportional scaling of the fresh maps |  |

## §15. Seeds (K1–K3)

Lean files (under `GMCExplicitDelta/`): Proofs/FreshInsertion/, Proofs/Normalization/

| Step | Statement | Lean |
|---|---|---|
| K1 | Affine seed |  |
| K2 | Norm seed | `GMCExplicitDelta.Assembly.normSeed_bound` |
| K3 | Mean seed | `GMCExplicitDelta.Assembly.meanSeed_bound` |

## §16. Frozen step, induction, λ-scaling, proof of T0 (R1–R5)

Lean files (under `GMCExplicitDelta/`): Assembly/, Steps/, Proofs/Scaling/, StatementProofs/

| Step | Statement | Lean |
|---|---|---|
| R1 | Translates and larger cubes | `GMCExplicitDelta.Assembly.inductionBounds_extend` |
| R2 | Frozen step |  |
| R3 | Insertion step |  |
| R4 | Every smaller disorder | `GMCExplicitDelta.Assembly.badCharge_scale_le`, `GMCExplicitDelta.Assembly.barrier_scale_pos`, `GMCExplicitDelta.Assembly.freshReturns_scale_le` |
| R5 | Proof of the main theorem T0 | `GMCExplicitDelta.Contract.cascade_of_obligations`, `GMCExplicitDelta.Assembly.measurable_cascadeObservables` |

## Numeric obligations

The numeric conditions on the three certified rows (one rational row of parameters per dimension
`d = 2, 3, 4`) are the fields of `GMCExplicitDelta.Contract.Row.Obligations`
(`Contract/Obligations.lean`). They are proved for each row by kernel computation with exact
rational and natural-number arithmetic (`decide +kernel`), in `Certificates/` and `Numerics/`.
