# Explicit constants for the GMC coarse-graining cascade

[![Build and verify](https://github.com/scottnarmstrong/GMCExplicitDelta/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/scottnarmstrong/GMCExplicitDelta/actions/workflows/build.yml)
[![Comparators](https://github.com/scottnarmstrong/GMCExplicitDelta/actions/workflows/comparators.yml/badge.svg?branch=main)](https://github.com/scottnarmstrong/GMCExplicitDelta/actions/workflows/comparators.yml)

This repository is built on top of
[subdiffusive-process](https://github.com/nitromannitol/subdiffusive-process), the Lean 4
formalization of

> Scott Armstrong, Ahmed Bou-Rabee and Tuomo Kuusi,
> *Anomalous scaling limit of a Brownian particle in a log-correlated potential*
> (preprint forthcoming).

The results of that paper are perturbative: they hold when the disorder strength `δ` of the
log-correlated potential is small enough, `δ ≤ δ₀`. The paper, and its formalization, prove that
such a `δ₀` and the accompanying constants exist, but do not compute them. The heart of the argument is a renormalization (coarse-graining) cascade: an
induction across scales showing that, for every infrared cutoff `m`, the cutoff coefficient `a_m`
normalized by its homogenized coefficient `ā_m` is close to the identity on every cube above the
cutoff scale, with an error of order `δ²`.

**The point of this repository is to exhibit explicit values for the perturbative parameter and the
constants in this cascade estimate.** We prove, in Lean, that it holds for

- `δ ≤ 0.36665` in dimension `d = 2`,
- `δ ≤ 0.18870` in dimension `d = 3`,
- `δ ≤ 0.15698` in dimension `d = 4`,

with explicit rational constants (table below). In particular, in two dimensions the cascade holds
for every disorder strength up to `δ = 0.366`.

The theorems are stated about the objects of subdiffusive-process itself, which is imported as a
pinned Lake dependency: the model, the cutoff coefficient, its homogenized coefficient, the response
functional `J` and the normalized defect are all the dependency's definitions.

## What is proved

The random potential is a sum of independent smooth random fields `γ₀, γ₁, γ₂, …`, where `γₖ` is a
copy of `γ₀` stretched by the factor `3ᵏ`; the size of the fluctuations is set by the *disorder
strength* `δ`. Keeping the first `m + 1` fields gives the mean-one *cutoff coefficient*

> `a_m(x) = exp(Σ_{k=0}^{m} (γₖ(x) − τ²))`,  `τ² = log 𝔼 exp(γ₀(0))`

(`SubdiffusiveProcess.Model.aCutoff`), and `ā_m` (`SubdiffusiveProcess.CoarseGrainingVocab.ahom`) is
its homogenized (effective) coefficient. A model is an element of
`SubdiffusiveProcess.Model.GMCModel d`: a probability law on the sequence of fields together with the
standing assumptions: independent layers with exact scaling, stationarity, finite range of
dependence, an exponential-square bound at scale `δ ≤ 1/2` on the field and its first two
derivatives, invariance under signed permutations and sign change, and a positive one-point
exponential moment.

The coarse-graining cascade compares `a_m/ā_m` with the identity on every cube `z + Q_n` of side
`3ⁿ ≥ 3ᵐ`. It is measured by two quantities:

- the *directional energy* `J(U, ā_m^{-1/2} e, ā_m^{1/2} e; a_m)` for a Euclidean unit vector `e`,
  where `J(U, p, q; a)` is the response functional of the coarse-graining theory of Armstrong and Kuusi
  (`SubdiffusiveProcess.CoarseGrainingVocab.J`, the response functional `Ch02.responseJ` of CoarseGraining);
- the *normalized defect* `Jmax_m(U)`, the supremum of the directional energy over unit vectors `e`
  (`SubdiffusiveProcess.CoarseGrainingVocab.normalizedDefect`); it is the operator norm of the matrix
  `½(𝐚(U) + 𝐚_*(U)⁻¹) − I` built from the coarse-grained matrices of `a_m/ā_m` on `U`.

**Theorem.** Let `d ∈ {2, 3, 4}` and let `δ*`, `C₃₂`, `C_mean` be given by the table below. For every
model with disorder strength `δ ≤ δ*`, every cutoff `m`, every `n ≥ m`, every `z ∈ ℝᵈ` and every
Euclidean unit vector `e`, the normalized defect `Jmax_m(z + Q_n)` and the directional energy are
measurable functions of the environment, and

- `‖Jmax_m(z + Q_n)‖_{L³²} ≤ C₃₂ δ²`,
- `𝔼 J(z + Q_n, ā_m^{-1/2} e, ā_m^{1/2} e; a_m) ≤ C_mean δ²`.

| `d` | `δ*` | `C₃₂` | `C_mean` |
|---|---|---|---|
| 2 | `0.36665` | `23138371504/53772889 ≈ 430.30` | `230590996/53772889 ≈ 4.288` |
| 3 | `0.18870` | `89475125/1186923 ≈ 75.384` | `17849411/3560769 ≈ 5.013` |
| 4 | `0.15698` | `5918767600/61606801 ≈ 96.073` | `423596800/61606801 ≈ 6.876` |

The bounds are uniform in the cutoff `m`. They make explicit, at the moment `32`, the
coarse-graining estimate on which the renormalization argument of the paper rests; they do not make
explicit the thresholds of the paper's main theorems, which use further steps.

The three theorems are `GMCExplicitDelta.explicit_cascade_two`, `explicit_cascade_three` and
`explicit_cascade_four`, in [`GMCExplicitDelta/Statements/`](GMCExplicitDelta/Statements/). The
statement in dimension two reads:

```lean
theorem explicit_cascade_two (M : SubdiffusiveProcess.Model.GMCModel 2)
    (hδ : M.delta ≤ 36665 / 100000) (m n : ℕ) (hmn : m ≤ n) (z : Homogenization.Vec 2) :
    Measurable (normalizedDefect M m
        (SubdiffusiveProcess.LambdaStability.translatedDomain z (originCube 2 (n : ℤ)))) ∧
    paperENNRealLpNorm M.P.toMeasure 32
        (normalizedDefect M m
          (SubdiffusiveProcess.LambdaStability.translatedDomain z (originCube 2 (n : ℤ)))) ≤
      ENNReal.ofReal (23138371504 / 53772889 * M.delta ^ 2) ∧
    ∀ e : Homogenization.Vec 2, vecNormSq e = 1 →
      Measurable (fun ω => J (SubdiffusiveProcess.LambdaStability.translatedDomain z (originCube 2 (n : ℤ)))
          (aCutoffCoeffOnData M m ω
            (SubdiffusiveProcess.LambdaStability.translatedDomain z (originCube 2 (n : ℤ)))).toCoeffOn
          ((Real.sqrt (ahom M m))⁻¹ • e) (Real.sqrt (ahom M m) • e)) ∧
      ∫⁻ ω, ENNReal.ofReal
          (J (SubdiffusiveProcess.LambdaStability.translatedDomain z (originCube 2 (n : ℤ)))
            (aCutoffCoeffOnData M m ω
              (SubdiffusiveProcess.LambdaStability.translatedDomain z
                (originCube 2 (n : ℤ)))).toCoeffOn
            ((Real.sqrt (ahom M m))⁻¹ • e) (Real.sqrt (ahom M m) • e)) ∂M.P.toMeasure ≤
        ENNReal.ofReal (230590996 / 53772889 * M.delta ^ 2) :=
```

`import GMCExplicitDelta` loads the three theorems.

## Guarantees

- The library contains no `sorry`, no `admit` and no custom axiom. The three theorems depend only on
  `propext`, `Classical.choice` and `Quot.sound` (see [Building and verifying](#building-and-verifying)).
- No `native_decide`: the numerical inequalities are checked by the Lean kernel, by `decide +kernel`
  on exact rational and natural-number arithmetic combined with rational bounds on the
  transcendental constants that occur (`π`, `e`, `log 2`, square roots and Gamma values).
- A Mathlib-only restatement of the three theorems, with every notion defined in a single file, is
  checked against the library with [comparator](https://github.com/leanprover/comparator); see
  [`GMCExplicitDeltaAudit/`](GMCExplicitDeltaAudit/).

## How the proof is organized

The proof follows a strong induction on the cutoff `m`. At each step the coefficient is frozen at
cutoff `L`, a per-scale contraction inequality is derived by localization with Haar-type norms on
triadic cubes, the contraction is summed across scales against a terminal barrier, and fresh
layers are inserted with a band operator that controls their moments. The induction runs with
caps `D` and `F` at the threshold `δ*`, and a scaling argument transfers the bounds to every
`δ ≤ δ*` with `C₃₂ = D/δ*²` and `C_mean = F/δ*²`.

The library separates the analysis from the numerics:

- `GMCExplicitDelta.Contract.cascade_of_obligations` (in [`Steps/CascadeOfObligations.lean`](GMCExplicitDelta/Steps/CascadeOfObligations.lean)):
  for any row of rational parameters in dimension `d ∈ {2, 3, 4}` that satisfies the numeric
  conditions `Row.Obligations`, the cascade bounds hold for `δ ≤ δ*` with `C₃₂ = D/δ*²` and
  `C_mean = F/δ*²`.
- `rowTwo_obligations`, `rowThree_obligations`, `rowFour_obligations`
  (in [`Steps/RowObligations.lean`](GMCExplicitDelta/Steps/RowObligations.lean)): the three certified
  rows satisfy their obligations, proved by kernel computation in
  [`Certificates/`](GMCExplicitDelta/Certificates/).
- The proofs in [`StatementProofs/`](GMCExplicitDelta/StatementProofs/) combine the two.

[`docs/PROOF-MAP.md`](docs/PROOF-MAP.md) lists the steps of the proof (labels such as `G7` or `H5`
in the docstrings) with the Lean declarations that state them.

## Repository layout

| Path | Contents |
|---|---|
| `GMCExplicitDelta/Statements/` | the three main theorems and three moment bounds for the source field |
| `GMCExplicitDelta/StatementProofs/` | their proofs |
| `GMCExplicitDelta/Contract/` | rows of parameters, derived constants, numeric obligations |
| `GMCExplicitDelta/Certificates/`, `Numerics/` | the numeric obligations, checked by the kernel |
| `GMCExplicitDelta/Steps/`, `Assembly/` | intermediate statements and the induction |
| `GMCExplicitDelta/Proofs/` | proofs of the intermediate statements, by topic |
| `GMCExplicitDelta/Source/`, `Coarse/`, `Haar/`, `Averaging/`, `Localization/`, `HistoryLane/`, `Insertion/`, `Contraction/` | the supporting theory |
| `GMCExplicitDeltaAudit/` | the comparator challenge, its solution and the axiom audit |

## Building and verifying

Install [elan](https://github.com/leanprover/elan). The toolchain is pinned in
[`lean-toolchain`](lean-toolchain) (Lean `v4.35.0-rc2`) and the dependency in
[`lake-manifest.json`](lake-manifest.json): subdiffusive-process at
`4c6b8fa60357a07fd5713e5104a6cc70f8e432dc`, with its own pinned dependencies (CoarseGraining,
MarkovProcess and Mathlib).

```bash
lake exe cache get   # prebuilt Mathlib
lake build           # the dependencies and every module of the library
```

The source dependencies have no prebuilt cache and are compiled on the first build. A few
certificate modules (`GMCExplicitDelta.Certificates.Group4*`) each need about 12 GB of memory; on a
machine with less memory, build them one at a time first, in the order used by the
[build workflow](.github/workflows/build.yml).

To print the axioms of the main theorems and of the comparator solution:

```bash
lake build GMCExplicitDeltaAudit
lake env lean GMCExplicitDeltaAudit/AxiomsAudit.lean
```

To run the comparator check (Linux; `landrun` and `nanoda_bin` on the `PATH`; the NanoDa replay
needs about 16 GB of memory):

```bash
scripts/verify_comparator.sh
```

## Authors, citation, acknowledgements

The Lean development is by **Scott Armstrong**, **Ahmed Bou-Rabee** and **Tuomo Kuusi**. To cite it,
use [`CITATION.cff`](CITATION.cff). Scott Armstrong and Tuomo Kuusi were supported by the European
Research Council (ERC) under the European Union's Horizon Europe research and innovation programme,
grant agreement No. 101200828.

## License

The Lean development is licensed under the Apache License 2.0; see [`LICENSE`](LICENSE).
