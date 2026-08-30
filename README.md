# Osterwalder-Schrader Axioms for the Gaussian Free Field

We construct the massive Gaussian Free Field (GFF) as a probability measure on
the space of tempered distributions S'(ℝ^d), and prove that it satisfies all five
Osterwalder-Schrader axioms for a Euclidean quantum field theory. The construction
and proofs are formalized in Lean 4 / Mathlib, following the conventions and
methods of proof in Glimm and Jaffe, *Quantum Physics: A Functional Integral
Point of View* (Springer, 1987).

The library is **dimension-generic**: the spacetime dimension is a parameter
`d` (any `d ≥ 2`), and the only per-dimension input is the closed form of
the radial covariance profile, isolated behind the two-field typeclass
`GFFPropagator d m` (see [docs/dimension_generic.md](docs/dimension_generic.md)).
Four instances are provided in `OSforGFF/Instances/`: the four-dimensional Bessel
kernel (m/4π²r)K₁(mr), the three-dimensional Yukawa kernel e^{−mr}/(4πr), the
two-dimensional Bessel kernel (1/2π)K₀(mr), and the five-dimensional K_{3/2}
kernel (1+mr)e^{−mr}/(8π²r³).

## Master Theorem

```lean
theorem gaussianFreeField_satisfies_all_OS_axioms_generic
    {d : ℕ} [Fact (2 ≤ d)] (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] :
    SatisfiesAllOS (gaussianFreeField_free (d := d) m)

theorem gaussianFreeField_satisfies_all_OS_axioms_dim4 (m : ℝ) [Fact (0 < m)] :
    SatisfiesAllOS (μ_GFF 4 m)

theorem gaussianFreeField_satisfies_all_OS_axioms_dim3 (m : ℝ) [Fact (0 < m)] :
    SatisfiesAllOS (μ_GFF 3 m)

theorem gaussianFreeField_satisfies_all_OS_axioms_dim2 (m : ℝ) [Fact (0 < m)] :
    SatisfiesAllOS (μ_GFF 2 m)

theorem gaussianFreeField_satisfies_all_OS_axioms_dim5 (m : ℝ) [Fact (0 < m)] :
    SatisfiesAllOS (μ_GFF 5 m)
```

where `SatisfiesAllOS` bundles OS0 (analyticity), OS1 (regularity), OS2
(Euclidean invariance), OS3 (reflection positivity), OS4 (clustering) and OS4
(ergodicity). The four `_dim4`/`_dim3`/`_dim2`/`_dim5` theorems are the closed-form
instances (Bessel K₁, Yukawa, K₀, K_{3/2}) of the first; the corollary
`gaussianFreeField_satisfies_all_OS_axioms_of_dim` covers every `d ≥ 2` via the
canonical proper-time propagator: the OS3 proper-time Fubini domination runs at
boundary-vanishing order `d`, so no upper bound on the dimension is needed.

[![CI](https://github.com/mrdouglasny/OSforGFF/actions/workflows/ci.yml/badge.svg)](https://github.com/mrdouglasny/OSforGFF/actions/workflows/ci.yml)

**Status:** Version 3.2 (general dimension `d ≥ 2`), August 2026. 0 sorries, 0 axioms, ~31,500 lines of Lean across 54 files. Instances for `d = 2, 3, 4, 5`; the axiom footprint and statement type of every headline theorem (generic, all-dimensions `d ≥ 2`, `d = 4`, `d = 3`, `d = 2`, `d = 5`) are build-frozen in `OSforGFF/Guardrails.lean`.

All results are fully proved — no assumed axioms. Nuclear space structure and the Minlos theorem
are provided by the external libraries [bochner](https://github.com/mrdouglasny/bochner) and
[gaussian-field](https://github.com/mrdouglasny/gaussian-field), which are themselves axiom-free.
The Minlos proof uses the external library [kolmogorov_extension4](https://github.com/remydegenne/kolmogorov_extension4).

## Project Structure

The 53 on-graph library files (plus 6 off-graph `Legacy/` files, below) are organized into 7 layers, with imports flowing from
earlier to later sections. See [docs/architecture.md](docs/architecture.md) for dependency structure,
design choices, and proof outlines, and [docs/dimension_generic.md](docs/dimension_generic.md)
for the dimension-generic design. For a pedagogical, axiom-by-axiom walkthrough of the
OS proofs — ordered by complexity, with pointers into the code — see
[docs/pedagogical/Overview.md](docs/pedagogical/Overview.md). The dependency graph source is in
[dependency/import_graph.dot](dependency/import_graph.dot) (render with `dot -Tsvg`).

---

### 1. General Mathematics — `OSforGFF/General/`

Pure extensions of Mathlib with no project-specific definitions.

| File | Contents |
|------|----------|
| [FunctionalAnalysis](OSforGFF/General/FunctionalAnalysis.lean) | [L² Fourier transform infrastructure, Plancherel identity](summary/OSforGFF/General/FunctionalAnalysis.md) |
| [SchurProduct](OSforGFF/General/SchurProduct.lean) | [Schur product theorem (Hadamard product preserves PSD)](summary/OSforGFF/General/SchurProduct.md) |
| [HadamardExp](OSforGFF/General/HadamardExp.lean) | [Entrywise exponential of PSD matrices is PSD](summary/OSforGFF/General/HadamardExp.md) |
| [PositiveDefinite](OSforGFF/General/PositiveDefinite.lean) | [Positive definite functions and kernels](summary/OSforGFF/General/PositiveDefinite.md) |
| [GaussianRBF](OSforGFF/General/GaussianRBF.lean) | [Gaussian RBF kernel exp(-‖x-y‖²) is positive definite](summary/OSforGFF/General/GaussianRBF.md) |
| [FourierTransforms](OSforGFF/General/FourierTransforms.lean) | [1D Fourier identities: Lorentzian ↔ exponential decay](summary/OSforGFF/General/FourierTransforms.md) |
| [LaplaceIntegral](OSforGFF/General/LaplaceIntegral.lean) | [Laplace integral identity (Bessel K_{1/2}): ∫ s^{-1/2} e^{-a/s-bs} ds](summary/OSforGFF/General/LaplaceIntegral.md) |
| [BesselFunction](OSforGFF/General/BesselFunction.lean) | [The modified Bessel function K₁ via its cosh integral representation (def only; the analytic lemmas are in `Legacy/`)](summary/OSforGFF/General/BesselFunction.md) |
| [BesselK0](OSforGFF/General/BesselK0.lean) | [The modified Bessel function K₀ via its cosh integral representation (def only)](summary/OSforGFF/General/BesselK0.md) |
| [BesselK](OSforGFF/General/BesselK.lean) | [The modified Bessel function K_ν of arbitrary order and the master Schwinger identity ∫ t^{ν−1} e^{−m²t−r²/4t} dt = 2(r/2m)^ν K_ν(mr); the K₀/K₁ evaluations and K_{1/2} are corollaries](summary/OSforGFF/General/BesselK.md) |
| [QuantitativeDecay](OSforGFF/General/QuantitativeDecay.lean) | [Schwartz bilinear forms with exponentially decaying kernels have polynomial decay](summary/OSforGFF/General/QuantitativeDecay.md) |
| [SchwartzTranslationDecay](OSforGFF/General/SchwartzTranslationDecay.lean) | [Schwartz seminorm bounds under translation](summary/OSforGFF/General/SchwartzTranslationDecay.md) |
| [L2TimeIntegral](OSforGFF/General/L2TimeIntegral.lean) | [L² bounds for time integrals: Cauchy-Schwarz, Fubini, Minkowski](summary/OSforGFF/General/L2TimeIntegral.md) |

---

### 2. Spacetime — `OSforGFF/Spacetime/`

Test functions, symmetries, and integration infrastructure.

| File | Contents |
|------|----------|
| [Basic](OSforGFF/Spacetime/Basic.lean) | [SpaceTime (ℝ^d), SchwartzTestFunction, FieldConfiguration, distribution pairing](summary/OSforGFF/Spacetime/Basic.md) |
| [Euclidean](OSforGFF/Spacetime/Euclidean.lean) | [Euclidean group E(d) = ℝ^d ⋊ O(d) and its action on test functions](summary/OSforGFF/Spacetime/Euclidean.md) |
| [DiscreteSymmetry](OSforGFF/Spacetime/DiscreteSymmetry.lean) | [Time reflection Θ: (t,x̄) ↦ (−t,x̄)](summary/OSforGFF/Spacetime/DiscreteSymmetry.md) |
| [Decomposition](OSforGFF/Spacetime/Decomposition.lean) | [Measure-preserving SpaceTime ≃ ℝ × ℝ^{d−1} decomposition](summary/OSforGFF/Spacetime/Decomposition.md) |
| [ComplexTestFunction](OSforGFF/Spacetime/ComplexTestFunction.lean) | [Complex-valued Schwartz test functions and conjugation](summary/OSforGFF/Spacetime/ComplexTestFunction.md) |
| [PositiveTimeTestFunction](OSforGFF/Spacetime/PositiveTimeTestFunction.lean) | [Subtype of test functions supported at positive time](summary/OSforGFF/Spacetime/PositiveTimeTestFunction.md) |
| [TimeTranslation](OSforGFF/Spacetime/TimeTranslation.lean) | [Time translation operators T_s on Schwartz space](summary/OSforGFF/Spacetime/TimeTranslation.md) |
| [ProdIntegrable](OSforGFF/Spacetime/ProdIntegrable.lean) | [Integrability of Schwartz function products](summary/OSforGFF/Spacetime/ProdIntegrable.md) |
| [Tonelli](OSforGFF/Spacetime/Tonelli.lean) | [Tonelli/Fubini for Schwartz integrands on spacetime](summary/OSforGFF/Spacetime/Tonelli.md) |

---

### 3. Schwinger — `OSforGFF/Schwinger/`

Generating functionals and correlation functions.

| File | Contents |
|------|----------|
| [Defs](OSforGFF/Schwinger/Defs.lean) | [Generating functional Z[J] = ∫ e^{i⟨φ,J⟩} dμ, Schwinger n-point functions](summary/OSforGFF/Schwinger/Defs.md) |
| [TwoPoint](OSforGFF/Schwinger/TwoPoint.lean) | [Two-point function S₂(x) as mollifier limit](summary/OSforGFF/Schwinger/TwoPoint.md) |
| [GaussianMoments](OSforGFF/Schwinger/GaussianMoments.lean) | [Gaussian moments: all n-point functions are integrable](summary/OSforGFF/Schwinger/GaussianMoments.md) |

---

### 4. Covariance — `OSforGFF/Covariance/`

The free scalar field propagator C(x,y) = Cprofile(|x−y|), isolated behind the
`GFFPropagator d m` typeclass and analyzed through its proper-time (Schwinger)
representation, uniformly in the dimension.

| File | Contents |
|------|----------|
| [Propagator](OSforGFF/Covariance/Propagator.lean) | [The `GFFPropagator` typeclass, proper-time covariance, engine lemmas (L¹, decay, Fourier transform)](summary/OSforGFF/Covariance/Propagator.md) |
| [ParsevalGeneric](OSforGFF/Covariance/ParsevalGeneric.lean) | [Parseval identity ⟨f,Cf̄⟩ = ∫\|f̂(k)\|² P(k) dk, positivity, invariances, centered-kernel decay](summary/OSforGFF/Covariance/ParsevalGeneric.md) |
| [RealForm](OSforGFF/Covariance/RealForm.lean) | [Real covariance bilinear form, square root propagator embedding](summary/OSforGFF/Covariance/RealForm.md) |

---

### 5. Measure — `OSforGFF/Measure/`

Construction of the GFF probability measure via the Minlos theorem.

| File | Contents |
|------|----------|
| [NuclearSpace](OSforGFF/Measure/NuclearSpace.lean) | [Schwartz space is Hilbert-nuclear and separable (bridges bochner + gaussian-field)](summary/OSforGFF/Measure/NuclearSpace.md) |
| [Minlos](OSforGFF/Measure/Minlos.lean) | [Minlos theorem application, Gaussian measure construction](summary/OSforGFF/Measure/Minlos.md) |
| [MinlosAnalytic](OSforGFF/Measure/MinlosAnalytic.lean) | [Symmetry and moments for Gaussian measures (sign-flip invariance, zero mean)](summary/OSforGFF/Measure/MinlosAnalytic.md) |
| [Construct](OSforGFF/Measure/Construct.lean) | [GFF measure construction: covariance → characteristic functional → μ](summary/OSforGFF/Measure/Construct.md) |
| [IsGaussian](OSforGFF/Measure/IsGaussian.lean) | [Verification that S₂(f,g) = C(f,g) via OS0 derivative interchange](summary/OSforGFF/Measure/IsGaussian.md) |
| [GaussianFreeField](OSforGFF/Measure/GaussianFreeField.lean) | [Main GFF assembly: gaussianFreeField_free m as a ProbabilityMeasure](summary/OSforGFF/Measure/GaussianFreeField.md) |

**Note:** `IsGaussian` imports `OS0_Analyticity` because it uses the proved analyticity of
Z[z₀f + z₁g] to identify S₂(f,g) = C(f,g) via the identity theorem. The dependency
is on the OS0 *result*, not on OS0-specific infrastructure.

---

### 6. OS Axioms — `OSforGFF/OS/`

Axiom definitions, individual proofs, and master theorem.

| File | Contents |
|------|----------|
| [Axioms](OSforGFF/OS/Axioms.lean) | [Formal Lean definitions of OS0 through OS4](summary/OSforGFF/OS/Axioms.md) |
| [OS0_Analyticity](OSforGFF/OS/OS0_Analyticity.lean) | [Closed-form Z[f] = exp(-½ C(f,f)) via identity theorem + Fernique](summary/OSforGFF/OS/OS0_Analyticity.md) |
| [OS1_Regularity](OSforGFF/OS/OS1_Regularity.lean) | [Plancherel + momentum-space bound: \|Z[f]\| ≤ exp(‖f‖²/2m²)](summary/OSforGFF/OS/OS1_Regularity.md) |
| [OS2_Invariance](OSforGFF/OS/OS2_Invariance.lean) | [C(x,y) depends only on \|x−y\|, Lebesgue measure invariance](summary/OSforGFF/OS/OS2_Invariance.md) |
| [OS3_MixedRepInfra](OSforGFF/OS/OS3_MixedRepInfra.lean) | [Schwinger parametrization and Fubini theorems for absolute integrability](summary/OSforGFF/OS/OS3_MixedRepInfra.md) |
| [OS3_MixedRep](OSforGFF/OS/OS3_MixedRep.lean) | [Mixed representation via Schwinger → heat kernel → Laplace transform](summary/OSforGFF/OS/OS3_MixedRep.md) |
| [OS3_CovarianceRP](OSforGFF/OS/OS3_CovarianceRP.lean) | [Covariance reflection positivity: ⟨Θf, Cf⟩ = ∫ (1/ω)\|F_ω\|² ≥ 0](summary/OSforGFF/OS/OS3_CovarianceRP.md) |
| [OS3_ReflectionPositivity](OSforGFF/OS/OS3_ReflectionPositivity.lean) | [Schur–Hadamard lifts covariance RP to generating functional](summary/OSforGFF/OS/OS3_ReflectionPositivity.md) |
| [OS4_MGF](OSforGFF/OS/OS4_MGF.lean) | [Shared infrastructure: MGF formula, time translation duality](summary/OSforGFF/OS/OS4_MGF.md) |
| [OS4_Clustering](OSforGFF/OS/OS4_Clustering.lean) | [Gaussian factorization + convolution decay lemma (domain split at ‖y‖=‖x‖/2)](summary/OSforGFF/OS/OS4_Clustering.md) |
| [OS4_Ergodicity](OSforGFF/OS/OS4_Ergodicity.lean) | [Polynomial clustering (α=6) → L² convergence](summary/OSforGFF/OS/OS4_Ergodicity.md) |
| [NonTrivial](OSforGFF/OS/NonTrivial.lean) | [Nontriviality: C(f,f) > 0, positive variance, UV divergence C(x,y) → ∞](summary/OSforGFF/OS/NonTrivial.md) — deliberately off the root import graph; compiled by `scripts/check-guardrails.sh`, not `lake build` |
| [Master](OSforGFF/OS/Master.lean) | [Assembles OS0–OS4 into the generic master theorem and its 4D, 3D, and 2D instances](summary/OSforGFF/OS/Master.md) |

---

### 7. Instances — `OSforGFF/Instances/`

Per-dimension closed forms of the covariance, packaged as `GFFPropagator` instances.

| File | Contents |
|------|----------|
| [Dim4](OSforGFF/Instances/Dim4.lean) | [The `GFFPropagator 4 m` instance: Bessel kernel (m/4π²r)K₁(mr) via the order ν=−1 case of the master identity (schwingerIntegral_eq_besselK1), plus the live 4D kernel `freeCovariance4`](summary/OSforGFF/Instances/Dim4.md) |
| [Dim3](OSforGFF/Instances/Dim3.lean) | [The `GFFPropagator 3 m` instance: Yukawa kernel e^{−mr}/(4πr) via the order ν=−1/2 case of the master identity (besselK_half), and the UV divergence](summary/OSforGFF/Instances/Dim3.md) |
| [Dim2](OSforGFF/Instances/Dim2.lean) | [The `GFFPropagator 2 m` instance: Bessel kernel (1/2π)K₀(mr) via the order-zero case of the master identity in `General/BesselK`](summary/OSforGFF/Instances/Dim2.md) |
| [Dim5](OSforGFF/Instances/Dim5.lean) | [The `GFFPropagator 5 m` instance: K_{3/2} kernel (1+mr)e^{−mr}/(8π²r³) via the order ν=−3/2 case of the master identity (besselK_three_half by Gaussian moments)](summary/OSforGFF/Instances/Dim5.md) |

### Legacy (off the build graph)

`OSforGFF/Legacy/` preserves genuine proven mathematics that the on-graph library no longer
consumes: the original four-dimensional development superseded in role by the dimension-generic
machinery, and the verified-dead declarations quarantined by the library-wide sweep. These files
are **not** imported by `OSforGFF.lean` and are not compiled by `lake build`; each carries a
module docstring with its supersession map, and is verified in isolation with `lake env lean`
(build `BesselK1Analytics`'s olean first, since `Dim4Bessel` depends on it).

| File | Description |
| --- | --- |
| [Legacy/Dim4Bessel](OSforGFF/Legacy/Dim4Bessel.lean) | The original 4D Bessel/momentum program: the named Bessel kernel `freeCovarianceBessel`/`freeCovariance4`, regulated-covariance / Fubini / momentum-space development, heat-kernel and Schwinger-representation defs, superseded by `Covariance/Propagator.lean` + `Covariance/ParsevalGeneric.lean` + `General/BesselK.lean` |
| [Legacy/BesselK1Analytics](OSforGFF/Legacy/BesselK1Analytics.lean) | The K₁ analytic lemmas (positivity, continuity, asymptotic/near-origin bounds, radial integrability) that supported the 4D analysis |
| [Legacy/UnusedGeneral](OSforGFF/Legacy/UnusedGeneral.lean) | Consumer-less general-analysis lemmas (Fourier/functional-analysis side lemmas, the entire former `FrobeniusPositivity.lean`, the L² time-average and weighted-Minkowski programs) |
| [Legacy/UnusedSpacetime](OSforGFF/Legacy/UnusedSpacetime.lean) | Consumer-less spacetime-layer declarations (Schwartz multiplication, spatial L², the matrix presentation of time reflection, unified Euclidean actions, openness of the positive-time set) |
| [Legacy/UnusedMeasureSchwinger](OSforGFF/Legacy/UnusedMeasureSchwinger.lean) | Consumer-less measure/Schwinger-layer declarations (the alternative `OS0_alt` program, RBF/symmetry Minlos corollaries, the exponential-series expansion of the generating functional) |
| [Legacy/UnusedOS](OSforGFF/Legacy/UnusedOS.lean) | Consumer-less OS-layer declarations (OS0 side lemmas, pre-H3 OS3 chain steps incl. `bilinear_to_k0_inside`, the ε–δ clustering formulation, kernel isometry invariance) |

---

## External Libraries

We depend on three auxiliary Lean libraries for nuclear space theory and measure construction.
All are axiom-free.

### [bochner](https://github.com/mrdouglasny/bochner) (BochnerMinlos)

| Module | What we use | Imported by |
|--------|-------------|-------------|
| `Minlos.Main` | `minlos_theorem` — existence and uniqueness of probability measures from characteristic functionals on nuclear spaces | [Minlos](OSforGFF/Measure/Minlos.lean) |
| `Minlos.NuclearSpace` | `IsHilbertNuclear` typeclass; `MeasurableSpace (WeakDual ℝ E)` cylinder σ-algebra instance | [Basic](OSforGFF/Spacetime/Basic.lean), [NuclearSpace](OSforGFF/Measure/NuclearSpace.lean) |
| `Minlos.PietschBridge` | `isHilbertNuclear_of_nuclear` — bridge from Pietsch to Hilbert-Schmidt characterization | [NuclearSpace](OSforGFF/Measure/NuclearSpace.lean) |
| `Bochner.PositiveDefinite` | `IsPositiveDefinite` structure for characteristic functionals | [Minlos](OSforGFF/Measure/Minlos.lean) |

### [gaussian-field](https://github.com/mrdouglasny/gaussian-field) (GaussianField)

| Module | What we use | Imported by |
|--------|-------------|-------------|
| `SchwartzNuclear.HermiteNuclear` | `schwartz_separableSpace` — Schwartz space is separable (via Hermite basis) | [NuclearSpace](OSforGFF/Measure/NuclearSpace.lean) |
| `Nuclear.NuclearSpace` | `DyninMityaginSpace` → `NuclearSpace` — proves Schwartz space is nuclear | [NuclearSpace](OSforGFF/Measure/NuclearSpace.lean) |

### [kolmogorov_extension4](https://github.com/remydegenne/kolmogorov_extension4) (transitive, via bochner)

| Module | What we use | Imported by |
|--------|-------------|-------------|
| `KolmogorovExtension4.KolmogorovExtension` | `projectiveLimit` — Kolmogorov extension theorem: constructs a measure on the infinite product from a consistent projective family of finite-dimensional measures | bochner's `Minlos.ProjectiveFamily` |

## Dependencies and Cross-Cutting Concerns

The import graph (`dependency/import_graph.dot`) is mostly layered, with one
cross-cutting dependency:

1. **IsGaussian → OS0_Analyticity**: Gaussianity verification uses the OS0 analyticity result
   to identify S₂(f,g) = C(f,g) via the identity theorem (see Section 5 note)

This prevents a perfectly linear ordering but does not create a circular dependency.

## Building

```bash
lake build
```

Requires Lean 4 and Mathlib (pinned via `lake-manifest.json`). The build also compiles
[`OSforGFF/Guardrails.lean`](OSforGFF/Guardrails.lean), whose `#guard_msgs` blocks freeze the
axiom footprint and statement type of all six headline theorems (generic, all-dimensions
`d ≥ 2`, and `d = 4, 3, 2, 5`) — so `lake build` fails if any change introduces a new axiom,
leaks a `sorry`, or alters a headline statement.

A companion `scripts/check-guardrails.sh` checks the same invariant at the source level, without
needing a build:

```bash
./scripts/check-guardrails.sh          # exit 0 = clean, exit 2 = violation
```

It scans every module reachable from `OSforGFF.lean` for `axiom` declarations, `sorry`/`admit`,
and kernel escape hatches (`native_decide`, `unsafe`, `implemented_by`, `extern`), stripping
comments first so prose that merely names them is not a false positive. The check is absolute
rather than relative to a baseline revision, so it cannot silently pass by losing its reference
point; set `GUARDRAIL_BASE=<rev>` to additionally report which violations a given range
introduced. `OSforGFF/Legacy/` is exempt — it is deliberately off the import graph and never
compiled.

Both checks run in CI on every push and pull request ([`.github/workflows/ci.yml`](.github/workflows/ci.yml)),
which also replays the built environment through an external kernel check (`leanchecker`).

## Related Work

- [or4nge19/OSforGFF](https://github.com/or4nge19/OSforGFF) — A fork by Matteo Cipollina pursuing a different measure construction pipeline: finite-dimensional Gaussians → Kolmogorov extension on test functions → nuclear support → pushforward to distribution space, avoiding the Minlos theorem. Develops coordinate-free Euclidean time-direction and dimension-agnostic Hermite APIs.

## Planned Generalizations

1. ~~The `d = 2` instance (the K₀ kernel (1/2π)K₀(mr))~~ — Done. The `d = 2` (K₀), `d = 3` (Yukawa), and `d = 4` (Bessel) instances are all provided, completing the dimensions discussed in [docs/dimension_dependence.md](docs/dimension_dependence.md).
2. ~~Explicit construction of the measure not using Minlos~~ — Done. The Minlos theorem and Kolmogorov extension are now fully proved in [bochner](https://github.com/mrdouglasny/bochner) and [kolmogorov_extension4](https://github.com/remydegenne/kolmogorov_extension4).
3. ~~General dimension `d ≥ 2`~~ — Done. The OS3 Fubini domination now runs at boundary-vanishing order `d` (positive-time test functions are flat to all orders at the time boundary), so the OS theorems hold in **every** dimension `d ≥ 2`; the program and its implementation are written up in [docs/general_dimension.md](docs/general_dimension.md).

## Authors

Sergey A. Cherkis, Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim

### Coding Assistance

Claude Opus 4.6, Gemini 3 Pro, GPT-5.2 Codex

## License

This project is licensed under the Apache License, Version 2.0. See [LICENSE](LICENSE) for details.

## References

- Glimm, Jaffe: *Quantum Physics* (Springer, 1987), pp. 89–90
- Osterwalder, Schrader: *Axioms for Euclidean Green's functions* I & II (1973, 1975)
- Gel'fand, Vilenkin: *Generalized Functions*, Vol. 4 (Academic Press, 1964)
- Reed, Simon: *Methods of Modern Mathematical Physics*, Vol. II (1975)
- Degenne, Pfaffelhuber: *Formalizing the Kolmogorov Extension Theorem in Lean* ([kolmogorov_extension4](https://github.com/remydegenne/kolmogorov_extension4))
