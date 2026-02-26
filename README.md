# Osterwalder-Schrader Axioms for the Gaussian Free Field

We construct the massive Gaussian Free Field (GFF) in four spacetime dimensions
as a probability measure on the space of tempered distributions S'(ℝ⁴), and
prove that it satisfies all five
Osterwalder-Schrader axioms for a Euclidean quantum field theory. The construction
and proofs are formalized in Lean 4 / Mathlib, following the conventions and
methods of proof in Glimm and Jaffe, *Quantum Physics: A Functional Integral
Point of View* (Springer, 1987).

This repository also develops **dimension-agnostic** and **vector-valued** abstraction layers:

- a coordinate-free Euclidean time-direction API for OS-style reflection/translation,
- an abstract Gel'fand triple interface `N ⊂ H ⊂ N'` for Minlos/Gaussian measure theory,
- vector-valued Schwartz test functions `𝓢(E, V)` and weak-dual distribution spaces `WeakDual 𝕜 𝓢(E, V)`,
  with lifted global internal symmetries (constant gauge rotations / matrices) acting on fields.

## Master Theorem

```lean
theorem gaussianFreeField_satisfies_all_OS_axioms_proved (m : ℝ) [Fact (0 < m)] :
  SatisfiesAllOS (μ_GFF m)
```

For a bundled “model” interface (PhysLean-style), see `QFT.EuclideanQFT` and the packaged GFF model:

```lean
noncomputable def QFT.gaussianFreeField_EuclideanQFT_proved (m : ℝ) [Fact (0 < m)] :
  QFT.EuclideanQFT
```

**Status:** Version 1.0, February 2026. 0 sorries, 0 `axiom`s, ~32,000 lines of Lean across 47 files.

### Assumptions / hypotheses

The development packages the Schwartz nuclearity input as the predicate `SchwartzNuclearInclusion`
(a `Prop` implying `NuclearSpaceStd TestFunction`). In this repository it is discharged (via spacetime Hermite
coefficients), so the wrapper theorem `gaussianFreeField_satisfies_all_OS_axioms_proved` has no
additional hypotheses beyond `m > 0`.

| Hypothesis | Where used | Mathematical content |
|-----------|------------|---------------------|
| `OSforGFF.SchwartzNuclearInclusion` | `OSforGFF/GFFmaster.lean` (via `gaussianFreeField_satisfies_all_OS_axioms_of_schwartzNuclearInclusion`) | Nuclearity of the canonical Schwartz local Banach inclusions; this implies `NuclearSpaceStd TestFunction` and is used to descend the Kolmogorov Gaussian process to a probability measure on `S'(ℝ⁴)` |

In this repository, `SchwartzNuclearInclusion` is discharged in the spacetime Hermite model; see
[`OSforGFF/NuclearSpace/PhysHermiteSpaceTimeSchwartzNuclearInclusion.lean`](OSforGFF/NuclearSpace/PhysHermiteSpaceTimeSchwartzNuclearInclusion.lean).

The repository also contains an **optional hypothesis package** `OSforGFF/MinlosAxiomatic.lean` assuming the full Minlos theorem as a typeclass `MinlosTheorem`, but the proved GFF pipeline does **not** rely on it.

The measure-theoretic pipeline is factored through an abstract Gel'fand triple API in:

- [`OSforGFF/Minlos/GelfandTriple.lean`](OSforGFF/Minlos/GelfandTriple.lean)

and the proved GFF construction is provided as a concrete instance of that API in:

- [`OSforGFF/GFFMconstructProved.lean`](OSforGFF/GFFMconstructProved.lean)

## Project Structure

The library files are organized into layers, with imports flowing from
earlier to later sections. The dependency graph is in [dependency/import_graph.svg](dependency/import_graph.svg).

---

### 1. [General Mathematics](docs/01_general_mathematics.md)

Results that do not depend on any project-specific definitions. Pure extensions
of Mathlib.

#### Functional Analysis

| File | Contents |
|------|----------|
| [FunctionalAnalysis](OSforGFF/FunctionalAnalysis.lean) | L² Fourier transform infrastructure, Plancherel identity |
| [FrobeniusPositivity](OSforGFF/FrobeniusPositivity.lean) | Frobenius inner product, positive semidefinite matrix theory |
| [SchurProduct](OSforGFF/SchurProduct.lean) | Schur product theorem (Hadamard product preserves PSD) |
| [HadamardExp](OSforGFF/HadamardExp.lean) | Hadamard exponential of PD matrices is PD |
| [PositiveDefinite](OSforGFF/PositiveDefinite.lean) | Positive definite functions and kernels |
| [GaussianRBF](OSforGFF/GaussianRBF.lean) | Gaussian RBF kernel exp(-‖x-y‖²) is positive definite |

#### Schwartz Functions and Decay Estimates

| File | Contents |
|------|----------|
| [SchwartzTranslationDecay](OSforGFF/SchwartzTranslationDecay.lean) | Schwartz seminorm bounds under translation |
| [QuantitativeDecay](OSforGFF/QuantitativeDecay.lean) | Quantitative polynomial decay estimates |
| [L2TimeIntegral](OSforGFF/L2TimeIntegral.lean) | L² bounds for time integrals: Cauchy-Schwarz, Fubini, Minkowski |

#### Special Functions and Integrals

| File | Contents |
|------|----------|
| [LaplaceIntegral](OSforGFF/LaplaceIntegral.lean) | Laplace integral identity (Bessel K_{1/2}): ∫ s^{-1/2} e^{-a/s-bs} ds |
| [FourierTransforms](OSforGFF/FourierTransforms.lean) | 1D Fourier identities: Lorentzian ↔ exponential decay, triple Fubini reorder (no project imports) |
| [BesselFunction](OSforGFF/BesselFunction.lean) | Modified Bessel function K₁ via integral representation |

---

### 2. [Basic Definitions](docs/02_basic_definitions.md)

Core type definitions and infrastructure for the formalization.

#### Spacetime and Symmetries

| File | Contents |
|------|----------|
| [Basic](OSforGFF/Basic.lean) | SpaceTime (ℝ⁴), TestFunction, FieldConfiguration, distribution pairing, spatial geometry |
| [Spacetime/Defs](OSforGFF/Spacetime/Defs.lean) | Dimension-agnostic aliases for reference measure and Schwartz test functions |
| [Spacetime/TimeDirection](OSforGFF/Spacetime/TimeDirection.lean) | Coordinate-free time direction + reflection API for OS axioms |
| [Spacetime/VectorValued](OSforGFF/Spacetime/VectorValued.lean) | Vector-valued Schwartz/distribution spaces + lifted global internal symmetries |
| [Euclidean](OSforGFF/Euclidean.lean) | Euclidean group E(d) and its action on test functions |
| [DiscreteSymmetry](OSforGFF/DiscreteSymmetry.lean) | Time reflection Θ and discrete symmetries |
| [SpacetimeDecomp](OSforGFF/SpacetimeDecomp.lean) | Measure-preserving SpaceTime ≃ ℝ × ℝ³ decomposition |

#### Test Function Spaces

| File | Contents |
|------|----------|
| [ComplexTestFunction](OSforGFF/ComplexTestFunction.lean) | Complex-valued Schwartz test functions and conjugation |
| [PositiveTimeTestFunction_real](OSforGFF/PositiveTimeTestFunction_real.lean) | Subtype of test functions supported at positive time |
| [TimeTranslation](OSforGFF/TimeTranslation.lean) | Time translation operators T_s on Schwartz space (continuity proved) |

#### Schwartz Space Integration

| File | Contents |
|------|----------|
| [SchwartzProdIntegrable](OSforGFF/SchwartzProdIntegrable.lean) | Integrability of Schwartz function products |
| [SchwartzTonelli](OSforGFF/SchwartzTonelli.lean) | Tonelli/Fubini for Schwartz integrands on spacetime |

#### Generating Functionals

| File | Contents |
|------|----------|
| [Schwinger](OSforGFF/Schwinger.lean) | Generating functional Z[J] = ∫ e^{i⟨φ,J⟩} dμ, Schwinger functions |
| [SchwingerTwoPointFunction](OSforGFF/SchwingerTwoPointFunction.lean) | Two-point function S₂(x) as mollifier limit |

---

### 3. [Free Covariance](docs/03_free_covariance.md)

The free scalar field propagator C(x,y) = ∫ e^{ik·(x-y)}/(k²+m²) d⁴k/(2π)⁴
and its properties.

| File | Contents |
|------|----------|
| [CovarianceMomentum](OSforGFF/CovarianceMomentum.lean) | Momentum-space propagator 1/(k²+m²), decay bounds |
| [Parseval](OSforGFF/Parseval.lean) | Parseval identity: ⟨f,Cf⟩ = ∫\|f̂(k)\|² P(k) dk |
| [Covariance](OSforGFF/Covariance.lean) | Position-space covariance C(x,y), Euclidean invariance, bounds |
| [CovarianceR](OSforGFF/CovarianceR.lean) | Real covariance bilinear form, square root propagator embedding |

---

### 4. [Gaussian Measure Construction](docs/04_gaussian_measure.md)

Construction of the GFF probability measure on tempered distributions
via a proved **Kolmogorov + nuclear support** pipeline (finite-dimensional Gaussians
→ Kolmogorov extension on `TestFunction → ℝ` → a.s. support on `WeakDual` → pushforward).

| File | Contents |
|------|----------|
| [NuclearSpace/Std](OSforGFF/NuclearSpace/Std.lean) | Countable-seminorm nuclearity package (`NuclearSpaceStd`) |
| [NuclearSpace/Schwartz](OSforGFF/NuclearSpace/Schwartz.lean) | Canonical Schwartz seminorm sequence + gap packaged as `SchwartzNuclearInclusion` |
| [NuclearSpace/PhysHermiteSpaceTimeSchwartzNuclearInclusion](OSforGFF/NuclearSpace/PhysHermiteSpaceTimeSchwartzNuclearInclusion.lean) | Discharges `SchwartzNuclearInclusion` (hence `NuclearSpaceStd TestFunction`) via spacetime Hermite coefficients |
| [GaussianProcessKolmogorov](OSforGFF/GaussianProcessKolmogorov.lean) | Kolmogorov Gaussian process measure on `E → ℝ` |
| [MinlosGaussianSupportNuclearL2](OSforGFF/MinlosGaussianSupportNuclearL2.lean) | Nuclear `L²` support theorem + measurable modification into `WeakDual` |
| [MinlosGaussianProved](OSforGFF/MinlosGaussianProved.lean) | Pushforward to `WeakDual` + characteristic functional identity |
| [GFFMconstructProved](OSforGFF/GFFMconstructProved.lean) | Free GFF measure `gaussianFreeField_free_proved` via the proved pipeline |
| [GFFMconstruct](OSforGFF/GFFMconstruct.lean) | Front-facing wrapper: `μ_GFF` / integrability lemmas built on the proved construction |
| [GaussianMoments](OSforGFF/GaussianMoments.lean) | Gaussian moments: all n-point functions are integrable |
| [GFFIsGaussian](OSforGFF/GFFIsGaussian.lean) | Verification that GFF satisfies Gaussian moment conditions (see note below) |
| [GaussianFreeField](OSforGFF/GaussianFreeField.lean) | Main GFF assembly: μ_GFF m as a ProbabilityMeasure |

The repository also contains an **optional hypothesis package**
`OSforGFF/MinlosAxiomatic.lean` (Minlos theorem as a typeclass `MinlosTheorem`), but the proved GFF
pipeline does **not** rely on it.

**Note:** `GFFIsGaussian` imports `OS0` because it uses the proved analyticity of
Z[z₀f + z₁g] in ℂ² to identify the two-point function S₂(f,g) = C(f,g) via the
identity theorem. The derivative interchange lemma is from Mathlib; the dependency
is on the OS0 *result* (analyticity of the GFF generating functional), not on
OS0-specific infrastructure.

---

### 5. [OS Axiom Definitions](docs/05_os_axiom_definitions.md)

| File | Contents |
|------|----------|
| [OS_Axioms](OSforGFF/OS_Axioms.lean) | Formal Lean definitions of OS0 through OS4 (all formulations) |

---

### 6. [OS0 — Analyticity](docs/06_os0_analyticity.md)

The generating functional Z[∑ zⱼ Jⱼ] is analytic in the complex parameters zⱼ.

| File | Contents |
|------|----------|
| [OS0_GFF](OSforGFF/OS0_GFF.lean) | Proof via holomorphic integral theorem (differentiation under ∫) |

---

### 7. [OS1 — Regularity](docs/07_os1_regularity.md)

The generating functional satisfies exponential bounds |Z[f]| ≤ exp(c(‖f‖₁ + ‖f‖₂²)).

| File | Contents |
|------|----------|
| [OS1_GFF](OSforGFF/OS1_GFF.lean) | Proof via Fourier/momentum-space methods and Gaussian structure |

---

### 8. [OS2 — Euclidean Invariance](docs/08_os2_euclidean_invariance.md)

The measure μ is invariant under the Euclidean group E(4).

| File | Contents |
|------|----------|
| [OS2_GFF](OSforGFF/OS2_GFF.lean) | Proof via Euclidean invariance of the free covariance kernel |

---

### 9. [OS3 — Reflection Positivity](docs/09_os3_reflection_positivity.md)

For positive-time test functions f₁,...,fₙ and real coefficients c₁,...,cₙ:
∑ᵢⱼ cᵢcⱼ Z[fᵢ - Θfⱼ] ≥ 0.

The Schur-Hadamard theorem extends reflection positivity of the free covariance to the full generating functional. Mix of Fourier representation and Schwinger representation of the free covariance was used to prove Fubini theorems for exchanging order of integration.

| File | Contents |
|------|----------|
| [OS3_MixedRepInfra](OSforGFF/OS3_MixedRepInfra.lean) | Infrastructure: Schwinger and Fourier representation setup |
| [OS3_MixedRep](OSforGFF/OS3_MixedRep.lean) | Fubini theorems in the Fourier representation through the Schwinger pathway |
| [OS3_CovarianceRP](OSforGFF/OS3_CovarianceRP.lean) | Complete covariance reflection positivity |
| [OS3_GFF](OSforGFF/OS3_GFF.lean) | OS3 for GFF: Schur-Hadamard argument extends covariance positivity to Gaussian measure |

**Note on `CovarianceR`:** The real covariance bilinear form `freeCovarianceFormR` and its
algebraic properties (bilinearity, symmetry, continuity, positivity, square root embedding)
live in `CovarianceR` (Section 3), which has no OS3 dependency. The single reflection
positivity lemma `freeCovarianceFormR_reflection_nonneg` is inlined into `OS3_GFF`.

---

### 10. [OS4 — Clustering and Ergodicity](docs/10_os4_clustering_ergodicity.md)

Two equivalent formulations:
- **Clustering:** Z[f + T_a g] → Z[f]·Z[g] as |a| → ∞
- **Ergodicity:** (1/T)∫₀ᵀ A(T_s φ) ds → E[A] in L²(μ)

The proof establishes polynomial clustering with rate α = 6 (from the mass gap
in d = 3 spatial dimensions), then derives ergodicity via L² variance bounds.

| File | Contents |
|------|----------|
| [OS4_MGF](OSforGFF/OS4_MGF.lean) | Shared infrastructure: MGF formula, time translation duality, exponential bounds |
| [OS4_Clustering](OSforGFF/OS4_Clustering.lean) | Clustering proof via Gaussian factorization + covariance decay |
| [OS4_Ergodicity](OSforGFF/OS4_Ergodicity.lean) | Ergodicity proof via polynomial clustering → L² convergence |

---

### 11. [Master Theorem](docs/11_master_theorem.md)

| File | Contents |
|------|----------|
| [GFFmaster](OSforGFF/GFFmaster.lean) | Assembles OS0–OS4 into `gaussianFreeField_satisfies_all_OS_axioms` |

---

## Dependencies and Cross-Cutting Concerns

The import graph (`dependency/import_graph.svg`) is mostly layered, with one
cross-cutting dependency:

1. **GFFIsGaussian → OS0_GFF**: Gaussianity verification uses the OS0 analyticity result
   to identify S₂(f,g) = C(f,g) via the identity theorem (see Section 4 note)

This prevents a perfectly linear ordering but does not create a circular dependency.

## Building

```bash
lake build
```

Requires Lean 4 and Mathlib (pinned via `lake-manifest.json`).

## Planned Generalizations

1. Other spacetime dimensions, as discussed in [docs/dimension_dependence.md](docs/dimension_dependence.md)
2. Explicit construction of the measure not using Minlos

## Authors

Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim, Matteo Cipollina

### Coding Assistance

Claude Opus 4.6, Gemini 3 Pro, GPT-5.2 Codex

## License

This project is licensed under the Apache License, Version 2.0. See [LICENSE](LICENSE) for details.

## References

- Glimm, Jaffe: *Quantum Physics* (Springer, 1987), pp. 89–90
- Osterwalder, Schrader: *Axioms for Euclidean Green's functions* I & II (1973, 1975)
- Gel'fand, Vilenkin: *Generalized Functions*, Vol. 4 (Academic Press, 1964)
- Reed, Simon: *Methods of Modern Mathematical Physics*, Vol. II (1975)
