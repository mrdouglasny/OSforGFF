# Osterwalder-Schrader Axioms for the Gaussian Free Field

We construct the massive Gaussian Free Field (GFF) in four spacetime dimensions
as a probability measure on the space of tempered distributions S'(ℝ⁴), and
prove that it satisfies all five
Osterwalder-Schrader axioms for a Euclidean quantum field theory. The construction
and proofs are formalized in Lean 4 / Mathlib, following the conventions and
methods of proof in Glimm and Jaffe, *Quantum Physics: A Functional Integral
Point of View* (Springer, 1987).

## Master Theorem

```lean
theorem gaussianFreeField_satisfies_all_OS_axioms (m : ℝ) [Fact (0 < m)] :
  OS0_Analyticity (μ_GFF m) ∧
  OS1_Regularity (μ_GFF m) ∧
  OS2_EuclideanInvariance (μ_GFF m) ∧
  OS3_ReflectionPositivity (μ_GFF m) ∧
  OS4_Clustering (μ_GFF m) ∧
  OS4_Ergodicity (μ_GFF m)
```

**Status:** Version 1.0, February 2026. 0 sorries, 3 assumed axioms (see below), ~32,000 lines of Lean across 47 files.

### Assumed Axioms

| Axiom | File | Mathematical content |
|-------|------|---------------------|
| [`schwartz_nuclear`](OSforGFF/Measure/NuclearSpace.lean) | [NuclearSpace](OSforGFF/Measure/NuclearSpace.lean) | Schwartz space is nuclear (Treves, Ch. 51) |
| [`minlos_theorem`](OSforGFF/Measure/Minlos.lean) | [Minlos](OSforGFF/Measure/Minlos.lean) | Minlos theorem: nuclear char. functional → unique measure (Gel'fand-Vilenkin IV) |
| [`differentiable_analyticAt_finDim`](OSforGFF/OS/OS0_Analyticity.lean) | [OS0_Analyticity](OSforGFF/OS/OS0_Analyticity.lean) | Hartogs' theorem in n dimensions: ℂ-differentiable implies analytic |

## Project Structure

The 47 library files are organized into 6 layers, with imports flowing from
earlier to later sections. See [docs/architecture.md](docs/architecture.md) for dependency structure,
design choices, and proof outlines. The dependency graph is in [dependency/import_graph.svg](dependency/import_graph.svg).

---

### 1. General Mathematics — `OSforGFF/General/`

Pure extensions of Mathlib with no project-specific definitions.

| File | Contents |
|------|----------|
| [FunctionalAnalysis](OSforGFF/General/FunctionalAnalysis.lean) | L² Fourier transform infrastructure, Plancherel identity |
| [FrobeniusPositivity](OSforGFF/General/FrobeniusPositivity.lean) | Frobenius inner product, positive semidefinite matrix theory |
| [SchurProduct](OSforGFF/General/SchurProduct.lean) | Schur product theorem (Hadamard product preserves PSD) |
| [HadamardExp](OSforGFF/General/HadamardExp.lean) | Entrywise exponential of PSD matrices is PSD |
| [PositiveDefinite](OSforGFF/General/PositiveDefinite.lean) | Positive definite functions and kernels |
| [GaussianRBF](OSforGFF/General/GaussianRBF.lean) | Gaussian RBF kernel exp(-‖x-y‖²) is positive definite |
| [FourierTransforms](OSforGFF/General/FourierTransforms.lean) | 1D Fourier identities: Lorentzian ↔ exponential decay |
| [LaplaceIntegral](OSforGFF/General/LaplaceIntegral.lean) | Laplace integral identity (Bessel K_{1/2}): ∫ s^{-1/2} e^{-a/s-bs} ds |
| [BesselFunction](OSforGFF/General/BesselFunction.lean) | Modified Bessel function K₁ via integral representation |
| [QuantitativeDecay](OSforGFF/General/QuantitativeDecay.lean) | Schwartz bilinear forms with exponentially decaying kernels have polynomial decay |
| [SchwartzTranslationDecay](OSforGFF/General/SchwartzTranslationDecay.lean) | Schwartz seminorm bounds under translation |
| [L2TimeIntegral](OSforGFF/General/L2TimeIntegral.lean) | L² bounds for time integrals: Cauchy-Schwarz, Fubini, Minkowski |

---

### 2. Spacetime — `OSforGFF/Spacetime/`

Test functions, symmetries, and integration infrastructure.

| File | Contents |
|------|----------|
| [Basic](OSforGFF/Spacetime/Basic.lean) | SpaceTime (ℝ⁴), TestFunction, FieldConfiguration, distribution pairing |
| [Euclidean](OSforGFF/Spacetime/Euclidean.lean) | Euclidean group E(4) = ℝ⁴ ⋊ O(4) and its action on test functions |
| [DiscreteSymmetry](OSforGFF/Spacetime/DiscreteSymmetry.lean) | Time reflection Θ: (t,x̄) ↦ (−t,x̄) |
| [Decomposition](OSforGFF/Spacetime/Decomposition.lean) | Measure-preserving SpaceTime ≃ ℝ × ℝ³ decomposition |
| [ComplexTestFunction](OSforGFF/Spacetime/ComplexTestFunction.lean) | Complex-valued Schwartz test functions and conjugation |
| [PositiveTimeTestFunction](OSforGFF/Spacetime/PositiveTimeTestFunction.lean) | Subtype of test functions supported at positive time |
| [TimeTranslation](OSforGFF/Spacetime/TimeTranslation.lean) | Time translation operators T_s on Schwartz space |
| [ProdIntegrable](OSforGFF/Spacetime/ProdIntegrable.lean) | Integrability of Schwartz function products |
| [Tonelli](OSforGFF/Spacetime/Tonelli.lean) | Tonelli/Fubini for Schwartz integrands on spacetime |

---

### 3. Schwinger — `OSforGFF/Schwinger/`

Generating functionals and correlation functions.

| File | Contents |
|------|----------|
| [Defs](OSforGFF/Schwinger/Defs.lean) | Generating functional Z[J] = ∫ e^{i⟨φ,J⟩} dμ, Schwinger n-point functions |
| [TwoPoint](OSforGFF/Schwinger/TwoPoint.lean) | Two-point function S₂(x) as mollifier limit |
| [GaussianMoments](OSforGFF/Schwinger/GaussianMoments.lean) | Gaussian moments: all n-point functions are integrable |

---

### 4. Covariance — `OSforGFF/Covariance/`

The free scalar field propagator C(x,y) = (m/4π²|x−y|) K₁(m|x−y|) and its properties.

| File | Contents |
|------|----------|
| [Momentum](OSforGFF/Covariance/Momentum.lean) | Momentum-space propagator 1/(k²+m²), decay bounds |
| [Parseval](OSforGFF/Covariance/Parseval.lean) | Parseval identity: ⟨f,Cf⟩ = ∫\|f̂(k)\|² P(k) dk |
| [Position](OSforGFF/Covariance/Position.lean) | Position-space covariance, Euclidean invariance, Schwinger representation |
| [RealForm](OSforGFF/Covariance/RealForm.lean) | Real covariance bilinear form, square root propagator embedding |

---

### 5. Measure — `OSforGFF/Measure/`

Construction of the GFF probability measure via the Minlos theorem.

| File | Contents |
|------|----------|
| [NuclearSpace](OSforGFF/Measure/NuclearSpace.lean) | Nuclear space definition (Hilbert-Schmidt embedding characterization) |
| [Minlos](OSforGFF/Measure/Minlos.lean) | Minlos theorem (axiom), Gaussian measure construction |
| [MinlosAnalytic](OSforGFF/Measure/MinlosAnalytic.lean) | Symmetry and moments for Gaussian measures (sign-flip invariance, zero mean) |
| [Construct](OSforGFF/Measure/Construct.lean) | GFF measure construction: covariance → characteristic functional → μ |
| [IsGaussian](OSforGFF/Measure/IsGaussian.lean) | Verification that S₂(f,g) = C(f,g) via OS0 derivative interchange |
| [GaussianFreeField](OSforGFF/Measure/GaussianFreeField.lean) | Main GFF assembly: μ_GFF m as a ProbabilityMeasure |

**Note:** `IsGaussian` imports `OS0_Analyticity` because it uses the proved analyticity of
Z[z₀f + z₁g] to identify S₂(f,g) = C(f,g) via the identity theorem. The dependency
is on the OS0 *result*, not on OS0-specific infrastructure.

---

### 6. OS Axioms — `OSforGFF/OS/`

Axiom definitions, individual proofs, and master theorem.

| File | Contents |
|------|----------|
| [Axioms](OSforGFF/OS/Axioms.lean) | Formal Lean definitions of OS0 through OS4 |
| [OS0_Analyticity](OSforGFF/OS/OS0_Analyticity.lean) | Hartogs + Fernique: derivative–integral interchange |
| [OS1_Regularity](OSforGFF/OS/OS1_Regularity.lean) | Plancherel + momentum-space bound: \|Z[f]\| ≤ exp(‖f‖²/2m²) |
| [OS2_Invariance](OSforGFF/OS/OS2_Invariance.lean) | C(x,y) depends only on \|x−y\|, Lebesgue measure invariance |
| [OS3_MixedRepInfra](OSforGFF/OS/OS3_MixedRepInfra.lean) | Schwinger parametrization and Fubini theorems for absolute integrability |
| [OS3_MixedRep](OSforGFF/OS/OS3_MixedRep.lean) | Mixed representation via Schwinger → heat kernel → Laplace transform |
| [OS3_CovarianceRP](OSforGFF/OS/OS3_CovarianceRP.lean) | Covariance reflection positivity: ⟨Θf, Cf⟩ = ∫ (1/ω)\|F_ω\|² ≥ 0 |
| [OS3_ReflectionPositivity](OSforGFF/OS/OS3_ReflectionPositivity.lean) | Schur–Hadamard lifts covariance RP to generating functional |
| [OS4_MGF](OSforGFF/OS/OS4_MGF.lean) | Shared infrastructure: MGF formula, time translation duality |
| [OS4_Clustering](OSforGFF/OS/OS4_Clustering.lean) | Gaussian factorization + convolution decay lemma (domain split at ‖y‖=‖x‖/2) |
| [OS4_Ergodicity](OSforGFF/OS/OS4_Ergodicity.lean) | Polynomial clustering (α=6) → L² convergence |
| [Master](OSforGFF/OS/Master.lean) | Assembles OS0–OS4 into `gaussianFreeField_satisfies_all_OS_axioms` |

---

## Dependencies and Cross-Cutting Concerns

The import graph (`dependency/import_graph.svg`) is mostly layered, with one
cross-cutting dependency:

1. **IsGaussian → OS0_Analyticity**: Gaussianity verification uses the OS0 analyticity result
   to identify S₂(f,g) = C(f,g) via the identity theorem (see Section 5 note)

This prevents a perfectly linear ordering but does not create a circular dependency.

## Building

```bash
lake build
```

Requires Lean 4 and Mathlib (pinned via `lake-manifest.json`).

## Planned Generalizations

1. Other spacetime dimensions, as discussed in [docs/dimension_dependence.md](docs/dimension_dependence.md)
2. Explicit construction of the measure not using Minlos (in progress at [mrdouglasny/GFF4D](https://github.com/mrdouglasny/GFF4D) and [or4nge19/OSforGFF](https://github.com/or4nge19/OSforGFF))

## Authors

Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim

### Coding Assistance

Claude Opus 4.6, Gemini 3 Pro, GPT-5.2 Codex

## License

This project is licensed under the Apache License, Version 2.0. See [LICENSE](LICENSE) for details.

## References

- Glimm, Jaffe: *Quantum Physics* (Springer, 1987), pp. 89–90
- Osterwalder, Schrader: *Axioms for Euclidean Green's functions* I & II (1973, 1975)
- Gel'fand, Vilenkin: *Generalized Functions*, Vol. 4 (Academic Press, 1964)
- Reed, Simon: *Methods of Modern Mathematical Physics*, Vol. II (1975)
