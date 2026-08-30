# Foundational Definitions and Axioms

This document catalogs all core definitions, structures, and axioms in the OSforGFF project
for human review. Helper lemmas and theorems are omitted; only the objects on which the
construction is built are listed.

---

## Axioms (0 total)

There are **no `axiom` declarations reachable from the master theorem**. `#print axioms` on every
headline shows exactly Lean's three foundational axioms — `propext`, `Classical.choice`,
`Quot.sound` — and nothing else; this is build-frozen in `OSforGFF/Guardrails.lean`.

The nuclear-space, Minlos, and Bochner machinery is supplied by the external, axiom-free libraries
`BochnerMinlos` / `GaussianField` (consumed as `Minlos.*` / `Bochner.*`), not by axioms in this
project. (An earlier version of this document listed three custom axioms — `schwartz_nuclear`,
`minlos_theorem`, `differentiable_analyticAt_finDim` — that expected a floating dependency state;
at the pinned dependency revisions none are reachable: `minlos_theorem` is a proven theorem, the
`schwartz_*` axioms live in an off-path `Test/` tree, and `differentiable_analyticAt_finDim` no
longer exists.)

---

## Spacetime and Test Functions

### Core types (`Spacetime/Basic.lean`)

The library is **dimension-generic**: types are parameterized by `d : ℕ`; the concrete instances
fix `d = 2, 3, 4, 5`.

| Name | Definition |
|------|------------|
| `SpaceTime d` | `EuclideanSpace ℝ (Fin d)` — Euclidean ℝ^d |
| `SchwartzTestFunction d` | `SchwartzMap (SpaceTime d) ℝ` — real Schwartz functions S(ℝ^d, ℝ) |
| `SchwartzTestFunctionℂ d` | `SchwartzMap (SpaceTime d) ℂ` — complex Schwartz functions S(ℝ^d, ℂ) |
| `FieldConfiguration d` | `WeakDual ℝ (SchwartzTestFunction d)` — tempered distributions S'(ℝ^d) |
| `SpatialCoords d` | `EuclideanSpace ℝ (Fin (d - 1))` — spatial ℝ^{d−1} |

### Pairings and generating functionals (`Spacetime/Basic.lean`)

| Name | Definition |
|------|------------|
| `distributionPairing` | `⟨ω, f⟩ : ℝ` — evaluation of distribution ω on test function f |
| `GJGeneratingFunctional` | `Z[J] = ∫ exp(i⟨ω,J⟩) dμ(ω)` — Glimm–Jaffe generating functional |
| `distributionPairingℂ_real` | `⟨ω, f⟩ₗ = ⟨ω, fᵣₑ⟩ + i⟨ω, fᵢₘ⟩` — complex pairing |
| `GJGeneratingFunctionalℂ` | Complex generating functional for complex test functions |
| `GJMean` | `𝔼_μ[⟨ω, φ⟩]` — mean field |
| `E` | `E(m, k) = √(‖k‖² + m²)` — relativistic dispersion relation |

### Complex test functions (`Spacetime/ComplexTestFunction.lean`)

| Name | Definition |
|------|------------|
| `toComplex` | Embedding ℝ-Schwartz → ℂ-Schwartz |
| `conjSchwartz` | Pointwise complex conjugation on Schwartz functions |

### Spacetime decomposition (`Spacetime/Decomposition.lean`)

| Name | Definition |
|------|------------|
| `spacetimeDecomp` | Measurable equivalence SpaceTime ≃ᵐ ℝ × SpatialCoords |

---

## Discrete Symmetries (`Spacetime/DiscreteSymmetry.lean`)

| Name | Definition |
|------|------------|
| `QFT.timeReflection` | Θ: (t, x̄) ↦ (−t, x̄) on spacetime |
| `QFT.timeReflectionLE` | Θ as linear isometry equivalence (self-inverse) |
| `QFT.compTimeReflection` | Pullback f ↦ f∘Θ on complex test functions (CLM) |
| `QFT.compTimeReflectionReal` | Pullback f ↦ f∘Θ on real test functions (CLM) |

---

## Euclidean Group (`Spacetime/Euclidean.lean`)

| Name | Definition |
|------|------------|
| `QFT.O` | Orthogonal group O(d) = linear isometries of ℝᵈ |
| `QFT.E` | `structure` — Euclidean motion (R ∈ O(d), t ∈ ℝᵈ), i.e. E(d) = ℝᵈ ⋊ O(d) |
| `QFT.act` | Group action x ↦ R·x + t |
| `QFT.euclidean_action` | Pullback (g·f)(x) = f(g⁻¹·x) on complex test functions |

---

## Time Translation (`Spacetime/TimeTranslation.lean`)

| Name | Definition |
|------|------------|
| `timeShift` | (t, x̄) ↦ (t+s, x̄) on spacetime |
| `timeTranslationSchwartzCLM` | T_s as CLM on real Schwartz functions |
| `timeTranslationDistribution` | T_s on distributions by duality: ⟨T_s ω, f⟩ = ⟨ω, T_{−s} f⟩ |

---

## Positive-Time Test Functions and OS Star (`Spacetime/PositiveTimeTestFunction.lean`)

| Name | Definition |
|------|------------|
| `HasPositiveTime` | Predicate: x₀ > 0 |
| `PositiveTimeTestFunctions.submodule` | Submodule of f ∈ S(ℝᵈ) with tsupport ⊆ {x₀ > 0} |
| `PositiveTimeTestFunction` | Type alias for positive-time test functions |
| `PositiveTimeTestFunctionsℂ.submodule` | ℂ-submodule of f ∈ S(ℝᵈ, ℂ) with tsupport ⊆ {x₀ > 0} |
| `PositiveTimeTestFunctionℂ` | Type alias for complex positive-time test functions |
| `starTestFunction` | OS star: (star f)(x) = conj(f(Θ x)) — time reflection + conjugation |

---

## Free Covariance

The covariance seam is the dimension-generic `GFFPropagator d m` typeclass: everything downstream
consumes only the class and the lemmas derived once from its two fields.

### The propagator typeclass and generic kernels (`Covariance/Propagator.lean`)

| Name | Definition |
|------|------------|
| `heatKernelProfile d t r` | (4πt)^{−d/2} exp(−r²/(4t)) — heat-kernel radial profile |
| `properTimeCovariance d m r` | ∫₀^∞ e^{−tm²} H_d(t,r) dt — proper-time (Schwinger) covariance profile (`C_S`) |
| `freePropagatorMom d m k` | 1/((2π)²‖k‖² + m²) — momentum-space propagator (Mathlib Fourier convention) |
| `GFFPropagator d m` | `class` — fields `Cprofile` (per-d closed-form radial kernel) + `schwinger_eq` (it equals `properTimeCovariance` for r>0) |
| `GFFPropagator.integrable / .fourier_eq / .decayBound` | derived once for all d: L¹, forward FT = `freePropagatorMom`, pointwise exponential decay |
| `GFFPropagator.ofProperTime d m` | canonical instance (Cprofile := `properTimeCovariance`); discharges the class for every 2 ≤ d |
| `freeCovariance d m x y` | **Principal two-point function** C(x,y) = `Cprofile ‖x − y‖` |

### Modified Bessel function and the master Schwinger identity (`General/BesselK.lean`)

| Name | Definition |
|------|------------|
| `besselK ν z` | ∫₀^∞ e^{−z cosh t} cosh(νt) dt — modified Bessel function of order ν |
| `schwingerIntegral_eq_besselK` | ∫₀^∞ t^{ν−1} e^{−m²t−r²/4t} dt = 2(r/2m)^ν K_ν(mr) — master identity |

### Real form and embedding (`Covariance/RealForm.lean`)

| Name | Definition |
|------|------------|
| `freeCovarianceFormR` | ∫∫ f(x) C(x,y) g(y) dx dy — real covariance bilinear form |
| `sqrtPropagatorMap` | T: f ↦ FT(f)·(‖k‖²+m²)^{−1/2} — embedding into L² |
| `embeddingMap` / `embeddingMapCLM` | ℝ-linear (resp. continuous) embedding T: SchwartzTestFunction → L² |
| `freePropagatorMomSqrt` | 1/√((2π)²‖k‖² + m²) — square-root propagator weight |

### Parseval and the complex bilinear form (`Covariance/ParsevalGeneric.lean`)

| Name | Definition |
|------|------------|
| `freeCovarianceℂ_bilinear` | ∫∫ f̄(x) C(x,y) g(y) dx dy — complex covariance bilinear form |
| `freeCovarianceKernel d m` | centered kernel `freeCovariance d m 0 ·` (continuity, integrability, exponential decay) |

The four-dimensional Bessel kernel `freeCovarianceBessel` / `freeCovariance4` = (m/4π²r)K₁(mr)
lives off-graph in `Legacy/Dim4Bessel.lean`. The original momentum-space program (`freePropagatorMomentum`,
`heatKernelPositionSpace`, `covarianceSchwingerRep`, `freeCovariance_regulated`, the momentum-weight
operators) is preserved off the build graph in `OSforGFF/Legacy/`.

---

## Schwinger Functions (`Schwinger/`)

### n-point functions (`Schwinger/Defs.lean`)

| Name | Definition |
|------|------------|
| `SchwingerFunction` | S_n(f₁,…,fₙ) = ∫ ∏ᵢ ⟨ω, fᵢ⟩ dμ(ω) — n-point correlation |
| `SchwingerFunction₁` | 1-point function (mean field) |
| `SchwingerFunction₂` | 2-point function (covariance) |
| `CovarianceBilinear` | Property: S₂ is ℂ-bilinear |

### Pointwise 2-point function (`Schwinger/TwoPoint.lean`)

| Name | Definition |
|------|------------|
| `SmearedTwoPointFunction` | Bump-regularized 2-point function |
| `SchwingerTwoPointFunction` | Pointwise 2-point function as limit of smeared correlations |

---

## Measure Construction (`Measure/`)

### Nuclear space (`Measure/NuclearSpace.lean`)

The nuclear-space notions themselves (`NuclearSpace`, nuclear maps) come from the external
bochner library; this file supplies the bridge facts the construction needs:

| Name | Definition |
|------|------------|
| `nuclearSpace_to_isNuclear` | the library's `NuclearSpace` instance yields nuclearity in bochner's sense |
| `schwartz_isHilbertNuclear` | Schwartz space is Hilbert-nuclear |
| `schwartz_separableSpace` | Schwartz space is separable |

### Minlos theorem (`Measure/Minlos.lean`)

| Name | Definition |
|------|------------|
| `gaussian_characteristic_functional` | Φ(f) = exp(−½⟨f, Cf⟩) |

### Covariance form structure (`Measure/MinlosAnalytic.lean`)

| Name | Definition |
|------|------------|
| `CovarianceForm` | `structure` — symmetric positive-semidefinite bilinear form Q with positive-definite Gaussian CF |

### GFF construction (`Measure/Construct.lean`)

| Name | Definition |
|------|------------|
| `isCenteredGJ` | 𝔼[⟨ω, f⟩] = 0 for all f |
| `isGaussianGJ` | Z[J] = exp(−½ S₂(J,J)) |
| `gaussianFreeField_free` | **The GFF measure** μ_GFF d m on S'(ℝ^d), constructed via Minlos |
| `freeCovarianceForm` | The free covariance packaged as a `CovarianceForm` |

---

## OS Axiom Definitions (`OS/Axioms.lean`)

| Name | Definition |
|------|------------|
| `OS0_Analyticity` | Z[∑ zᵢJᵢ] is analytic on ℂⁿ |
| `OS1_Regularity` | ‖Z[f]‖ ≤ exp(c·‖f‖_Lp) |
| `OS2_EuclideanInvariance` | Z[f] = Z[g·f] for all g ∈ E(d) |
| `OS3_ReflectionPositivity` | Re(∑ c̄ᵢcⱼ Z_ℂ[fᵢ − star fⱼ]) ≥ 0 for complex positive-time fᵢ, star f = conj∘f∘Θ |
| `OS4_Clustering` | Z[f + τ_a g] → Z[f]·Z[g] as ‖a‖ → ∞ |
| `OS4_Ergodicity` | (1/T)∫₀ᵀ A(T_s ω) ds →_{L²} 𝔼[A] |
| `SatisfiesAllOS` | `structure` — bundles OS0–OS4 |

### Master theorem (`OS/Master.lean`)

The dimension-generic master theorem, its all-dimensions corollary, and the four concrete instances:

```
theorem gaussianFreeField_satisfies_all_OS_axioms_generic
    {d : ℕ} [Fact (2 ≤ d)] (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] :
    SatisfiesAllOS (gaussianFreeField_free (d := d) m)

theorem gaussianFreeField_satisfies_all_OS_axioms_of_dim (d : ℕ) [Fact (2 ≤ d)]
    (m : ℝ) [Fact (0 < m)] : … (via GFFPropagator.ofProperTime)

theorem gaussianFreeField_satisfies_all_OS_axioms_dim4      (m) [Fact (0 < m)] : SatisfiesAllOS (μ_GFF 4 m)  -- d = 4
theorem gaussianFreeField_satisfies_all_OS_axioms_dim3 (m) [Fact (0 < m)] : SatisfiesAllOS (μ_GFF 3 m)  -- d = 3
theorem gaussianFreeField_satisfies_all_OS_axioms_dim2 (m) [Fact (0 < m)] : SatisfiesAllOS (μ_GFF 2 m)  -- d = 2
theorem gaussianFreeField_satisfies_all_OS_axioms_dim5 (m) [Fact (0 < m)] : SatisfiesAllOS (μ_GFF 5 m)  -- d = 5
```

---

## General Mathematics (`General/`)

| File | Name | Definition |
|------|------------|
| BesselK.lean | `besselK ν z` | Modified Bessel function of order ν + the master Schwinger identity |
| BesselFunction.lean | `besselK1` | Modified Bessel function K₁(z) (def only; analytic lemmas in `Legacy/`) |
| BesselK0.lean | `besselK0` | Modified Bessel function K₀(z) (def only) |
| PositiveDefinite.lean | `IsPositiveDefinite` | ∑ c̄ᵢcⱼ φ(xᵢ−xⱼ) ≥ 0 |
| GaussianRBF.lean | `IsPositiveDefiniteKernel` | ∑ c̄ᵢcⱼ K(xᵢ,xⱼ) ≥ 0 |
| FunctionalAnalysis.lean | `schwartzToL2` | Continuous embedding S(ℝ^d) ↪ L²(ℝ^d) |
| FunctionalAnalysis.lean | `SchwartzMap.translate` | f.translate(a)(x) = f(x−a) |
