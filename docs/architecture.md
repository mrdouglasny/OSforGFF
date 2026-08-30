# Architecture

How the 52 on-graph files fit together (plus the off-graph `OS/NonTrivial.lean` and 6
off-graph `Legacy/` files — see below).
For proof details see the paper (§4); for the dimension-generic design (the `GFFPropagator`
typeclass and where the dimension enters each axiom) see `dimension_generic.md`.

## Dependency layers

```
General ──→ Spacetime ──→ Covariance ──→ Measure ──→ OS
  (13)        (9)  │        (3)     ↑      (6)      (12)
                   └────→ Schwinger ┘
                            (3)
                               ↑
                          Instances (4): the per-dimension closed forms
                          (d = 2, 3, 4, 5) on top of Covariance/Propagator,
                          consumed by the per-dimension headline theorems
                          and OS/NonTrivial's UV statement
```

All proof files are parameterized by the spacetime dimension `d` and consume the
covariance only through the `GFFPropagator d m` typeclass
(`Covariance/Propagator.lean`). The genuine per-`d` input is a single closed-form kernel
identified with the generic proper-time integral; the modified Bessel function of arbitrary
order and the master Schwinger identity live in `General/BesselK.lean`.

The `Legacy/` directory (off the root import graph, not built by `lake build`) preserves
superseded proven mathematics: the original four-dimensional Bessel/momentum development
(`Dim4Bessel`, `BesselK1Analytics` — the regulated-covariance program and the K₁ analytic
lemmas) and the four `Unused*.lean` files holding declarations retired by the library-wide
dead-code sweeps. Each Legacy file carries a supersession map and is verified in isolation
with `lake env lean`. `OS/NonTrivial.lean` (the non-degeneracy results) is also off the
import graph, but is live mathematics: `scripts/check-guardrails.sh` compiles it.

Imports flow left to right with two cross-cutting edges:

- `Measure/IsGaussian` imports `OS/OS0_Analyticity` to use the proved
  analyticity for the identity-theorem argument S₂ = C.
- `Schwinger/GaussianMoments` imports `Measure/Construct`: the moment bounds are
  stated for the constructed free-field measure.

Neither is circular: OS0 depends on `Measure/Construct` (the measure must
exist before we can prove analyticity), and `IsGaussian` feeds back into
the later OS proofs (OS1–OS4 need S₂ = C).

## No assumed axioms

Everything is proved: `#print axioms` for the master theorem — the dimension-generic form, the
all-dimensions corollary (`d ≥ 2`), and each concrete instance (`d = 2, 3, 4, 5`) — shows
exactly Lean's three foundational axioms: `propext`, `Classical.choice`, `Quot.sound`.
`Guardrails.lean` freezes this footprint and the exact statement of all six headline theorems into
the build, so any regression fails `lake build`.

## OS3: the longest proof chain

OS3 (reflection positivity) is the most technically involved axiom, spanning
4 files and ~6600 lines. The logical chain:

1. **MixedRepInfra** (~3600 lines): Schwinger parametrization makes all
   integrals absolutely convergent (the naive momentum-space approach fails
   because 1/√(k²+m²) is not L¹ in the spatial momentum space). Proves ~36
   Fubini exchange and integrability lemmas, with the dominating function built
   from order-`d` boundary vanishing (see `dimension_generic.md`).

2. **MixedRep** (~1500 lines): Chains the exchanges to reach the mixed
   representation ⟨Θf, Cf⟩ = ∫ (1/ω)|F_ω(k̄)|² dk̄, going through
   heat kernel → Fourier → Gaussian k₀ integral → Laplace transform.

3. **CovarianceRP** (~460 lines): Defines the star operation
   `(star f)(x) = conj(f(Θx))` on complex test functions and proves
   `Re⟨star f, Cf⟩ ≥ 0` for positive-time f.  The factorization
   |−x₀−y₀| = x₀+y₀ for positive-time support makes the integrand a
   perfect square.  Bridges to real test functions via
   `star (toComplex f) = compTimeReflection (toComplex f)`.

4. **ReflectionPositivity** (~1000 lines): Two independent proofs.

   **Real version**: Schur–Hadamard lift for real coefficients:
   R_ij = ⟨Θfᵢ, Cfⱼ⟩ is PSD → exp(R) is PSD (Hadamard series) →
   ∑ cᵢcⱼ Z[fᵢ−Θfⱼ] ≥ 0.

   **Complex version**: Full Osterwalder–Schrader formulation
   with complex test functions and complex coefficients.  The matrix entry
   factorizes as Z_ℂ[fᵢ − star fⱼ] = Aᵢ · conj(Aⱼ) · exp(Rᵢⱼ) where
   Rᵢⱼ = C(fᵢ, star fⱼ) is Hermitian PSD.  Key ingredients:
   - `star` antilinearity: star(∑ c̄ⱼfⱼ) = ∑ cⱼ star(fⱼ)
   - Hermiticity: R_{ji} = conj(R_{ij}) via C(star f, star g) = conj(C(f,g))
   - Complex Schur product theorem (Kronecker ⊗ diagonal submatrix)
   - Complex entrywise exponential PSD via Hadamard power series limit

## OS4: two-stage argument

1. **Clustering** (OS4_Clustering): Gaussian factorization reduces the
   clustering bound to estimating S₂(f, T_{−s}g), which decays as
   (1+|s|)^{−α} by Schwartz convolution decay with the exponentially decaying
   kernel |C(z)| ≤ A e^{−(m/2)|z|} for |z| ≥ 1 (the mass gap, from the
   proper-time representation).

2. **Ergodicity** (OS4_Ergodicity): Polynomial clustering with α = 6 feeds
   into an L² time-average bound: ‖(1/t)∫₀ᵗ A(T_s φ) ds − 𝔼[A]‖² ≤ C/t → 0.

## Key design choices

- **Schwartz over D**: We use S(ℝ^d) rather than D(ℝ^d) because Mathlib has
  SchwartzSpace but not test function spaces with compact support. Since
  D ⊂ S and S' ⊂ D', our axioms imply the Glimm–Jaffe versions.

- **Schwinger parametrization for OS3**: The direct momentum-space Fubini
  fails (conditional convergence). The Schwinger representation
  C = ∫₀^∞ e^{−sm²} H_s ds introduces the heat kernel as a regularizer,
  making all integrals absolutely convergent.

- **Proper-time kernel for Parseval**: The Parseval identity
  ⟨f, C f̄⟩ = ∫ ‖𝓕f‖²/((2π)²‖k‖²+m²) is derived against the proper-time
  covariance (which is L¹ with an explicit Fourier transform), avoiding
  convergence issues with the bare propagator — no regulator needed
  (`Covariance/ParsevalGeneric.lean`).

- **Closed form behind a typeclass**: Rather than Fourier-transforming the
  propagator directly (conditionally convergent), C(x,y) is the radial profile
  `Cprofile |x−y|` of a `GFFPropagator d m` instance, identified with the
  Schwinger integral by the instance's one obligation `schwinger_eq`. The
  instances supply the closed forms — (1/2π)K₀(mr) at d=2, e^{−mr}/(4πr) at d=3,
  (m/4π²r)K₁(mr) at d=4, (1+mr)e^{−mr}/(8π²r³) at d=5 — each the order ν=1−d/2
  case of the master identity in `General/BesselK.lean`. `ofProperTime`
  (`Covariance/Propagator.lean`) additionally discharges the class in every
  dimension `d ≥ 2` with no closed form, giving the all-dimensions corollary.
