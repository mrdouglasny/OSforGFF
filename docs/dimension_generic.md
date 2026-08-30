# The dimension-generic architecture

How one library proves the Osterwalder–Schrader axioms for the free field in every
dimension `d ≥ 2` at once, and what a new dimension has to supply.

## The idea in one paragraph

Almost nothing in the OS proofs is about four dimensions. The free covariance is a radial
kernel `C(x,y) = C_d(|x−y|)`, and every axiom consumes it through a handful of analytic
facts — integrability, positivity of its Fourier transform, exponential decay, continuity
away from the origin — all of which follow from the **proper-time (Schwinger)
representation**

    C_d(r) = ∫₀^∞ e^{−s m²} · (4πs)^{−d/2} e^{−r²/4s} ds,

one uniform formula for every `d`. What genuinely varies with the dimension is only the
*closed form* of this integral: `(m/4π²r)K₁(mr)` in 4D, the Yukawa potential
`e^{−mr}/4πr` in 3D, `(1/2π)K₀(mr)` in 2D. The library therefore isolates the dimension
behind a two-field typeclass (`Covariance/Propagator.lean`):

```
class GFFPropagator (d : ℕ) (m : ℝ) [Fact (0 < m)] [Fact (2 ≤ d)] where
  Cprofile     : ℝ → ℝ                                      -- the closed form
  schwinger_eq : ∀ r > 0, Cprofile r = properTimeCovariance d m r
```

An instance for a new dimension owes exactly one computation: evaluating the proper-time
integral to its closed form. Everything else — the measure construction, all of OS0–OS4,
non-triviality — is proved once, generically, from `properTimeCovariance`.

## The engine

Facts proved uniformly in `d` and transported to `Cprofile` through `schwinger_eq`:

| Fact | Statement | Consumed by |
|------|-----------|-------------|
| `GFFPropagator.integrable` | `x ↦ C_d(‖x‖)` is L¹ | OS1 local integrability |
| `GFFPropagator.fourier_eq` | `𝓕[C_d(‖·‖)] = 1/((2π)²‖k‖²+m²)` | Parseval bridge, Minlos |
| `GFFPropagator.decayBound` | `C_d(r) ≤ A e^{−(m/2)r}` for `r ≥ 1` | OS4 clustering |
| `properTimeCovariance_continuousOn` | continuity on `(0,∞)` | two-point kernel, OS1 |

On top of these, `Covariance/ParsevalGeneric.lean` derives the momentum-space form of the
covariance pairing (`⟨f, C f̄⟩ = ∫ ‖𝓕f‖²·P`, hence positivity), its bilinear algebra and
reflection/Euclidean invariance, and `Covariance/RealForm.lean` realizes `C(f,f) = ‖Tf‖²`
via the square-root propagator embedding `T = √P ∘ 𝓕` — the continuity and positivity
hypotheses of the Minlos theorem, by which the measure exists on `S′(ℝ^d)`.

## Where the dimension actually shows up

- **Everywhere `d` is a silent parameter.** Types (`SpaceTime d = ℝ^d`, spatial slice
  `ℝ^{d−1}`), Plancherel factors `(2π)^d`, `(2π)^{d−1}`, heat-kernel prefactors
  `(4πs)^{−d/2}`, Schwartz decay exponents. These thread through mechanically.
- **OS3 and the order-`d` domination.** The mixed representation requires exchanging the
  proper-time integral with the spatial momentum integral. A positive-time test function is
  flat to *all* orders at the time boundary, and the dominating function uses vanishing to
  order `d`, giving `s^{d+1/2} e^{−s(‖k‖²+m²)}` (the heat-kernel prefactor `(4πs)^{−d/2}`
  cancels against the `(4πs)^{(d−1)/2}` of the spatial Fourier transform, and each order of
  boundary vanishing contributes one power of `s`). Its `k`-integral is
  `∼ s^{(d+2)/2} e^{−sm²}`, integrable near `s = 0` for every `d` — so the OS3 chain carries
  no upper bound on the dimension (`OS3_MixedRepInfra.integrable_dominate_G`); see
  [`general_dimension.md`](general_dimension.md) for the history of this bound and its removal.
- **The UV statement.** `C(x,y) → ∞` as `x → y` (`OS/NonTrivial.lean`) is generic for every
  `d ≥ 2`: on the proper-time window `[r², (4π)⁻¹]` the integrand dominates a constant
  multiple of `1/s`, so the integral grows at least like `log(1/r²)` — the sharp rate at
  `d = 2`; for `d ≥ 3` the true rate `r^{2−d}` is polynomial. Non-degeneracy of the measure
  (injectivity of `T`, positive variance of every pairing) is likewise generic.

## The instance layer

Every instance owes exactly one closed-form evaluation of the proper-time integral, and all four
go through **one** identity. `General/BesselK.lean` defines the modified Bessel function of
arbitrary order `K_ν(z) = ∫₀^∞ e^{−z cosh t} cosh(νt) dt` and proves the master Schwinger identity

    ∫₀^∞ t^{ν−1} e^{−m²t − r²/(4t)} dt = 2 (r/2m)^ν · K_ν(mr)

(change of variables `t = (r/2m)eᵘ` + a ν-generic symmetrization). At dimension `d` the
proper-time integrand carries `t^{−d/2}`, i.e. `ν = 1 − d/2`, so each instance is one order of the
same identity, using `K_{−ν} = K_ν`:

- `Instances/Dim2.lean` (`ν = 0`): the Bessel kernel `(1/2π)K₀(mr)`.
- `Instances/Dim3.lean` (`ν = −1/2`): the Yukawa kernel `e^{−mr}/(4πr)`, using the elementary
  `K_{1/2}(z) = √(π/2z) e^{−z}` (`besselK_half`, substitution `u = sinh(t/2)` → Gaussian).
- `Instances/Dim4.lean` (`ν = −1`): the Bessel kernel `(m/4π²r)K₁(mr)` (the original
  4D development's named kernel `freeCovariance4` survives off-graph in
  `Legacy/Dim4Bessel.lean`).
- `Instances/Dim5.lean` (`ν = −3/2`): the `K_{3/2}` kernel `(1+mr)e^{−mr}/(8π²r³)`, using
  `K_{3/2}(z) = √(π/2z) e^{−z}(1+1/z)` (`besselK_three_half`, Gaussian zeroth and second moments).

`Covariance/Propagator.ofProperTime` additionally discharges the class in every dimension with the
proper-time integral itself, needing no closed form. The master theorem

    gaussianFreeField_satisfies_all_OS_axioms_generic :
      ∀ {d} [Fact (2 ≤ d)] (m) [Fact (0 < m)] [GFFPropagator d m],
        SatisfiesAllOS (gaussianFreeField_free d m)

specializes to the concrete headlines `SatisfiesAllOS (μ_GFF 4 m)` (d = 4), `μ_GFF 3 m`,
`μ_GFF 2 m`, `μ_GFF 5 m`, and to the all-dimensions corollary `gaussianFreeField_satisfies_all_OS_axioms_of_dim`
for every `d ≥ 2` — each with the same axiom footprint (`propext`, `Classical.choice`,
`Quot.sound` — nothing else). `Guardrails.lean` freezes all six of these facts into the build.

The original four-dimensional Bessel/momentum development (the regulated-covariance program and the
K₁ analytic lemmas), superseded by the machinery above, is preserved off the build graph in
`OSforGFF/Legacy/` with per-file supersession maps.
