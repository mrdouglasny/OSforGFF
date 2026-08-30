# `BesselFunction.lean` — Informal Summary

> **Source**: [`OSforGFF/General/BesselFunction.lean`](../../../OSforGFF/General/BesselFunction.lean)
> **Generated**: 2026-07-05 (regenerated from current source)

## Overview

This file defines the modified Bessel function of the second kind of order one, `besselK1`,
through its $\cosh$ integral representation. This $K_1$ profile is the shape of the free
covariance in four dimensions: the radial profile there is
$\bigl(m/(4\pi^2 r)\bigr)\, K_1(m r)$ (`Instances/Dim4.lean`). The proper-time (Schwinger)
evaluation
$$\int_0^\infty \frac{1}{t^2}\, e^{-m^2 t - r^2/(4t)}\, dt = \frac{4m}{r}\, K_1(m r)$$
is the order-one case of the master identity `schwingerIntegral_eq_besselK`
(`General/BesselK`). The analytic lemmas about $K_1$ (positivity, continuity, the asymptotic
and near-origin bounds, radial integrability) that supported the original four-dimensional
analysis are preserved off the build graph in `OSforGFF/Legacy/BesselK1Analytics.lean`; this
file itself contains only the definition.

## Status

**Main result**: Defines `besselK1` (0 sorries).

**Length**: 29 lines, 1 definition + 0 theorem(s)/lemma(s)

---

### [`besselK1`](../../../OSforGFF/General/BesselFunction.lean#L28) — Definition

**Lean signature**
```lean
noncomputable def besselK1 (z : ℝ) : ℝ :=
  ∫ t : ℝ in Ici 0, exp (-z * cosh t) * cosh t
```

**Informal**: The modified Bessel function $K_1(z)$ of the second kind of order one, defined
by its $\cosh$ integral representation
$$K_1(z) = \int_0^\infty e^{-z \cosh t}\, \cosh t \, dt.$$
Well-defined and positive for $z > 0$.

---

*This file has **1** definitions and **0** theorems/lemmas (0 with sorry).*
